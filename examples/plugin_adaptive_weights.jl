"""
Adaptive Mutation Weights via the Plugin Interface (Layer 1 + 2)

This example tracks per-mutation success rates during the search and adapts
mutation weights using an exponential moving average — the discrete-type analogue
of CMA-ES. Mutations that are frequently accepted get higher weights; rarely-accepted
mutations are down-weighted toward a configurable floor.

It demonstrates:
  - @extend_mutation_weights — extending the default mutation weight type
  - AbstractPluginState with per-worker attempt/success counters
  - on_mutation_evaluated! — worker hook, fires after each accept/reject decision
  - on_population_evaluated! — push worker stats to head via Channel
  - on_generation_complete! — aggregate stats and update shared weights (EMA + normalize)
  - Base.getproperty trick: redirecting :mutation_weights so workers see the live weights

Run with:
    julia --project=. examples/plugin_adaptive_weights.jl
"""

using SymbolicRegression
import SymbolicRegression:
    AbstractOptions, AbstractPluginState,
    init_plugin_state, on_mutation_evaluated!, on_population_evaluated!, on_generation_complete!
using Printf

# ============================================================
# Step 1: Extended mutation weights type (no extra fields — same
#         fields as MutationWeights, but a distinct type so
#         getproperty can redirect :mutation_weights to it)
# ============================================================

@extend_mutation_weights AdaptiveWeights begin end

# ============================================================
# Step 2: Custom options type
# ============================================================
#
# Key design: getproperty redirects :mutation_weights → :adaptive_weights.
# Workers call `copy(options.mutation_weights)` at the start of each
# next_generation call, so they always read the current weights.
# The head node modifies adaptive_weights in-place each generation.

struct AdaptiveOptions{O<:AbstractOptions} <: AbstractOptions
    base::O
    adaptive_weights::AdaptiveWeights        # mutable, shared by reference
    stats_channel::Channel{Dict{Symbol,Vector{Int}}}  # mutation → [attempts, successes]
    smoothing::Float64                        # EMA α — adaptation speed (e.g. 0.3)
    min_weight::Float64                       # floor to preserve exploration (e.g. 0.01)
    log_every::Int                            # print weights every N generations
end

Base.getproperty(o::AdaptiveOptions, k::Symbol) =
    k === :mutation_weights ? getfield(o, :adaptive_weights) :
    k in (:adaptive_weights, :stats_channel, :smoothing, :min_weight, :log_every) ? getfield(o, k) :
    getproperty(getfield(o, :base), k)

# ============================================================
# Step 3: Plugin state (one instance per worker + one on head)
# ============================================================

mutable struct AdaptiveState <: AbstractPluginState
    attempts::Dict{Symbol,Int}
    successes::Dict{Symbol,Int}
    stats_channel::Channel{Dict{Symbol,Vector{Int}}}
    generation::Int   # head-node generation counter (workers ignore this)
end

SymbolicRegression.init_plugin_state(opts::AdaptiveOptions, datasets) =
    AdaptiveState(Dict(), Dict(), opts.stats_channel, 0)

# ============================================================
# Step 4: Worker hook — record accept/reject per mutation type
# ============================================================
#
# Skip :do_nothing — it always "succeeds" trivially (return_immediately=true)
# and would dominate the statistics, obscuring meaningful signal.

function SymbolicRegression.on_mutation_evaluated!(
    state::AdaptiveState, mutation_type::Symbol, accepted::Bool, dataset, opts::AdaptiveOptions
)
    mutation_type === :do_nothing && return
    state.attempts[mutation_type] = get(state.attempts, mutation_type, 0) + 1
    if accepted
        state.successes[mutation_type] = get(state.successes, mutation_type, 0) + 1
    end
    return nothing
end

# ============================================================
# Step 5: After each population cycle — push stats and reset
# ============================================================

function SymbolicRegression.on_population_evaluated!(
    state::AdaptiveState, pop, dataset, hof, opts::AdaptiveOptions
)
    isempty(state.attempts) && return
    batch = Dict(
        k => [state.attempts[k], get(state.successes, k, 0)]
        for k in keys(state.attempts)
    )
    put!(opts.stats_channel, batch)
    empty!(state.attempts)
    empty!(state.successes)
    return nothing
end

# ============================================================
# Step 6: Head-node hook — aggregate and update weights (EMA)
# ============================================================
#
# EMA update: w ← (1-α)·w + α·rate
# Then floor at min_weight and normalize so total weight mass
# stays constant (preserves the relative scale of sampling).

function SymbolicRegression.on_generation_complete!(
    state::AdaptiveState, search_state, datasets, opts::AdaptiveOptions, ropt
)
    totals_attempts  = Dict{Symbol,Int}()
    totals_successes = Dict{Symbol,Int}()
    while isready(opts.stats_channel)
        for (m, (a, s)) in take!(opts.stats_channel)
            totals_attempts[m]  = get(totals_attempts,  m, 0) + a
            totals_successes[m] = get(totals_successes, m, 0) + s
        end
    end
    isempty(totals_attempts) && return

    w = opts.adaptive_weights
    α = opts.smoothing
    for m in fieldnames(AdaptiveWeights)
        a = get(totals_attempts, m, 0)
        a == 0 && continue
        rate = totals_successes[m] / a
        old  = getfield(w, m)
        setfield!(w, m, max(opts.min_weight, (1 - α) * old + α * rate))
    end

    # Normalize: keep total weight mass equal to the default total
    total         = sum(getfield(w, m) for m in fieldnames(AdaptiveWeights))
    initial_total = sum(getfield(AdaptiveWeights(), m) for m in fieldnames(AdaptiveWeights))
    scale = initial_total / total
    for m in fieldnames(AdaptiveWeights)
        setfield!(w, m, getfield(w, m) * scale)
    end

    state.generation += 1
    if state.generation % opts.log_every == 0
        _print_weights(opts.adaptive_weights, state.generation, totals_attempts, totals_successes)
    end
    return nothing
end

function _print_weights(
    w::AdaptiveWeights, gen::Int,
    attempts::Dict{Symbol,Int}, successes::Dict{Symbol,Int}
)
    defaults = AdaptiveWeights()
    println("\n--- Generation $gen: adaptive weights (success rate → weight) ---")
    @printf "  %-25s  %6s  %6s  %8s\n" "mutation" "rate%" "evals" "weight"
    for m in fieldnames(AdaptiveWeights)
        getfield(defaults, m) == 0.0 && continue  # skip disabled-by-default
        a = get(attempts, m, 0)
        s = get(successes, m, 0)
        wt = getfield(w, m)
        rate_str = a > 0 ? @sprintf("%5.1f%%", 100 * s / a) : "     —"
        @printf "  %-25s  %s  %6d  %8.4f\n" m rate_str a wt
    end
end

# ============================================================
# Step 7: Run equation_search with adaptive options
# ============================================================

base = Options(
    binary_operators=[+, *, -, /],
    unary_operators=[sin, exp],
    populations=4,
    verbosity=0,
    progress=false,
)

channel = Channel{Dict{Symbol,Vector{Int}}}(Inf)
opts = AdaptiveOptions(base, AdaptiveWeights(), channel, 0.3, 0.01, 5)

# Target: y = 2x₁·sin(x₂) + x₃²
X = rand(Float32, 3, 100)
y = @. 2f0 * X[1, :] * sin(X[2, :]) + X[3, :]^2

println("Running equation_search with adaptive mutation weights …")
equation_search(X, y; options=opts, niterations=30, parallelism=:serial)

# Print final weights vs defaults for comparison
println("\n=== Final adaptive weights ===")
println("  (weights > default → more successful; near min_weight → rarely accepted)\n")
defaults = AdaptiveWeights()
@printf "  %-25s %8s  %8s\n" "mutation" "default" "adapted"
println("  ", "-"^44)
for m in fieldnames(AdaptiveWeights)
    d = getfield(defaults, m)
    a = getfield(opts.adaptive_weights, m)
    d == 0.0 && continue  # skip disabled-by-default mutations
    marker = abs(a - d) > 0.005 ? (a > d ? " ▲" : " ▼") : ""
    @printf "  %-25s %8.4f  %8.4f%s\n" m d a marker
end
