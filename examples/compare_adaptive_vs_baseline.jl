"""
Quick one-off comparison: adaptive mutation weights vs baseline.

Runs both with the same global seed and prints best loss per complexity side by side.

Run with:
    julia --project=. examples/compare_adaptive_vs_baseline.jl
"""

include("plugin_adaptive_weights.jl")  # defines AdaptiveOptions, AdaptiveWeights, AdaptiveState, etc.

using Random
using Printf

const NITERATIONS = 50
const SEED = 42

X = rand(MersenneTwister(SEED), Float32, 3, 100)
y = @. 2f0 * X[1, :] * sin(X[2, :]) + X[3, :]^2

base = Options(
    binary_operators=[+, *, -, /],
    unary_operators=[sin, exp],
    populations=4,
    verbosity=0,
    progress=false,
)

# --- Baseline ---
println("=== Baseline (fixed weights) ===")
Random.seed!(SEED)
hof_base = equation_search(X, y; options=base, niterations=NITERATIONS, parallelism=:serial)

# --- Adaptive ---
println("\n=== Adaptive weights ===")
channel = Channel{Dict{Symbol,Tuple{Int,Float64}}}(Inf)
opts = AdaptiveOptions(base, AdaptiveWeights(), channel, 0.3, 0.01, typemax(Int))  # suppress intermediate prints
Random.seed!(SEED)
hof_adaptive = equation_search(X, y; options=opts, niterations=NITERATIONS, parallelism=:serial)

# --- Side-by-side comparison ---
println("\n=== Best loss per complexity ===")
@printf "  %10s  %14s  %14s\n" "complexity" "baseline" "adaptive"
println("  ", "-"^42)

for c in eachindex(hof_base.members, hof_base.exists)
    b_exists = hof_base.exists[c]
    a_exists = hof_adaptive.exists[c]
    (b_exists || a_exists) || continue
    b_str = b_exists ? @sprintf("%14.6e", hof_base.members[c].loss)     : "             —"
    a_str = a_exists ? @sprintf("%14.6e", hof_adaptive.members[c].loss) : "             —"
    println("  ", @sprintf("%10d  %s  %s", c, b_str, a_str))
end
