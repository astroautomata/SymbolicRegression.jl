"""
Operator Frequency Reporter via the Plugin Interface (Layer 2)

This example counts how often each operator appears across all evaluated
populations and prints a frequency table at the end of the search.

It demonstrates:
  - AbstractPluginState holding mutable worker-local data
  - on_population_evaluated! — worker hook, fires after each s_r_cycle
  - on_search_end! — head-node hook, fires once at the end
  - The Channel pattern: workers push Dict counts, head drains and aggregates

The plugin is purely observational. It does not change the search at all.

Run with:
    julia --project=. examples/plugin_operator_stats.jl
"""

using SymbolicRegression
import SymbolicRegression:
    AbstractOptions, AbstractPluginState,
    init_plugin_state, on_population_evaluated!, on_search_end!
using DynamicExpressions: get_tree

# ============================================================
# Step 1: Custom AbstractOptions subtype
# ============================================================
#
# Stores a shared Channel so workers can push operator counts to the
# head node. The channel is unbounded (capacity=Inf), so put! never
# blocks even if the head hasn't drained it yet.

struct OpStatsOptions{O<:AbstractOptions} <: AbstractOptions
    base::O
    op_channel::Channel{Dict{String,Int}}
end

Base.getproperty(o::OpStatsOptions, k::Symbol) =
    k === :op_channel ? getfield(o, :op_channel) :
    getproperty(getfield(o, :base), k)

# ============================================================
# Step 2: Plugin state (one instance per worker + one on head)
# ============================================================
#
# Each worker holds a reference to the shared channel so
# on_population_evaluated! can push results back to the head node.

mutable struct OpStatsState <: AbstractPluginState
    op_channel::Channel{Dict{String,Int}}
end

SymbolicRegression.init_plugin_state(opts::OpStatsOptions, datasets) =
    OpStatsState(opts.op_channel)

# ============================================================
# Step 3: Worker hook — count operators after each cycle
# ============================================================

function SymbolicRegression.on_population_evaluated!(
    state::OpStatsState, pop, dataset, hof, opts::OpStatsOptions
)
    counts = Dict{String,Int}()
    for member in pop.members
        _count_ops!(counts, get_tree(member.tree), opts)
    end
    put!(state.op_channel, counts)
end

# Recursive tree walk: increment counts for every operator node.
# (tree_mapreduce is designed for functional aggregation; a simple
# recursive walk is clearer for side-effectful counting.)
function _count_ops!(counts::Dict{String,Int}, node, opts)
    node.degree == 0 && return
    name = if node.degree == 1
        string(opts.operators.unaops[node.op])
    else
        string(opts.operators.binops[node.op])
    end
    counts[name] = get(counts, name, 0) + 1
    _count_ops!(counts, node.l, opts)
    node.degree == 2 && _count_ops!(counts, node.r, opts)
end

# ============================================================
# Step 4: Head-node hook — drain channel and print summary
# ============================================================

function SymbolicRegression.on_search_end!(
    state::OpStatsState, search_state, datasets, opts::OpStatsOptions, ropt
)
    totals = Dict{String,Int}()
    while isready(opts.op_channel)
        for (op, n) in take!(opts.op_channel)
            totals[op] = get(totals, op, 0) + n
        end
    end
    println("\n=== Operator frequencies ===")
    for (op, n) in sort(collect(totals); by=last, rev=true)
        println("  $op: $n")
    end
end

# ============================================================
# Step 5: Run equation_search with the plugin options
# ============================================================

base = Options(binary_operators=[+, *, -], unary_operators=[sin])
channel = Channel{Dict{String,Int}}(Inf)
opts = OpStatsOptions(base, channel)

# Target: y = 2x₁·sin(x₂) + x₃
X = rand(Float32, 3, 100)
y = @. 2f0 * X[1, :] * sin(X[2, :]) + X[3, :]

equation_search(X, y; options=opts, niterations=10, parallelism=:serial)
