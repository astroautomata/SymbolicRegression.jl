"""
Custom Mutation via the Plugin Interface (Layer 1)

This example adds a `:perturb_all_constants` mutation that adds Gaussian noise
to every constant in the tree simultaneously — contrast with the built-in
`mutate_constant` which changes only one at a time.

Recipe (4 steps):
  1. @extend_mutation_weights     — defines PerturbWeights with one extra field
  2. Custom AbstractOptions subtype  — stores perturb_strength + custom weights
  3. Override mutate!                — implements the mutation
  4. Run equation_search             — pass opts, get results

Run with:
    julia --project=. examples/plugin_mutation.jl
"""

using SymbolicRegression
import SymbolicRegression: AbstractOptions, AbstractPopMember, MutationResult, mutate!
using DynamicExpressions: AbstractExpression, get_scalar_constants, set_scalar_constants!

# ============================================================
# Step 1: Custom AbstractMutationWeights subtype
# ============================================================
#
# @extend_mutation_weights generates the full struct with all 14 standard
# MutationWeights fields pre-populated, plus any extra fields you declare.
# It also generates Base.copy and sample_mutation automatically.

@extend_mutation_weights PerturbWeights begin
    perturb_all_constants::Float64 = 0.5
end

# ============================================================
# Step 2: Custom AbstractOptions subtype
# ============================================================

struct PerturbOptions{O<:AbstractOptions} <: AbstractOptions
    base::O
    perturb_strength::Float64
    mutation_weights::PerturbWeights
end

# Forward all property accesses to base, except our own fields
function Base.getproperty(o::PerturbOptions, k::Symbol)
    k === :perturb_strength  && return getfield(o, :perturb_strength)
    k === :mutation_weights  && return getfield(o, :mutation_weights)
    return getproperty(getfield(o, :base), k)
end

# ============================================================
# Step 3: Implement mutate! for :perturb_all_constants
# ============================================================

function mutate!(
    tree::N,
    member::P,
    ::Val{:perturb_all_constants},
    weights::PerturbWeights,
    opts::PerturbOptions;
    kws...,
) where {N<:AbstractExpression, P<:AbstractPopMember}
    x, refs = get_scalar_constants(tree)
    if isempty(x)
        # No constants to perturb — return tree unchanged
        return MutationResult{N,P}(; tree=tree, num_evals=0.0)
    end
    x_new = x .+ opts.perturb_strength .* randn(eltype(x), length(x))
    set_scalar_constants!(tree, x_new, refs)
    return MutationResult{N,P}(; tree=tree, num_evals=0.0)
end

# ============================================================
# Step 4: Run equation_search with the custom options
# ============================================================

base = Options(binary_operators=[+, *, -], unary_operators=[sin])
opts = PerturbOptions(base, 0.1, PerturbWeights())

# Target: y = 2x₁ + 3x₂ - 1
X = rand(Float32, 2, 100)
y = @. 2f0 * X[1, :] + 3f0 * X[2, :] - 1f0

equation_search(X, y; options=opts, niterations=10, parallelism=:serial)
