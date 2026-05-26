module MutationsModule

"""
    AbstractMutation

A mutation kind is a struct (often `Base.@kwdef` for per-mutation config)
subtyping `AbstractMutation`. The engine dispatches the per-cycle `mutate!`
method on the mutation's type; weight sampling, plugin observation hooks,
and `condition_mutation_weights!` all key off the type.

To add a new mutation kind, define a struct + a `mutate!` method:

```julia
struct MyMutation <: AbstractMutation end

function SymbolicRegression.mutate!(
    new_tree, parent_member, ::MyMutation, options; kws...
)
    # ... modify new_tree ...
    return MutationResult(; tree=new_tree)
end
```

Then include it in `Options(; mutations = [default_mutations()..., MyMutation() => 0.1])`.

!!! warning "Experimental"
"""
abstract type AbstractMutation end

"""
    MutateConstant(; perturbation_factor=0.086, probability_negate=0.01)

Perturb a random constant. `perturbation_factor` scales the magnitude;
`probability_negate` is the chance of flipping the constant's sign.

Per-call plugin modulation (e.g. `SimulatedAnnealingPlugin` shrinking the
perturbation magnitude across an iteration) flows through
[`MutateConstantContext`](@ref), not the immutable struct itself.
"""
Base.@kwdef struct MutateConstant <: AbstractMutation
    perturbation_factor::Float64 = 0.086
    probability_negate::Float64 = 0.01
end

"""
    MutateConstantContext

Per-call mutable companion of [`MutateConstant`](@ref). Holds **only**
the fields plugins are allowed to layer per-call modulation on top of
(currently just `perturbation_factor`); static fields like
`probability_negate` remain on the immutable mutation. The body of
`mutate_constant` reads `perturbation_factor` from this context and any
other field directly from the mutation.
"""
Base.@kwdef mutable struct MutateConstantContext
    perturbation_factor::Float64
end

"""Swap a random operator for another of the same arity."""
struct MutateOperator <: AbstractMutation end

"""Reassign a random variable leaf to a different input feature."""
struct MutateFeature <: AbstractMutation end

"""Swap the operands of a random binary operator."""
struct SwapOperands <: AbstractMutation end

"""Append a random new operator (with fresh leaves) at a random leaf."""
struct AddNode <: AbstractMutation end

"""Insert a random new operator between an existing node and its parent."""
struct InsertNode <: AbstractMutation end

"""Delete a random non-leaf node, replacing it with one of its children."""
struct DeleteNode <: AbstractMutation end

"""Form a shared-subtree connection between two nodes (graph-mode only)."""
struct FormConnection <: AbstractMutation end

"""Break a shared-subtree connection by deep-copying one of the references."""
struct BreakConnection <: AbstractMutation end

"""Rotate a random subtree (rebalancing the AST)."""
struct RotateTree <: AbstractMutation end

"""
    Backsolve(; max_library_size=500, lambda=0.01, max_iter=10)

Invert a random non-root node by solving for its target values, then
replace it with a sparse-expression fit (STLSQ).

!!! warning
    Experimental. May change in minor version increments.
"""
Base.@kwdef struct Backsolve <: AbstractMutation
    max_library_size::Int = 500
    lambda::Float64 = 0.01
    max_iter::Int = 10
end

"""Algebraically simplify the tree (e.g. fold constants)."""
struct Simplify <: AbstractMutation end

"""Replace the tree with a freshly generated random tree."""
struct Randomize <: AbstractMutation end

"""Run gradient-based constant optimization on the tree (reads optimizer settings from `options`)."""
struct Optimize <: AbstractMutation end

"""No-op mutation: copy the parent unchanged (acts as a sampling weight reserve)."""
struct DoNothing <: AbstractMutation end

"""
    default_mutations() -> Vector{Pair{AbstractMutation,Float64}}

Default mutation list with the historical `MutationWeights` weights. The
weights match `MutationWeights`' field defaults but the order is keyed by
type, not by the field-name order — conversion from `MutationWeights` is
done by `_mutations_from_weights` via an explicit symbol → type mapping.
"""
function default_mutations()
    return Pair{AbstractMutation,Float64}[
        MutateConstant() => 0.0353,
        MutateOperator() => 3.63,
        MutateFeature() => 0.1,
        SwapOperands() => 0.00608,
        RotateTree() => 1.42,
        AddNode() => 0.0771,
        InsertNode() => 2.44,
        DeleteNode() => 0.369,
        Simplify() => 0.00148,
        Randomize() => 0.00695,
        DoNothing() => 0.431,
        Optimize() => 0.0,
        Backsolve() => 0.0,
        FormConnection() => 0.5,
        BreakConnection() => 0.1,
    ]
end

end  # module MutationsModule
