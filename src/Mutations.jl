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

Perturb a random constant. `perturbation_factor` scales the magnitude
(modulated by temperature); `probability_negate` is the chance of
flipping the constant's sign.
"""
Base.@kwdef struct MutateConstant <: AbstractMutation
    perturbation_factor::Float64 = 0.086
    probability_negate::Float64 = 0.01
end

struct MutateOperator <: AbstractMutation end
struct MutateFeature <: AbstractMutation end
struct SwapOperands <: AbstractMutation end
struct AddNode <: AbstractMutation end
struct InsertNode <: AbstractMutation end
struct DeleteNode <: AbstractMutation end
struct FormConnection <: AbstractMutation end
struct BreakConnection <: AbstractMutation end
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

struct Simplify <: AbstractMutation end
struct Randomize <: AbstractMutation end
struct Optimize <: AbstractMutation end
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
