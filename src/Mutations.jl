module MutationsModule

"""
    AbstractMutation

A mutation kind is a singleton struct subtyping `AbstractMutation`. The
engine dispatches the per-cycle `mutate!` method on the mutation's type;
weight sampling, plugin observation hooks, and `condition_mutation_weights!`
all key off the type.

To add a new mutation kind, define a struct + a `mutate!` method:

```julia
struct MyMutation <: AbstractMutation end

function SymbolicRegression.mutate!(
    new_tree, parent_member, ::MyMutation, mutations, options; kws...
)
    # ... modify new_tree ...
    return MutationResult(; tree=new_tree)
end
```

Then include it in `Options(; mutations = [default_mutations()..., MyMutation() => 0.1])`.

!!! warning "Experimental"
    Per-mutation config (e.g. `MutateConstant(perturbation_factor=0.1)`) is
    not yet supported; config still lives on `Options`. Migration is planned.
"""
abstract type AbstractMutation end

"""
    BacksolveOptions(; max_library_size=500, lambda=0.01, max_iter=10)

Config for the [`Backsolve`](@ref) mutation's sparse-expression fit.

!!! warning
    Experimental. May change in minor version increments.
"""
Base.@kwdef struct BacksolveOptions
    max_library_size::Int = 500
    lambda::Float64 = 0.01
    max_iter::Int = 10
end

struct MutateConstant   <: AbstractMutation end
struct MutateOperator   <: AbstractMutation end
struct MutateFeature    <: AbstractMutation end
struct SwapOperands     <: AbstractMutation end
struct AddNode          <: AbstractMutation end
struct InsertNode       <: AbstractMutation end
struct DeleteNode       <: AbstractMutation end
struct FormConnection   <: AbstractMutation end
struct BreakConnection  <: AbstractMutation end
struct RotateTree       <: AbstractMutation end
Base.@kwdef struct Backsolve <: AbstractMutation
    options::BacksolveOptions = BacksolveOptions()
end
struct Simplify         <: AbstractMutation end
struct Randomize        <: AbstractMutation end
struct Optimize         <: AbstractMutation end
struct DoNothing        <: AbstractMutation end

"""
    default_mutations() -> Vector{Pair{AbstractMutation,Float64}}

Default mutation list with the historical `MutationWeights` weights, in the
same order as `fieldnames(MutationWeights)` so backwards-compat conversion
from `MutationWeights` is straightforward.
"""
function default_mutations()
    return Pair{AbstractMutation,Float64}[
        MutateConstant() => 0.0353,
        MutateOperator() => 3.63,
        MutateFeature()  => 0.1,
        SwapOperands()   => 0.00608,
        RotateTree()     => 1.42,
        AddNode()        => 0.0771,
        InsertNode()     => 2.44,
        DeleteNode()     => 0.369,
        Simplify()       => 0.00148,
        Randomize()      => 0.00695,
        DoNothing()      => 0.431,
        Optimize()       => 0.0,
        Backsolve()      => 0.0,
        FormConnection() => 0.5,
        BreakConnection()=> 0.1,
    ]
end

end  # module MutationsModule
