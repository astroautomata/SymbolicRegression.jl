module MutationWeightsModule

using StatsBase: StatsBase

"""
    AbstractMutationWeights

Abstract type for mutation weight structs. Every field is treated as the name and
weight of a mutation type by the internal dispatch mechanism.

**Recommended usage**: use [`@extend_mutation_weights`](@ref) to create a subtype that
inherits all standard [`MutationWeights`](@ref) fields plus your own:

```julia
using SymbolicRegression

@extend_mutation_weights MyWeights begin
    my_mutation::Float64 = 0.5
end
```

This generates the struct, `Base.copy`, and `sample_mutation` automatically. Then
implement `mutate!` for your new mutation type. See [`@extend_mutation_weights`](@ref)
for the full recipe.

!!! note "All fields must be Float64"
    Every field in an `AbstractMutationWeights` subtype is used as a mutation weight.
    Non-Float64 fields are not supported. If you use `@extend_mutation_weights`, this
    is enforced at macro-expansion time.

# See Also

- [`@extend_mutation_weights`](@ref): Macro to define a custom subtype with pre-populated standard fields.
- [`MutationWeights`](@ref): The concrete default implementation.
- [`sample_mutation`](@ref): Function to sample a mutation based on current weights.
- [`mutate!`](@ref SymbolicRegression.MutateModule.mutate!): Function to apply a mutation to an expression tree.
- [`AbstractOptions`](@ref SymbolicRegression.OptionsStruct.AbstractOptions): See how to extend abstract types for customizing options.
"""
abstract type AbstractMutationWeights end

"""
    MutationWeights(;kws...) <: AbstractMutationWeights

This defines how often different mutations occur. These weightings
will be normalized to sum to 1.0 after initialization.

# Arguments

- `mutate_constant::Float64`: How often to mutate a constant.
- `mutate_operator::Float64`: How often to mutate an operator.
- `mutate_feature::Float64`: How often to mutate which feature a variable node references.
- `swap_operands::Float64`: How often to swap the operands of a binary operator.
- `rotate_tree::Float64`: How often to perform a tree rotation at a random node.
- `add_node::Float64`: How often to append a node to the tree.
- `insert_node::Float64`: How often to insert a node into the tree.
- `delete_node::Float64`: How often to delete a node from the tree.
- `simplify::Float64`: How often to simplify the tree.
- `randomize::Float64`: How often to create a random tree.
- `do_nothing::Float64`: How often to do nothing.
- `optimize::Float64`: How often to optimize the constants in the tree, as a mutation.
    Note that this is different from `optimizer_probability`, which is
    performed at the end of an iteration for all individuals.
- `form_connection::Float64`: **Only used for `GraphNode`, not regular `Node`**.
    Otherwise, this will automatically be set to 0.0. How often to form a
    connection between two nodes.
- `break_connection::Float64`: **Only used for `GraphNode`, not regular `Node`**.
    Otherwise, this will automatically be set to 0.0. How often to break a
    connection between two nodes.

# See Also

- [`AbstractMutationWeights`](@ref SymbolicRegression.CoreModule.MutationWeightsModule.AbstractMutationWeights): Use to define custom mutation weight types.
"""
Base.@kwdef mutable struct MutationWeights <: AbstractMutationWeights
    mutate_constant::Float64 = 0.0353
    mutate_operator::Float64 = 3.63
    mutate_feature::Float64 = 0.1
    swap_operands::Float64 = 0.00608
    rotate_tree::Float64 = 1.42
    add_node::Float64 = 0.0771
    insert_node::Float64 = 2.44
    delete_node::Float64 = 0.369
    simplify::Float64 = 0.00148
    randomize::Float64 = 0.00695
    do_nothing::Float64 = 0.431
    optimize::Float64 = 0.0
    form_connection::Float64 = 0.5
    break_connection::Float64 = 0.1
end

const mutations = fieldnames(MutationWeights)
const v_mutations = Symbol[mutations...]

# For some reason it's much faster to write out the fields explicitly:
let contents = [Expr(:., :w, QuoteNode(field)) for field in mutations]
    @eval begin
        function Base.convert(::Type{Vector}, w::MutationWeights)::Vector{Float64}
            return $(Expr(:vect, contents...))
        end
        function Base.copy(w::MutationWeights)
            return $(Expr(:call, :MutationWeights, contents...))
        end
    end
end

"""Sample a mutation, given the weightings."""
function sample_mutation(w::AbstractMutationWeights)
    weights = convert(Vector, w)
    return StatsBase.sample(v_mutations, StatsBase.Weights(weights))
end

"""
    @extend_mutation_weights Name begin
        extra_field::Float64 = default
        ...
    end

Define a new `AbstractMutationWeights` subtype with all standard
[`MutationWeights`](@ref) fields (with their default values) pre-populated,
plus any extra fields you declare in the block.

Also generates:
- A keyword constructor (via `Base.@kwdef`)
- `Base.copy`
- `sample_mutation` (samples over all fields, weighted by their values)

!!! note "Float64 fields only"
    All extra fields must be annotated `::Float64`. Every field in an
    `AbstractMutationWeights` subtype is treated as a mutation weight (probability)
    by the internal dispatch mechanism, so non-Float64 fields are not supported.
    The macro enforces this at expansion time.

# Example

```julia
@extend_mutation_weights PerturbWeights begin
    perturb_all_constants::Float64 = 0.5
end
```

This is equivalent to manually defining a `mutable struct` with all standard
fields copied from `MutationWeights` plus `perturb_all_constants`, along with the
required `Base.copy` and `sample_mutation` methods.

After defining the struct, implement `mutate!` for your new mutation type
(using `import SymbolicRegression: AbstractPopMember` and
`using DynamicExpressions: AbstractExpression`):

```julia
function SymbolicRegression.mutate!(
    tree::N, member::P, ::Val{:perturb_all_constants},
    weights::PerturbWeights, opts::MyOptions;
    kws...,
) where {N<:AbstractExpression, P<:AbstractPopMember}
    # ... apply mutation ...
    return MutationResult{N,P}(; tree=tree, num_evals=0.0)
end
```
"""
macro extend_mutation_weights(name, block)
    std_names = fieldnames(MutationWeights)
    defaults = MutationWeights()
    std_fields = [
        Expr(:(=), Expr(:(::), f, :Float64), getfield(defaults, f))
        for f in std_names
    ]
    extra_fields = filter(e -> !(e isa LineNumberNode), block.args)
    # Validate that every extra field is annotated ::Float64.
    # Required because _dispatch_mutations! treats every fieldname as a mutation
    # type, and the generated sample_mutation/copy collect field values as Float64.
    for ex in extra_fields
        type_ann = ex isa Expr && ex.head == :(=) ? ex.args[1] : ex
        if !(type_ann isa Expr && type_ann.head == :(::) && type_ann.args[2] == :Float64)
            error(
                "@extend_mutation_weights: extra fields must be annotated `::Float64`, got: $ex\n" *
                "Every field in an AbstractMutationWeights subtype is treated as a " *
                "mutation weight (probability), so only Float64 fields are supported.",
            )
        end
    end
    # GlobalRef ensures the generated method extends *this* module's sample_mutation,
    # not accidentally creating a new function in the calling module.
    sample_mutation_ref = GlobalRef(@__MODULE__, :sample_mutation)
    # Module-level const avoids allocating a new Vector{Symbol} on every
    # sample_mutation call — consistent with how v_mutations works for MutationWeights.
    mutations_const = esc(Symbol(:_, name, :_mutations))
    return quote
        Base.@kwdef mutable struct $(esc(name)) <: AbstractMutationWeights
            $(std_fields...)
            $(extra_fields...)
        end
        const $(mutations_const) = Symbol[fieldnames($(esc(name)))...]
        function Base.copy(w::$(esc(name)))
            return $(esc(name))(Float64[getfield(w, f) for f in $(mutations_const)]...)
        end
        function $(sample_mutation_ref)(w::$(esc(name)))
            weights = Float64[getfield(w, f) for f in $(mutations_const)]
            return StatsBase.sample($(mutations_const), StatsBase.Weights(weights))
        end
    end
end

end
