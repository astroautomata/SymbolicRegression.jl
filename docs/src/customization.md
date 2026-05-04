# Customization

Many parts of SymbolicRegression.jl are designed to be customizable.

The normal way to do this in Julia is to define a new type that subtypes
an abstract type from a package, and then define new methods for the type,
extending internal methods on that type.

## Custom Options

For example, you can define a custom options type:

```@docs
AbstractOptions
```

Any function in SymbolicRegression.jl you can generally define a new method
on your custom options type, to define custom behavior.

## Custom Mutations

You can define custom mutation operators by defining a new method on
`mutate!`, as well as subtyping `AbstractMutationWeights`:

```@docs
mutate!
AbstractMutationWeights
condition_mutation_weights!
sample_mutation
MutationResult
```

## Custom Expressions

You can create your own expression types by defining a new type that extends `AbstractExpression`.

```@docs
AbstractExpression
```

The interface is fairly flexible, and permits you define specific functional forms,
extra parameters, etc. See the documentation of DynamicExpressions.jl for more details on what
methods you need to implement. You can test the implementation of a given interface by using
`ExpressionInterface` which makes use of `Interfaces.jl`:

```@docs
ExpressionInterface
```

Then, for SymbolicRegression.jl, pass an `expression_spec` to `Options`.
`expression_spec` is the preferred way to select expression types and related
construction options. The older `expression_type` and `expression_options`
keywords are deprecated.

You can look at the files `src/ParametricExpression.jl` and `src/TemplateExpression.jl`
for more examples of custom expression types, though note that `ParametricExpression` itself
is defined in DynamicExpressions.jl, while that file just overloads some methods for
SymbolicRegression.jl.

### Custom expression wrappers

For plugin expression types that wrap a normal DynamicExpressions tree, subtype
`AbstractComposableExpression`. Store the inner tree in one field and metadata in
another field, then define `constructorof` so parsing, mutation, simplification,
and template construction can rebuild your expression type.

```julia
using DynamicExpressions:
    DynamicExpressions,
    AbstractExpressionNode,
    AbstractOperatorEnum,
    EvalOptions,
    Metadata,
    get_contents,
    get_metadata
using SymbolicRegression
using SymbolicRegression: AbstractComposableExpression

mutable struct MyExpression{T,N<:AbstractExpressionNode{T},D} <:
               AbstractComposableExpression{T,N}
    tree::N
    metadata::Metadata{D}
end

function MyExpression(
    tree::AbstractExpressionNode{T};
    operators::Union{AbstractOperatorEnum,Nothing}=nothing,
    variable_names::Union{AbstractVector{<:AbstractString},Nothing}=nothing,
    eval_options::Union{EvalOptions,Nothing}=nothing,
    scale::Real=one(T),
) where {T}
    return MyExpression(
        tree, Metadata((; operators, variable_names, eval_options, scale=T(scale)))
    )
end

DynamicExpressions.constructorof(::Type{<:MyExpression}) = MyExpression

Base.copy(ex::MyExpression) =
    MyExpression(copy(get_contents(ex)), copy(get_metadata(ex)))
```

This wrapper pattern is directly supported as the inner expression type for
template expressions:

```julia
structure = TemplateStructure{(:f,)}(
    ((; f), (x,)) -> f(x);
    num_features=(; f=1),
)

spec = TemplateExpressionSpec(;
    structure,
    inner_expression_type=MyExpression,
    inner_expression_options=(; scale=1.0),
)

options = Options(;
    binary_operators=(+, *),
    unary_operators=(),
    expression_spec=spec,
)
```

If your loss needs expression-level metadata, use `loss_function_expression`
rather than `loss_function`, so the first argument is the full expression object.
If metadata or other expression state should be optimized together with scalar
tree constants, implement the optimizable-parameter hooks described in the
[Plugin Guide](plugin-guide.md#exposing-extra-optimizable-parameters).

If your metadata contains mutable arrays or parameter stores, make `Base.copy`
copy those fields explicitly so copied expressions do not share mutable state.

## Plugin Interface (Lifecycle Hooks + Persistent State)

For cross-generation state, concept databases, and search-level callbacks, use the
plugin interface. See the [Plugin Guide](plugin-guide.md) for a full walkthrough.

## Other Customizations

Other internal abstract types include the following:

```@docs
AbstractRuntimeOptions
AbstractSearchState
```

These let you include custom state variables and runtime options.
