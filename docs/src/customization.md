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

## Custom Plugins

Define a plugin configuration type by subtyping `AbstractPlugin`. Plugin state
is created separately with `init_plugin_state`, and hooks dispatch on the
plugin type.

```@docs
PluginInterface
```

Use `PluginInterface` to test the complete plugin contract. Hooks left at
their default implementations are valid. The test also checks that custom
hook methods accept the head or worker state produced by the plugin state
lifecycle:

```julia
using Interfaces: Arguments, test
using SymbolicRegression
using SymbolicRegression:
    AbstractPlugin,
    AbstractMutation,
    Dataset,
    MutationEvent,
    PluginInterface

mutable struct MutationCounterState
    count::Int
end

struct MutationCounterPlugin <: AbstractPlugin end

SymbolicRegression.init_plugin_state(
    ::MutationCounterPlugin, options, dataset
) = MutationCounterState(0)

function SymbolicRegression.on_mutation_end!(
    state::MutationCounterState,
    ::MutationCounterPlugin,
    ::AbstractMutation,
    ::MutationEvent,
    dataset,
    options,
)
    state.count += 1
    return nothing
end

plugin = MutationCounterPlugin()
options = Options(;
    plugins=(plugin,),
    default_plugins=(),
    default_mutations=(),
    mutations=(DoNothingMutation() => 1.0,),
)
dataset = Dataset(zeros(1, 8), zeros(8))
member = PopMember(
    dataset, Node(Float64; feature=1), options; deterministic=true
)
arguments = Arguments(;
    plugin,
    options,
    dataset,
    member,
    mutation=DoNothingMutation(),
)

@assert test(PluginInterface, MutationCounterPlugin, [arguments])
```

The required fields are `plugin`, `options`, `dataset`, `member`, and
`mutation`. Hooks that dispatch on more specific runtime values can also
receive those values through the additional fields documented by
`PluginInterface`.

## Custom Mutations

Define a custom mutation type by subtyping `AbstractMutation`, then define
its `mutate!` method and pass a weighted instance through `Options(; mutations=...)`:

```@docs
mutate!
AbstractMutation
condition_mutation_weights!
sample_mutation
MutationResult
```

Use `MutationInterface` to run the mutation with the same keyword context
provided by the engine and validate its `MutationResult`:

```julia
using Interfaces: Arguments, test
using SymbolicRegression
using SymbolicRegression:
    AbstractMutation, Dataset, MutationInterface, MutationResult, RecordType

struct MyMutation <: AbstractMutation end

function SymbolicRegression.mutate!(
    tree::N, ::P, ::MyMutation, options; kws...
) where {N,P}
    return MutationResult{N,P}(; tree)
end

mutation = MyMutation()
options = Options(;
    default_plugins=(),
    default_mutations=(),
    mutations=(mutation => 1.0,),
)
dataset = Dataset(zeros(1, 8), zeros(8))
member = PopMember(
    dataset, Node(Float64; feature=1), options; deterministic=true
)
arguments = Arguments(;
    mutation,
    new_tree=copy(member.tree),
    parent_member=member,
    options,
    recorder=RecordType(),
    context=nothing,
    dataset,
    cost=member.cost,
    loss=member.loss,
    parent_ref=member.ref,
    curmaxsize=options.maxsize,
    nfeatures=1,
    plugin_states=(),
    population_for_backsolve=nothing,
)

@assert test(MutationInterface, MyMutation, [arguments])
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

Then, for SymbolicRegression.jl, you would
pass `expression_type` to the `Options` constructor, as well as any
`expression_options` you need (as a `NamedTuple`).

If needed, you may need to overload `SymbolicRegression.ExpressionBuilder.extra_init_params` in
case your expression needs additional parameters. See the method for `ParametricExpression`
as an example.

You can look at the files `src/ParametricExpression.jl` and `src/TemplateExpression.jl`
for more examples of custom expression types, though note that `ParametricExpression` itself
is defined in DynamicExpressions.jl, while that file just overloads some methods for
SymbolicRegression.jl.

## Other Customizations

Other internal abstract types include the following:

```@docs
AbstractRuntimeOptions
AbstractSearchState
```

These let you include custom state variables and runtime options.
