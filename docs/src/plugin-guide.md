# Plugin Development Guide

> **Experimental**: The plugin interface is experimental. Design may change until validated by multiple plugin packages.

SymbolicRegression.jl provides two main extension layers, plus candidate-local
state hooks for custom expression types. This guide walks through each scope,
when to use it, and how to combine them for real-world plugins.

---

## Overview: Layers and State Scopes

| Layer       | Scope                    | Mechanism                                          | Best for                                                             |
| ----------- | ------------------------ | -------------------------------------------------- | -------------------------------------------------------------------- |
| **Layer 1** | **Algorithm overrides**  | Dispatch on a custom `AbstractOptions` subtype     | Swapping out algorithms (complexity, loss, optimizer, mutations)     |
| **Layer 1** | **Expression state**     | Expression-local optimizable parameter hooks       | Extra differentiable state owned by one expression object            |
| **Layer 1** | **Template state**       | Candidate-local `TemplateExpression` hooks         | State shared by multiple template subexpressions in one candidate    |
| **Layer 2** | **Lifecycle state**      | Lifecycle hooks + per-worker `AbstractPluginState` | Cross-generation state, concept databases, logging, steering         |

Layer 1 and Layer 2 remain the main mental model: Layer 1 changes how
candidates behave or are optimized, while Layer 2 manages state across the
search loop. Expression-local and template shared-state hooks are candidate-local
state scopes used within Layer 1.

---

## Using a Plugin

If you're using an existing plugin package, the workflow is:

```julia
using SymbolicRegression
using SomePlugin  # defines SomeOptions <: AbstractOptions

base = Options(binary_operators=[+, *, -, /], unary_operators=[sin, exp])
opts = SomeOptions(base; plugin_param=0.3)  # plugin's options type wraps base

equation_search(X, y; options=opts, niterations=10)
```

That's all — no extra imports or registration required. The plugin's methods are
loaded automatically when you `using` the package.

---

## Layer 1: Algorithm Overrides via `AbstractOptions`

Every core algorithm in SR.jl dispatches on `options::AbstractOptions`. To override any piece of the algorithm, define a custom options type and add a method.

### Defining a custom options type

```julia
using SymbolicRegression
import SymbolicRegression: AbstractOptions

struct MyOptions{O<:AbstractOptions} <: AbstractOptions
    base::O
    my_param::Float64
end

# Forward all standard option fields to base
Base.getproperty(o::MyOptions, k::Symbol) =
    k === :my_param ? getfield(o, :my_param) :
    getproperty(getfield(o, :base), k)
```

Then pass it to `equation_search`:

```julia
base = Options(binary_operators=[+, *, /, -], unary_operators=[sin, cos])
opts = MyOptions(base, 2.0)
equation_search(X, y; options=opts)
```

### Overriding `compute_complexity`

```julia
using DynamicExpressions: AbstractExpression, count_nodes, get_tree

function SymbolicRegression.compute_complexity(tree::AbstractExpression, opts::MyOptions; kws...)
    # e.g., penalize trigonometric functions more
    return count_nodes(get_tree(tree)) + 2 * count_trig(get_tree(tree))
end
```

Override the `AbstractExpression` method — the `AbstractPopMember` overload just reads a
cached value and delegates to `compute_complexity(member.tree, options)`, so the tree-level
method is the correct entry point.

See [`compute_complexity`](@ref) for the default implementation.

### Overriding `eval_cost`

```julia
function SymbolicRegression.eval_cost(dataset, member, opts::MyOptions; kws...)
    cost, loss = invoke(
        SymbolicRegression.eval_cost,
        Tuple{Dataset,Any,AbstractOptions},
        dataset, member, opts; kws...
    )
    # Add a custom structural penalty
    return cost + structural_penalty(member.tree, opts.my_param), loss
end
```

See [`eval_cost`](@ref) for the default implementation.

### Exposing extra optimizable parameters

If a plugin expression type wants the built-in constant optimizer to see more than
ordinary scalar constants in the tree, first implement:

- [`get_optimizable_parameters`](@ref)
- [`set_optimizable_parameters!`](@ref)
- [`extract_optimizable_gradient`](@ref)

These hooks flatten extra expression state into the same vector as ordinary tree
constants, so the default [`optimize_constants`](@ref) loop can optimize both.
Only override `optimize_constants` when you need a custom optimization algorithm,
explicit constraints, or custom restart behavior.

!!! note "Autodiff backend support"
Custom optimizable metadata works with the default `autodiff_backend=nothing`
path and generic DifferentiationInterface backends. The Enzyme extension
currently handles ordinary scalar constants only.

This assumes your custom expression type is already used in the search, typically
by passing it through an `expression_spec`. See
[Custom expression wrappers](customization.md#custom-expression-wrappers) for the
full setup.

For example, a mutable expression wrapper with ordinary tree constants and one
extra metadata scalar, `scale`, can expose both in one optimizable vector:

```julia
using DynamicExpressions:
    get_contents,
    get_metadata,
    get_scalar_constants,
    set_scalar_constants!,
    extract_gradient,
    Metadata

function SymbolicRegression.get_optimizable_parameters(ex::MyExpression{T}) where {T}
    tree_values, tree_refs = get_scalar_constants(get_contents(ex))
    metadata = get_metadata(ex)
    return vcat(tree_values, T[metadata.scale]), (;
        tree_refs, n_tree=length(tree_values)
    )
end

function SymbolicRegression.set_optimizable_parameters!(
    ex::MyExpression{T}, x, refs
) where {T}
    set_scalar_constants!(get_contents(ex), x[1:(refs.n_tree)], refs.tree_refs)

    metadata = get_metadata(ex)
    ex.metadata = Metadata((;
        operators=metadata.operators,
        variable_names=metadata.variable_names,
        eval_options=metadata.eval_options,
        scale=T(x[refs.n_tree + 1]),
    ))
    return ex
end

function SymbolicRegression.extract_optimizable_gradient(
    grad, ex::MyExpression{T}
) where {T}
    tree_gradient = extract_gradient(get_contents(grad), get_contents(ex))
    return vcat(tree_gradient, T[get_metadata(grad).scale])
end
```

The gradient object supplied by the autodiff backend must expose the same
differentiable metadata fields that your hook reads, such as
`get_metadata(grad).scale` above.

### Sharing state across `TemplateExpression` subexpressions

Expression-local hooks expose state owned by one expression object. In contrast,
some template plugins need state that is owned by the whole candidate and shared
by every inner expression in a `TemplateExpression`. For example, a template may
contain `f` and `g`, but both should refer to the same learned operator
parameters inside one population member. Another population member should still
receive its own independent copy of those parameters.

Use the template shared-state hooks for this case:

- [`NoTemplateSharedState`](@ref)
- [`template_shared_state`](@ref)
- [`get_template_shared_state`](@ref)
- [`copy_template_shared_state`](@ref)
- [`attach_template_shared_state`](@ref)
- [`get_template_optimizable_parameters`](@ref)
- [`set_template_optimizable_parameters!`](@ref)
- [`extract_template_optimizable_gradient`](@ref)

The hook dispatch key is the inner expression type `E` used by the
`TemplateExpression`. A minimal shared-state implementation looks like:

```julia
using DynamicExpressions: get_contents, get_metadata, with_metadata
import SymbolicRegression:
    template_shared_state,
    get_template_shared_state,
    copy_template_shared_state,
    attach_template_shared_state

mutable struct MySharedState
    weight::Float64
end

template_shared_state(
    ::Type{<:MyExpression}, contents::NamedTuple, metadata
) = MySharedState(0.0)

function get_template_shared_state(::Type{<:MyExpression}, ex::TemplateExpression)
    states = MySharedState[]
    for inner in values(get_contents(ex))
        state = get_metadata(inner).state
        any(existing -> existing === state, states) || push!(states, state)
    end
    length(states) == 1 || error("template inners do not share state")
    return only(states)
end

copy_template_shared_state(
    ::Type{<:MyExpression}, state::MySharedState
) = MySharedState(state.weight)

attach_template_shared_state(
    ::Type{<:MyExpression}, inner::MyExpression, state::MySharedState, key::Symbol
) = with_metadata(inner; state)
```

`template_shared_state` is applied by the public keyword constructor for
`TemplateExpression`, by expression parsing/creation paths that go through that
constructor, and by template `copy`/`copy_into!`. The raw
`TemplateExpression(contents, metadata)` constructor preserves the contents it
is given. This matters for gradient objects, which may intentionally contain
separate per-subexpression gradient state that should be reduced by
`extract_template_optimizable_gradient`.

If the shared state is optimizable, override the template-level optimizer hooks
instead of the ordinary expression-level hooks. The template-level hooks should
flatten candidate-local state once, then include any template parameters from
`get_metadata(ex).parameters` if those should remain optimizable.

### Overriding `optimize_constants`

```julia
function SymbolicRegression.optimize_constants(dataset, member, opts::MyOptions; kws...)
    # Use a completely custom optimizer
    return my_custom_optimizer(dataset, member, opts)
end
```

See [`optimize_constants`](@ref) for the default implementation.

### Overriding `mutate!`

Use [`@extend_mutation_weights`](@ref) to define the weights type, then implement `mutate!`:

```julia
import SymbolicRegression: AbstractOptions, AbstractPopMember, MutationResult, mutate!
using DynamicExpressions: AbstractExpression

@extend_mutation_weights MyWeights begin
    my_mutation::Float64 = 0.5
end

function SymbolicRegression.mutate!(
    tree::N, member::P, ::Val{:my_mutation},
    weights::MyWeights, opts::MyOptions;
    kws...,
) where {N<:AbstractExpression, P<:AbstractPopMember}
    new_tree = apply_my_mutation(tree, opts.my_param)
    return MutationResult{N,P}(; tree=new_tree, num_evals=0.0)
end
```

`@extend_mutation_weights` generates the struct with all 14 standard [`MutationWeights`](@ref)
fields pre-populated, plus `Base.copy` and `sample_mutation` automatically. The one thing
that still requires care: use precise type bounds (`N<:AbstractExpression, P<:AbstractPopMember`)
on your `mutate!` to avoid ambiguity with the fallback error method.

If your mutation needs access to the worker plugin state, capture it from `kws...`:

```julia
function SymbolicRegression.mutate!(
    tree::N, member::P, ::Val{:concept_guided},
    weights::MyWeights, opts::MyOptions;
    plugin_state::MyPluginState, kws...,
) where {N<:AbstractExpression, P<:AbstractPopMember}
    new_tree = guide_from_concepts(tree, plugin_state.concept_db)
    return MutationResult{N,P}(; tree=new_tree, num_evals=0.0)
end
```

A complete runnable example is in
[`examples/plugin_mutation.jl`](https://github.com/MilesCranmer/SymbolicRegression.jl/blob/master/examples/plugin_mutation.jl).

```@docs
@extend_mutation_weights
```

See [`mutate!`](@ref SymbolicRegression.MutateModule.mutate!) and [`AbstractMutationWeights`](@ref) for more details.

---

## Layer 2: Lifecycle Hooks + Persistent State

For cross-generation state (e.g., a concept database that evolves alongside the search), use `AbstractPluginState` and the lifecycle hooks.

### Key types

```@docs
AbstractPluginState
NoPluginState
```

### Hook reference

```@docs
init_plugin_state
on_search_start!
on_search_end!
on_generation_complete!
on_population_evaluated!
on_mutation_evaluated!
init_member
```

### How it works

1. `init_plugin_state(options, datasets)` is called on the **head node** (receives the full `datasets` vector) to create the state stored in `SearchState`.
2. Per-worker state is initialized lazily: on the first `s_r_cycle` call, each worker calls `init_plugin_state(options, (dataset,))` (receives a single-element tuple) to create a local copy.
3. `on_search_start!` and `on_search_end!` run once on the head node.
4. `on_generation_complete!` runs on the head node each time any population completes a cycle (after HoF update + migration) — safe to mutate state. With `populations=N`, this fires up to `N` times per "global" generation step.
5. `on_population_evaluated!` runs on the **worker** after each `s_r_cycle` — may be concurrent.
6. `init_member` runs on the worker during **initial population creation only** — it is not called during ongoing mutations. To inject trees into the running search, use the `seed_members` field of `SearchState` via `on_generation_complete!`. Note that `seed_members[j]` **persists across generations** — it is read but never cleared by the search loop, so whatever you push will be re-injected on every subsequent generation. Clear it manually (e.g., `empty!(search_state.seed_members[j])`) after a one-shot injection.

---

## Worked Example: LaSR-Style Concept Database

[LaSR](https://trishullab.github.io/lasr-web/) (Language-guided Adaptive Symbolic Regression)
is an existing system built on SymbolicRegression.jl that uses a concept database to
guide the search with an LLM. This example sketches the same architectural pattern.

**Key design point**: the head node and each worker have _separate_ `AbstractPluginState`
instances. To share data from head to workers, store a `Channel` in `options` — the head
pushes batches of concepts in, workers drain it into their local state.

```julia
using SymbolicRegression
import SymbolicRegression:
    AbstractOptions, AbstractPluginState, init_plugin_state,
    on_generation_complete!, on_population_evaluated!, init_member

# --- Plugin state (one instance per worker, plus one on head node) ---

mutable struct LaSRState <: AbstractPluginState
    local_concepts::Vector{Any}  # worker-local, populated via channel
end

# --- Custom options (holds the shared channel for head→worker comms) ---

struct LaSROptions{O<:AbstractOptions} <: AbstractOptions
    base::O
    concept_prob::Float64
    concept_channel::Channel{Vector{Any}}  # head pushes, workers drain
end
Base.getproperty(o::LaSROptions, k::Symbol) =
    k in (:concept_prob, :concept_channel) ? getfield(o, k) :
    getproperty(getfield(o, :base), k)

# --- Hook implementations ---

# Called once per worker (and once on head node) at startup
SymbolicRegression.init_plugin_state(opts::LaSROptions, datasets) = LaSRState([])

# HEAD NODE: harvest good trees from HoF and push to channel each generation
function SymbolicRegression.on_generation_complete!(
    state::LaSRState, search_state, datasets, opts::LaSROptions, ropt
)
    good_trees = Any[
        copy(member.tree)
        for hof in search_state.halls_of_fame
        for member in hof.members[hof.exists]
        if member.loss < 0.01
    ]
    isempty(good_trees) || put!(opts.concept_channel, good_trees)
end

# WORKER: drain channel into local state after each cycle
function SymbolicRegression.on_population_evaluated!(
    state::LaSRState, pop, dataset, hof, opts::LaSROptions
)
    while isready(opts.concept_channel)
        append!(state.local_concepts, take!(opts.concept_channel))
        # Keep only the most recent 50 concepts
        if length(state.local_concepts) > 50
            deleteat!(state.local_concepts, 1:(length(state.local_concepts) - 50))
        end
    end
end

# WORKER: sample from local concepts when initializing new population members
function SymbolicRegression.init_member(
    state::LaSRState, dataset, opts::LaSROptions
)
    isempty(state.local_concepts) && return nothing
    rand() < opts.concept_prob || return nothing
    return copy(rand(state.local_concepts))
end

# --- Usage (:serial or :multithreading) ---

base = Options(binary_operators=[+, *, -, /], unary_operators=[sin, exp])
channel = Channel{Vector{Any}}(Inf)  # unbounded so put! never blocks
opts = LaSROptions(base, 0.3, channel)

X = rand(Float32, 3, 100)
y = 2f0 .* sin.(X[1, :]) .* X[2, :] .+ X[3, :]

result = equation_search(X, y; options=opts, niterations=10, parallelism=:serial)
```

> **Multiprocessing note**: `Channel` only works within a single process. For
> `:multiprocessing`, replace `Channel` with `RemoteChannel` and adjust the
> `put!`/`take!` calls accordingly.

A complete, runnable Layer 2 example (operator frequency reporter) is in
[`examples/plugin_operator_stats.jl`](https://github.com/MilesCranmer/SymbolicRegression.jl/blob/master/examples/plugin_operator_stats.jl).

For a complete example of `on_mutation_evaluated!` driving adaptive mutation
weights, see
[`examples/plugin_adaptive_weights.jl`](https://github.com/MilesCranmer/SymbolicRegression.jl/blob/master/examples/plugin_adaptive_weights.jl).

---

## Threading and Multiprocessing Safety

### What runs where

| Hook                       | Where                                         | Concurrency                         |
| -------------------------- | --------------------------------------------- | ----------------------------------- |
| `init_plugin_state`        | Head node (once) + each worker (once, lazily) | Safe                                |
| `on_search_start!`         | Head node                                     | Serial                              |
| `on_generation_complete!`  | Head node (once per population cycle)         | Serial                              |
| `on_search_end!`           | Head node (after all workers finish)          | Serial                              |
| `on_population_evaluated!` | Worker                                        | **Concurrent** in `:multithreading` |
| `on_mutation_evaluated!`   | Worker (once per `next_generation` return)    | **Concurrent** in `:multithreading` |
| `init_member`              | Head node (initial population creation only)  | **Concurrent** in `:multithreading` |

### Rules

- **Head node hooks** (`on_generation_complete!`, `on_search_start!`, `on_search_end!`) are always serial — safe to mutate shared state.
- **Worker hooks** (`on_population_evaluated!`, `on_mutation_evaluated!`) may run concurrently in multithreading mode. Each `(output, population)` slot has its own `AbstractPluginState` Ref, so **there are no races between slots**. Each worker thread only touches its own state.
- **`init_member`** uses the **head node's** state and is called only during initial population creation. In `:multithreading`, multiple population slots are created concurrently — keep `init_member` read-only or thread-safe.
- **Template shared state** lives inside expression candidates, not in `AbstractPluginState`. It is copied when candidates are copied, so each population member owns independent candidate-local state even if its template subexpressions share within that member.
- To push data from workers to the head node (e.g., promising trees found during evaluation), use a `Channel{T}` stored in your options and drained in `on_generation_complete!`.

### Multiprocessing

In `:multiprocessing` mode, your `AbstractOptions` subtype is serialized to remote workers via `Distributed`. Ensure all fields of your options type are serializable. Worker-local `AbstractPluginState` is initialized fresh on each worker process — it is never serialized back to the head node. Use a `RemoteChannel` for cross-process communication.

---

## Structuring a Plugin Package

A typical plugin package looks like:

```
MyPlugin.jl/
├── Project.toml           # SymbolicRegression as a dependency
├── src/
│   ├── MyPlugin.jl        # top-level module, exports MyOptions
│   ├── state.jl           # AbstractPluginState subtype + ConceptDB
│   ├── hooks.jl           # init_plugin_state, on_generation_complete!, etc.
│   └── mutations.jl       # custom mutate! methods (optional)
└── test/
    └── runtests.jl
```

```julia
# src/MyPlugin.jl
module MyPlugin

using SymbolicRegression
import SymbolicRegression:
    AbstractOptions, AbstractPluginState, init_plugin_state,
    on_generation_complete!, on_population_evaluated!, init_member

export MyOptions

include("state.jl")
include("hooks.jl")
include("mutations.jl")

end
```

Avoid re-exporting all of SymbolicRegression — let users bring in what they need.
