module ConstantOptimizationModule

using Random: AbstractRNG, default_rng
using LineSearches: LineSearches
using Optim: Optim
using NLSolversBase: NLSolversBase
using ADTypes: AbstractADType, AutoEnzyme
using DifferentiationInterface: value_and_gradient, prepare_gradient
using DynamicExpressions:
    AbstractExpression,
    AbstractExpressionNode,
    Expression,
    OperatorEnum,
    FeatureMajorMatrix,
    get_tree,
    get_child,
    get_operators,
    preserve_sharing,
    with_contents,
    eval_tree_array,
    constructorof,
    get_scalar_constants,
    set_scalar_constants!,
    extract_gradient
using DynamicExpressions.EvaluateModule: reset_index!
using DispatchDoctor: @unstable
using ..CoreModule:
    AbstractOptions,
    Dataset,
    DATA_TYPE,
    LOSS_TYPE,
    specialized_options,
    dataset_fraction,
    eval_X,
    with_eval_X,
    has_units
using ..UtilsModule: get_birth_order, PerTaskCache, stable_get!
using ..LossFunctionsModule: create_eval_context, eval_loss, loss_to_cost
using ..PopMemberModule: AbstractPopMember, PopMember

function can_optimize(::AbstractExpression{T}, options) where {T}
    return can_optimize(T, options)
end
function can_optimize(::Type{T}, _) where {T<:Number}
    return true
end

"""
    get_constants_for_optimization(ex) -> x0, refs

Flatten all parameters optimized by `optimize_constants` into a single vector `x0`,
along with any references needed by [`set_constants_for_optimization!`](@ref).

By default this forwards to `get_scalar_constants`.

New expression integrations should overload [`get_optimizable_parameters`](@ref)
instead. This method remains as a compatibility hook for existing integrations.
"""
get_constants_for_optimization(ex::AbstractExpression) = get_scalar_constants(ex)

"""
    set_constants_for_optimization!(ex, x, refs)

Set the optimizable parameters of `ex` from the flat vector `x`, using the `refs`
returned by [`get_constants_for_optimization`](@ref).

By default this forwards to `set_scalar_constants!`.

New expression integrations should overload [`set_optimizable_parameters!`](@ref)
instead. This method remains as a compatibility hook for existing integrations.
"""
function set_constants_for_optimization!(ex::AbstractExpression, x, refs)
    set_scalar_constants!(ex, x, refs)
end

"""
    extract_gradient_for_optimization(grad, ex)

Extract the gradient of all optimizable parameters of `ex` into the same flattened
order returned by [`get_constants_for_optimization`](@ref).

By default this forwards to `extract_gradient`.

New expression integrations should overload [`extract_optimizable_gradient`](@ref)
instead. This method remains as a compatibility hook for existing integrations.
"""
extract_gradient_for_optimization(grad, ex::AbstractExpression) = extract_gradient(grad, ex)

"""
    get_optimizable_parameters(ex, options) -> x0, refs

Flatten the parameters from `ex` that should be optimized under `options` into `x0`.
The returned `refs` object is passed unchanged to
[`set_optimizable_parameters!`](@ref) and
[`extract_optimizable_gradient`](@ref).

By default this forwards to [`get_constants_for_optimization`](@ref).

The returned `refs` is opaque and only valid for the expression state and `x0`
returned by the same call. Implementations must preserve parameter ordering across
this function, [`set_optimizable_parameters!`](@ref), and
[`extract_optimizable_gradient`](@ref).
"""
function get_optimizable_parameters(ex, options)
    return get_constants_for_optimization(ex)
end
function get_optimizable_parameters(ex::Expression, options)
    return get_scalar_constants(ex)
end

"""
    get_optimizable_parameters(context, ex, options) -> x0, refs

Flatten the parameters selected for `ex` by an owning `context`.

Structured expressions may route parameter selection through a context object such
as their combiner. By default the context does not alter constant selection.
"""
function get_optimizable_parameters(context, ex, options)
    return get_optimizable_parameters(ex, options)
end

"""
    set_optimizable_parameters!(ex, x, refs)

Set the optimizable parameters of `ex` from `x`, using the opaque `refs` object
returned by [`get_optimizable_parameters`](@ref).

By default this forwards to [`set_constants_for_optimization!`](@ref).

Implementations must consume parameters in exactly the order returned by
[`get_optimizable_parameters`](@ref).
"""
function set_optimizable_parameters!(ex, x, refs)
    return set_constants_for_optimization!(ex, x, refs)
end
function set_optimizable_parameters!(ex::Expression, x, refs)
    return set_scalar_constants!(ex, x, refs)
end

"""
    extract_optimizable_gradient(grad, ex, refs)

Extract the gradient of the selected parameters in the same order returned by
[`get_optimizable_parameters`](@ref). The `refs` object is the exact object returned
by that call, allowing custom integrations to preserve an active parameter subset.

By default this forwards to [`extract_gradient_for_optimization`](@ref).

Implementations must return one gradient entry for each parameter returned by
[`get_optimizable_parameters`](@ref), in the same order.
"""
function extract_optimizable_gradient(grad, ex, refs)
    return extract_gradient_for_optimization(grad, ex)
end
function extract_optimizable_gradient(grad, ex::Expression, refs)
    return extract_gradient(grad, ex)
end

@unstable function optimize_constants(
    dataset::Dataset{T,L},
    member::P,
    options::AbstractOptions;
    rng::AbstractRNG=default_rng(),
)::Tuple{P,Float64} where {T<:DATA_TYPE,L<:LOSS_TYPE,N,P<:AbstractPopMember{T,L,N}}
    can_optimize(member.tree, options) || return (member, 0.0)
    x0, refs = get_optimizable_parameters(member.tree, options)
    nconst = length(x0)
    nconst == 0 && return (member, 0.0)
    if nconst == 1 && !(T <: Complex)
        algorithm = Optim.Newton(; linesearch=LineSearches.BackTracking())
        return _optimize_constants(
            dataset,
            member,
            x0,
            refs,
            specialized_options(options),
            algorithm,
            options.optimizer_options,
            rng,
        )
    end
    return _optimize_constants(
        dataset,
        member,
        x0,
        refs,
        specialized_options(options),
        # We use specialized options here due to Enzyme being
        # more particular about dynamic dispatch
        options.optimizer_algorithm,
        options.optimizer_options,
        rng,
    )
end

function _plan_hoist(node::AbstractExpressionNode)::Tuple{Bool,Int}
    deg = node.degree
    deg == 0 && return (node.constant, 0)
    any_const = false
    nhoist = 0
    for i in 1:deg
        c, h = _plan_hoist(get_child(node, i))
        any_const |= c
        nhoist += h
    end
    return any_const ? (true, nhoist) : (false, 1)
end

function _collect_hoist_inputs!(
    node::N, orig_features::Vector{UInt16}, hoisted_nodes::Vector{N}
)::Bool where {N<:AbstractExpressionNode}
    deg = node.degree
    if deg == 0
        return node.constant
    end
    has_c = false
    for i in 1:deg
        if _has_any_constant(get_child(node, i))
            has_c = true
            break
        end
    end
    if !has_c
        if findfirst(==(node), hoisted_nodes) === nothing
            push!(hoisted_nodes, node)
        end
        return false
    end
    for i in 1:deg
        ch = get_child(node, i)
        if ch.degree == 0
            if !ch.constant && !(ch.feature in orig_features)
                push!(orig_features, ch.feature)
            end
        else
            _collect_hoist_inputs!(ch, orig_features, hoisted_nodes)
        end
    end
    return true
end

function _has_any_constant(node::AbstractExpressionNode)::Bool
    deg = node.degree
    deg == 0 && return node.constant
    for i in 1:deg
        _has_any_constant(get_child(node, i)) && return true
    end
    return false
end

function _build_hoisted_node(
    node::N,
    orig_features::Vector{UInt16},
    hoisted_nodes::Vector{N},
    m_orig::Int,
    opt_refs::Vector{Base.RefValue{N}},
)::N where {T,N<:AbstractExpressionNode{T}}
    deg = node.degree
    if deg == 0
        if node.constant
            leaf = constructorof(N)(T; val=node.val)
            push!(opt_refs, Ref(leaf))
            return leaf
        else
            idx = findfirst(==(node.feature), orig_features)::Int
            return constructorof(N)(T; feature=UInt16(idx))
        end
    end
    if !_has_any_constant(node)
        m = findfirst(==(node), hoisted_nodes)::Int
        return constructorof(N)(T; feature=UInt16(m_orig + m))
    end
    if deg == 1
        c1 = _build_hoisted_node(
            get_child(node, 1), orig_features, hoisted_nodes, m_orig, opt_refs
        )
        return constructorof(N)(T; op=node.op, children=(c1,))
    elseif deg == 2
        c1 = _build_hoisted_node(
            get_child(node, 1), orig_features, hoisted_nodes, m_orig, opt_refs
        )
        c2 = _build_hoisted_node(
            get_child(node, 2), orig_features, hoisted_nodes, m_orig, opt_refs
        )
        return constructorof(N)(T; op=node.op, children=(c1, c2))
    else
        cs = ntuple(
            i -> _build_hoisted_node(
                get_child(node, i), orig_features, hoisted_nodes, m_orig, opt_refs
            ),
            deg,
        )
        return constructorof(N)(T; op=node.op, children=cs)
    end
end

@unstable function _try_hoist_for_optimization(
    ex::Expression{T,N},
    dataset::Dataset{T,L},
    options::AbstractOptions,
    eval_context,
    n_params::Int,
) where {T<:Number,L<:LOSS_TYPE,N<:AbstractExpressionNode{T}}
    preserve_sharing(N) && return nothing
    ops = get_operators(ex, options)
    ops isa OperatorEnum || return nothing
    options.autodiff_backend === nothing || return nothing
    options.turbo isa Val{false} || return nothing
    has_units(dataset) && return nothing
    isnothing(options.loss_function) || return nothing
    isnothing(options.loss_function_expression) || return nothing
    X_base = eval_X(dataset)
    X_base isa FeatureMajorMatrix{T} || return nothing

    raw_tree = get_tree(ex)
    has_const, nhoist = _plan_hoist(raw_tree)
    (has_const && nhoist > 0) || return nothing

    orig_features = UInt16[]
    hoisted_nodes = N[]
    _collect_hoist_inputs!(raw_tree, orig_features, hoisted_nodes)
    m_orig = length(orig_features)
    k = length(hoisted_nodes)
    k == 0 && return nothing

    n = dataset.n
    nfeatures_base = size(X_base, 1)
    data = Matrix{T}(undef, n, m_orig + k)
    for i in 1:m_orig
        src_col = Int(@inbounds orig_features[i])
        (1 <= src_col <= nfeatures_base) || return nothing
        @inbounds copyto!(data, (i - 1) * n + 1, X_base.data, (src_col - 1) * n + 1, n)
    end
    for m in 1:k
        eval_context === nothing || reset_index!(eval_context.buffer)
        pred, ok = eval_tree_array(hoisted_nodes[m], X_base, ops; eval_context)
        ok || return nothing
        @inbounds copyto!(data, (m_orig + m - 1) * n + 1, pred, 1, n)
    end

    opt_refs = Vector{Base.RefValue{N}}()
    opt_node = _build_hoisted_node(raw_tree, orig_features, hoisted_nodes, m_orig, opt_refs)
    length(opt_refs) == n_params || return nothing
    X_hoisted = FeatureMajorMatrix{T}(data)
    opt_dataset = with_eval_X(dataset, X_hoisted)
    opt_ex = with_contents(ex, opt_node)
    return (opt_ex, opt_refs, opt_dataset)
end
_try_hoist_for_optimization(_, _, _, _, _) = nothing

function _optimize_constants(
    dataset, member::P, x0, refs, options, algorithm, optimizer_options, rng
)::Tuple{P,Float64} where {T,L,N,P<:AbstractPopMember{T,L,N}}
    tree = member.tree
    eval_context = if options.autodiff_backend === nothing
        create_eval_context(dataset, options, 0)
    else
        nothing
    end
    hoisted = _try_hoist_for_optimization(
        tree, dataset, options, eval_context, length(x0)
    )
    if hoisted !== nothing
        opt_tree, opt_refs, opt_dataset = hoisted
        ctx = EvaluatorContext(opt_dataset, options, eval_context)
        f = Evaluator(opt_tree, opt_refs, ctx)
        fg! = GradEvaluator(f, options.autodiff_backend)
        return _optimize_constants_inner(
            f, fg!, x0, refs, dataset, member, options, algorithm, optimizer_options, rng
        )
    end
    ctx = EvaluatorContext(dataset, options, eval_context)
    f = Evaluator(tree, refs, ctx)
    fg! = GradEvaluator(f, options.autodiff_backend)
    return _optimize_constants_inner(
        f, fg!, x0, refs, dataset, member, options, algorithm, optimizer_options, rng
    )
end
function _optimize_constants(
    dataset, member::P, options, algorithm, optimizer_options, rng
)::Tuple{P,Float64} where {T,L,N,P<:AbstractPopMember{T,L,N}}
    x0, refs = get_optimizable_parameters(member.tree, options)
    return _optimize_constants(
        dataset, member, x0, refs, options, algorithm, optimizer_options, rng
    )
end
function _optimize_constants_inner(
    f::F, fg!::G, x0, refs, dataset, member::P, options, algorithm, optimizer_options, rng
)::Tuple{P,Float64} where {F,G,T,L,N,P<:AbstractPopMember{T,L,N}}
    obj = if algorithm isa Optim.Newton || options.autodiff_backend === nothing
        f
    else
        NLSolversBase.only_fg!(fg!)
    end
    baseline = f(x0)
    result = Optim.optimize(obj, x0, algorithm, optimizer_options)
    eval_fraction = dataset_fraction(dataset)
    num_evals = result.f_calls * eval_fraction
    # Try other initial conditions:
    for _ in 1:(options.optimizer_nrestarts)
        xt = let
            ET = eltype(x0)
            eps = randn(rng, ET, size(x0)...)
            @. ifelse(iszero(x0), eps, x0 * (ET(1) + ET(1 // 2) * eps))
        end
        tmpresult = Optim.optimize(obj, xt, algorithm, optimizer_options)
        num_evals += tmpresult.f_calls * eval_fraction
        # TODO: Does this need to take into account h_calls?

        if tmpresult.minimum < result.minimum
            result = tmpresult
        end
    end

    if result.minimum < baseline
        set_optimizable_parameters!(member.tree, result.minimizer, refs)
        member.loss = f(result.minimizer; regularization=true)
        member.cost = loss_to_cost(
            member.loss, dataset.use_baseline, dataset.baseline_loss, member, options
        )
        member.birth = get_birth_order(; deterministic=options.deterministic)
        num_evals += eval_fraction
    else
        # Reset to original state
        set_optimizable_parameters!(member.tree, x0, refs)
    end

    return member, num_evals
end

struct EvaluatorContext{D<:Dataset,O<:AbstractOptions,E} <: Function
    dataset::D
    options::O
    eval_context::E
end
function (c::EvaluatorContext)(tree; regularization=false)
    return eval_loss(
        tree, c.dataset, c.options; regularization, eval_context=c.eval_context
    )
end

struct Evaluator{N<:AbstractExpression,R,C<:EvaluatorContext} <: Function
    tree::N
    refs::R
    ctx::C
end
function (e::Evaluator)(x::AbstractVector; regularization=false)
    set_optimizable_parameters!(e.tree, x, e.refs)
    return e.ctx(e.tree; regularization)
end

struct GradEvaluator{E<:Evaluator,AD<:Union{Nothing,AbstractADType},PR,EX} <: Function
    e::E
    prep::PR
    backend::AD
    extra::EX
end
@unstable function GradEvaluator(e::Evaluator, backend)
    prep = isnothing(backend) ? nothing : _cached_prep(e.ctx, backend, e.tree)
    return GradEvaluator(e, prep, backend, nothing)
end

const CachedPrep = PerTaskCache{Dict{UInt,Any}}()

@unstable function _cached_prep(ctx, backend, example_tree)
    # We avoid hashing on the tree _value_ because it should not
    # affect the prep. We want to cache as much as possible!
    key = hash((ctx, backend, typeof(example_tree)))
    stable_get!(CachedPrep[], key) do
        prepare_gradient(ctx, backend, example_tree)
    end
end

function (g::GradEvaluator{<:Any,AD})(_, G, x::AbstractVector) where {AD}
    AD isa AutoEnzyme && error("Please load the `Enzyme.jl` package.")
    set_optimizable_parameters!(g.e.tree, x, g.e.refs)
    maybe_prep = isnothing(g.prep) ? () : (g.prep,)
    (val, grad) = value_and_gradient(g.e.ctx, maybe_prep..., g.backend, g.e.tree)
    if G !== nothing && grad !== nothing
        extracted_gradient = extract_optimizable_gradient(grad, g.e.tree, g.e.refs)
        length(extracted_gradient) == length(G) || throw(
            DimensionMismatch(
                "extracted $(length(extracted_gradient)) parameter gradients for " *
                "an optimization vector of length $(length(G))",
            ),
        )
        G .= extracted_gradient
    end
    return val
end

end
