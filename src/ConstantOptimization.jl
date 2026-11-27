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
    EvalContext,
    ArrayBuffer,
    ResultOk,
    get_tree,
    get_child,
    get_operators,
    preserve_sharing,
    is_valid_array,
    get_scalar_constants,
    set_scalar_constants!,
    extract_gradient
using DynamicExpressions.NodeUtilsModule: is_constant
using DynamicExpressions.EvaluateModule:
    _eval_tree_array, apply_op_array, reset_index!, get_array
using DispatchDoctor: @unstable
using ..CoreModule:
    AbstractOptions, Dataset, DATA_TYPE, LOSS_TYPE, specialized_options, dataset_fraction
using ..CoreModule.DatasetModule: has_units
using ..UtilsModule: get_birth_order, PerTaskCache, stable_get!
using ..LossFunctionsModule:
    create_eval_context, eval_loss, loss_to_cost, _loss, _weighted_loss
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
    opt_options =
        options.autodiff_backend === nothing ? options : specialized_options(options)
    if nconst == 1 && !(T <: Complex)
        algorithm = Optim.Newton(; linesearch=LineSearches.BackTracking())
        return _optimize_constants(
            dataset,
            member,
            x0,
            refs,
            opt_options,
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
        opt_options,
        options.optimizer_algorithm,
        options.optimizer_options,
        rng,
    )
end

struct MemoNode{T,NT<:AbstractExpressionNode{T}}
    node::NT
    mask::UInt64
    slot::Int
    has_slots::Bool
    children::Vector{MemoNode{T,NT}}
end

mutable struct MemoPlan{T,L,NT<:AbstractExpressionNode{T},OP,CX,EC,AY,AW,LF}
    const tree::MemoNode{T,NT}
    const nconst::Int
    const cache_vecs::Vector{Vector{T}}
    const base_x::Vector{T}
    const operators::OP
    const cX::CX
    const eval_context::EC
    const y::AY
    const weights::AW
    const loss_fn::LF
    base_loss::L
    base_valid::Bool
end

function _build_memo_masks(
    node::NT, const_idx::Base.RefValue{Int}
)::MemoNode{T,NT} where {T,NT<:AbstractExpressionNode{T}}
    deg = node.degree
    if deg == 0
        if node.constant
            idx = const_idx[]
            const_idx[] = idx + 1
            return MemoNode{T,NT}(node, UInt64(1) << (idx - 1), 0, false, MemoNode{T,NT}[])
        else
            return MemoNode{T,NT}(node, UInt64(0), 0, false, MemoNode{T,NT}[])
        end
    end
    # Keep constant-only subtrees intact so Evaluate.jl evaluates them in scalar.
    if is_constant(node)
        m = UInt64(0)
        m = _consume_const_mask!(node, const_idx)
        return MemoNode{T,NT}(node, m, 0, false, MemoNode{T,NT}[])
    end
    children = Vector{MemoNode{T,NT}}(undef, deg)
    m = UInt64(0)
    for i in 1:deg
        ch = _build_memo_masks(get_child(node, i), const_idx)
        children[i] = ch
        m |= ch.mask
    end
    return MemoNode{T,NT}(node, m, 0, false, children)
end

function _consume_const_mask!(
    node::AbstractExpressionNode, const_idx::Base.RefValue{Int}
)::UInt64
    deg = node.degree
    if deg == 0
        if node.constant
            idx = const_idx[]
            const_idx[] = idx + 1
            return UInt64(1) << (idx - 1)
        end
        return UInt64(0)
    end
    m = UInt64(0)
    for i in 1:deg
        m |= _consume_const_mask!(get_child(node, i), const_idx)
    end
    return m
end

function _assign_memo_slots(
    mnode::MemoNode{T,NT}, parent_mask::UInt64, cache_vecs::Vector{Vector{T}}, n::Int
)::MemoNode{T,NT} where {T,NT<:AbstractExpressionNode{T}}
    slot =
        if mnode.node.degree > 0 &&
            !isempty(mnode.children) &&
            mnode.mask != UInt64(0) &&
            mnode.mask != parent_mask
            push!(cache_vecs, Vector{T}(undef, n))
            length(cache_vecs)
        else
            0
        end
    if isempty(mnode.children)
        return MemoNode{T,NT}(mnode.node, mnode.mask, slot, false, mnode.children)
    end
    new_children = Vector{MemoNode{T,NT}}(undef, length(mnode.children))
    has_child_slots = false
    for i in eachindex(mnode.children)
        nc = _assign_memo_slots(mnode.children[i], mnode.mask, cache_vecs, n)
        new_children[i] = nc
        has_child_slots |= (nc.slot > 0 || nc.has_slots)
    end
    return MemoNode{T,NT}(mnode.node, mnode.mask, slot, has_child_slots, new_children)
end

@unstable function _build_memo_plan(
    ex::Expression{T,NT},
    dataset::Dataset{T,L},
    options::AbstractOptions,
    nconst::Int,
    eval_context,
) where {
    T<:Union{AbstractFloat,Complex{<:AbstractFloat}},
    L<:LOSS_TYPE,
    NT<:AbstractExpressionNode{T},
}
    (2 <= nconst <= 64) || return nothing
    preserve_sharing(NT) && return nothing
    ops = get_operators(ex, options)
    ops isa OperatorEnum || return nothing
    options.autodiff_backend === nothing || return nothing
    options.turbo isa Val{false} || return nothing
    has_units(dataset) && return nothing
    isnothing(options.loss_function) || return nothing
    isnothing(options.loss_function_expression) || return nothing
    eval_context isa EvalContext{false,<:Any,true,<:ArrayBuffer{Vector{Vector{T}}}} ||
        return nothing
    cX = dataset.X
    cX isa Union{Matrix{T},SubArray{T,2,Matrix{T}}} || return nothing
    dataset.n >= 512 || return nothing

    raw_tree = get_tree(ex)
    const_idx = Ref(1)
    masked = _build_memo_masks(raw_tree, const_idx)
    (const_idx[] - 1 == nconst) || return nothing
    cache_vecs = Vector{Vector{T}}()
    slotted = _assign_memo_slots(masked, masked.mask, cache_vecs, dataset.n)
    isempty(cache_vecs) && return nothing
    cX = dataset.X
    y = dataset.y::AbstractArray
    w = dataset.weights
    lf = options.elementwise_loss
    return MemoPlan{
        T,L,NT,typeof(ops),typeof(cX),typeof(eval_context),typeof(y),typeof(w),typeof(lf)
    }(
        slotted,
        nconst,
        cache_vecs,
        Vector{T}(undef, nconst),
        ops,
        cX,
        eval_context,
        y,
        w,
        lf,
        L(Inf),
        false,
    )
end
_build_memo_plan(_, _, _, _, _) = nothing

@inline function _check_memo_ok(
    res::ResultOk{Vector{T}}, eval_context::EvalContext
)::ResultOk{Vector{T}} where {T}
    if !res.ok
        return res
    end
    if eval_context.early_exit isa Val{true} && !is_valid_array(res.x)
        return ResultOk(res.x, false)
    end
    return res
end

function _eval_memo_record(
    mnode::MemoNode{T,NT},
    cache_vecs::Vector{Vector{T}},
    cX::AbstractMatrix{T},
    operators,
    eval_context::EvalContext,
)::ResultOk{Vector{T}} where {T,NT}
    res = if !mnode.has_slots
        _check_memo_ok(
            _eval_tree_array(mnode.node, cX, operators, eval_context)::ResultOk{Vector{T}},
            eval_context,
        )
    else
        deg = mnode.node.degree
        raw = if deg == 1
            r1 = _eval_memo_record(mnode.children[1], cache_vecs, cX, operators, eval_context)
            r1.ok || return r1
            apply_op_array(
                (r1.x,), mnode.node.op, operators, eval_context
            )::ResultOk{Vector{T}}
        elseif deg == 2
            r1 = _eval_memo_record(mnode.children[1], cache_vecs, cX, operators, eval_context)
            r1.ok || return r1
            r2 = _eval_memo_record(
                mnode.children[2], cache_vecs, cX, operators, eval_context
            )
            r2.ok || return r2
            apply_op_array(
                (r1.x, r2.x), mnode.node.op, operators, eval_context
            )::ResultOk{Vector{T}}
        else
            rs = ntuple(
                i -> _eval_memo_record(
                    mnode.children[i], cache_vecs, cX, operators, eval_context
                ),
                deg,
            )
            for r in rs
                r.ok || return r
            end
            xs = map(r -> r.x, rs)
            apply_op_array(xs, mnode.node.op, operators, eval_context)::ResultOk{Vector{T}}
        end
        _check_memo_ok(raw, eval_context)
    end
    if mnode.slot > 0 && res.ok
        @inbounds copyto!(cache_vecs[mnode.slot], res.x)
    end
    return res
end

function _eval_memo_read(
    mnode::MemoNode{T,NT},
    diff_mask::UInt64,
    cache_vecs::Vector{Vector{T}},
    cX::AbstractMatrix{T},
    operators,
    eval_context::EvalContext,
)::ResultOk{Vector{T}} where {T,NT}
    if (mnode.mask & diff_mask) == UInt64(0)
        if mnode.slot > 0
            out = get_array(eval_context.buffer, cX, axes(cX, 2))::Vector{T}
            @inbounds copyto!(out, cache_vecs[mnode.slot])
            return ResultOk(out, true)
        end
        return _check_memo_ok(
            _eval_tree_array(mnode.node, cX, operators, eval_context)::ResultOk{Vector{T}},
            eval_context,
        )
    end
    if !mnode.has_slots
        return _check_memo_ok(
            _eval_tree_array(mnode.node, cX, operators, eval_context)::ResultOk{Vector{T}},
            eval_context,
        )
    end
    deg = mnode.node.degree
    raw = if deg == 1
        r1 = _eval_memo_read(
            mnode.children[1], diff_mask, cache_vecs, cX, operators, eval_context
        )
        r1.ok || return r1
        apply_op_array((r1.x,), mnode.node.op, operators, eval_context)::ResultOk{Vector{T}}
    elseif deg == 2
        r1 = _eval_memo_read(
            mnode.children[1], diff_mask, cache_vecs, cX, operators, eval_context
        )
        r1.ok || return r1
        r2 = _eval_memo_read(
            mnode.children[2], diff_mask, cache_vecs, cX, operators, eval_context
        )
        r2.ok || return r2
        apply_op_array(
            (r1.x, r2.x), mnode.node.op, operators, eval_context
        )::ResultOk{Vector{T}}
    else
        rs = ntuple(
            i -> _eval_memo_read(
                mnode.children[i],
                diff_mask,
                cache_vecs,
                cX,
                operators,
                eval_context,
            ),
            deg,
        )
        for r in rs
            r.ok || return r
        end
        xs = map(r -> r.x, rs)
        apply_op_array(xs, mnode.node.op, operators, eval_context)::ResultOk{Vector{T}}
    end
    return _check_memo_ok(raw, eval_context)
end

function _eval_with_memo(
    memo::MemoPlan{T,L,NT,OP,CX,EC,AY,AW,LF},
    tree::Expression{T,NT},
    refs,
    x::AbstractVector,
)::L where {T,L,NT,OP,CX,EC,AY,AW,LF}
    diff_mask = UInt64(0)
    if memo.base_valid
        @inbounds for i in 1:(memo.nconst)
            if convert(T, x[i]) !== memo.base_x[i]
                diff_mask |= (UInt64(1) << (i - 1))
            end
        end
        if diff_mask == UInt64(0)
            set_optimizable_parameters!(tree, x, refs)
            return memo.base_loss
        end
    end

    set_optimizable_parameters!(tree, x, refs)
    eval_context = memo.eval_context
    reset_index!(eval_context.buffer)
    cX = memo.cX
    ops = memo.operators

    if memo.base_valid && count_ones(diff_mask) == 1
        res = _eval_memo_read(memo.tree, diff_mask, memo.cache_vecs, cX, ops, eval_context)
        res.ok || return L(Inf)
        return if memo.weights !== nothing
            _weighted_loss(res.x, memo.y, memo.weights, memo.loss_fn)
        else
            _loss(res.x, memo.y, memo.loss_fn)
        end
    end

    res = _eval_memo_record(memo.tree, memo.cache_vecs, cX, ops, eval_context)
    if !res.ok
        memo.base_valid = false
        return L(Inf)
    end
    loss_val = if memo.weights !== nothing
        _weighted_loss(res.x, memo.y, memo.weights, memo.loss_fn)
    else
        _loss(res.x, memo.y, memo.loss_fn)
    end
    @inbounds for i in 1:(memo.nconst)
        memo.base_x[i] = convert(T, x[i])
    end
    memo.base_loss = loss_val
    memo.base_valid = true
    return loss_val
end

function _optimize_constants(
    dataset, member::P, x0, refs, options, algorithm, optimizer_options, rng
)::Tuple{P,Float64} where {T,L,N,P<:AbstractPopMember{T,L,N}}
    tree = member.tree
    eval_context = if options.autodiff_backend === nothing
        create_eval_context(dataset, options, 0)
    else
        nothing
    end
    ctx = EvaluatorContext(dataset, options, eval_context)
    memo = _build_memo_plan(tree, dataset, options, length(x0), eval_context)
    f = Evaluator(tree, refs, ctx, memo)
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
    memo::Any
end
function Evaluator(tree::N, refs::R, ctx::C) where {N,R,C}
    Evaluator{N,R,C}(tree, refs, ctx, nothing)
end
function (e::Evaluator{N,R,EvaluatorContext{D,O,E}})(
    x::AbstractVector; regularization=false
)::L where {T,L,D<:Dataset{T,L},N,R,O,E}
    if !regularization && e.memo !== nothing && length(x) == e.memo.nconst
        return _eval_with_memo(e.memo, e.tree, e.refs, x)::L
    end
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
