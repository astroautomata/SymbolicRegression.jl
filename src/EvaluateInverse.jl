module EvaluateInverseModule

using DynamicExpressions:
    OperatorEnum, AbstractExpressionNode, eval_tree_array, get_child, preserve_sharing

using ..InverseFunctionsModule: approx_inverse

# Helper struct for returning results
struct ResultOk{T}
    x::T
    ok::Bool
end

is_bad_array(x) = any(isnan, x) || any(isinf, x)

"""
Inverse the tree evaluation at some `node_to_invert_at` in the `tree`,
given some output of the `tree`, `y` and feature values `X`.

For example, inverting `y = cos(x) * 2.1` with `x` as
`node_to_invert_at` would return an evaluation of the
tree `acos(y / 2.1)`.

!!! warning
    This API supports an experimental mutation and will change in minor version
    increments.
"""
function eval_inverse_tree_array(
    tree::N,
    X::AbstractMatrix{T},
    operators::OperatorEnum,
    node_to_invert_at::N,
    y::AbstractVector{T};
    eval_kws...,
) where {T,N<:AbstractExpressionNode{T,2}}
    if preserve_sharing(tree)
        throw(
            ArgumentError(
                "eval_inverse_tree_array does not currently support shared-node expressions.",
            ),
        )
    end
    result = _eval_inverse_tree_array(
        tree, X, operators, node_to_invert_at, copy(y), (; eval_kws...)
    )
    return (result.x, result.ok && !is_bad_array(result.x))
end

function eval_inverse_tree_array(
    tree::N,
    X::AbstractMatrix{T},
    operators::OperatorEnum,
    node_to_invert_at::N,
    y::AbstractVector{T};
    eval_kws...,
) where {T,D,N<:AbstractExpressionNode{T,D}}
    throw(
        ArgumentError(
            "eval_inverse_tree_array only supports AbstractExpressionNode{T,2}; got $(N)."
        ),
    )
end

@generated function _eval_inverse_tree_array(
    tree::N,
    X::AbstractMatrix{T},
    operators::O,
    node_to_invert_at::N,
    y::AbstractVector{T},
    eval_kws::NamedTuple,
)::ResultOk where {T,N<:AbstractExpressionNode{T,2},O<:OperatorEnum}
    op_type = O.parameters[1]  # Tuple{Tuple{unary...}, Tuple{binary...}}
    nuna = length(op_type.parameters[1].parameters)
    nbin = length(op_type.parameters[2].parameters)
    quote
        tree === node_to_invert_at && return ResultOk(y, true)

        tree.degree == 0 && return ResultOk(y, false)

        if tree.degree == 1 && $nuna > 0
            op_idx = tree.op
            Base.Cartesian.@nif(
                $nuna,
                i -> i == op_idx,
                i -> let op = operators.unaops[i]
                    return dispatch_deg1(
                        tree, X, op, operators, node_to_invert_at, y, eval_kws
                    )
                end
            )
        elseif tree.degree == 2 && $nbin > 0
            op_idx = tree.op
            Base.Cartesian.@nif(
                $nbin,
                i -> i == op_idx,
                i -> let op = operators.binops[i]
                    return dispatch_deg2(
                        tree, X, op, operators, node_to_invert_at, y, eval_kws
                    )
                end
            )
        else
            throw(
                ArgumentError(
                    "eval_inverse_tree_array cannot invert node degree $(tree.degree) with the configured operators.",
                ),
            )
        end
    end
end

function dispatch_deg1(
    tree::N,
    X::AbstractMatrix{T},
    op::F,
    operators::OperatorEnum,
    node_to_invert_at::N,
    y::AbstractVector{T},
    eval_kws::NamedTuple,
) where {F,T,N<:AbstractExpressionNode{T,2}}
    complete_inv = deg1_invert!(y, op)
    (!complete_inv || is_bad_array(y)) && return ResultOk(y, false)
    return _eval_inverse_tree_array(
        get_child(tree, 1), X, operators, node_to_invert_at, y, eval_kws
    )
end

function dispatch_deg2(
    tree::N,
    X::AbstractMatrix{T},
    op::F,
    operators::OperatorEnum,
    node_to_invert_at::N,
    y::AbstractVector{T},
    eval_kws::NamedTuple,
) where {F,T,N<:AbstractExpressionNode{T,2}}
    left_child = get_child(tree, 1)
    right_child = get_child(tree, 2)

    if any(Base.Fix1(===, node_to_invert_at), right_child)
        (result_l, complete_l) = eval_tree_array(left_child, X, operators; eval_kws...)
        !complete_l && return ResultOk(result_l, complete_l)
        complete_inv_r = deg2_invert_right!(y, result_l, op)
        (!complete_inv_r || is_bad_array(y)) && return ResultOk(y, false)
        return _eval_inverse_tree_array(
            right_child, X, operators, node_to_invert_at, y, eval_kws
        )
    else  # any(===(node_to_invert_at), left_child)
        (result_r, complete_r) = eval_tree_array(right_child, X, operators; eval_kws...)
        !complete_r && return ResultOk(result_r, complete_r)
        complete_inv_l = deg2_invert_left!(y, result_r, op)
        (!complete_inv_l || is_bad_array(y)) && return ResultOk(y, false)
        return _eval_inverse_tree_array(
            left_child, X, operators, node_to_invert_at, y, eval_kws
        )
    end
end

function deg1_invert!(y::AbstractVector, op::F) where {F}
    op_inv = approx_inverse(op)
    op_inv === nothing && return false
    @inbounds @simd for i in eachindex(y)
        y[i] = op_inv(y[i])
    end
    return true
end

function deg2_invert_right!(y::AbstractVector, l::AbstractVector, op::F) where {F}
    @inbounds for i in eachindex(y, l)
        op_inv = approx_inverse(Base.Fix1(op, l[i]))
        op_inv === nothing && return false
        y[i] = op_inv(y[i])
    end
    return true
end

function deg2_invert_left!(y::AbstractVector, r::AbstractVector, op::F) where {F}
    @inbounds for i in eachindex(y, r)
        op_inv = approx_inverse(Base.Fix2(op, r[i]))
        op_inv === nothing && return false
        y[i] = op_inv(y[i])
    end
    return true
end

end
