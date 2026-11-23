module SymbolicRegressionEnzymeExt

using SymbolicRegression.LossFunctionsModule: eval_loss
using SymbolicRegression.ConstantOptimizationModule:
    get_optimizable_parameters, set_optimizable_parameters!
using SymbolicRegression.ComposableExpressionModule: ComposableExpression
using SymbolicRegression.TemplateExpressionModule:
    TemplateExpression, TemplateOptimizableRefs
using DynamicExpressions: Expression, get_scalar_constants
using ADTypes: AutoEnzyme
using Enzyme: autodiff, Reverse, Active, Const, Duplicated, make_zero, remake_zero!

import SymbolicRegression.ConstantOptimizationModule:
    Evaluator, GradEvaluator, extract_optimizable_gradient

function extract_optimizable_gradient(grad::Expression, ::Expression, _refs)
    return first(get_scalar_constants(grad))
end
function extract_optimizable_gradient(
    grad::ComposableExpression, ::ComposableExpression, _refs
)
    return first(get_scalar_constants(grad))
end
function extract_optimizable_gradient(
    grad::TemplateExpression, ::TemplateExpression, _refs::TemplateOptimizableRefs
)
    return first(get_scalar_constants(grad))
end

# We prepare a copy of the tree and all arrays
function GradEvaluator(f::F, backend::AE) where {F<:Evaluator,AE<:AutoEnzyme}
    storage_tree = make_zero(f.tree)
    storage_dataset = make_zero(f.ctx.dataset)
    storage_options = make_zero(f.ctx.options)
    # TODO: It is super inefficient to deepcopy; how can we skip this
    return GradEvaluator(
        f, nothing, backend, (; storage_tree, storage_dataset, storage_options)
    )
end

function evaluator(tree, dataset, options, output)
    output[] = eval_loss(tree, dataset, options; regularization=false)
    return nothing
end

with_stacksize(f::F, n) where {F} = fetch(schedule(Task(f, n)))

function (g::GradEvaluator{<:Any,<:AutoEnzyme})(_, G, x::AbstractVector{T}) where {T}
    set_optimizable_parameters!(g.e.tree, x, g.e.refs)
    remake_zero!(g.extra.storage_tree)
    remake_zero!(g.extra.storage_dataset)
    remake_zero!(g.extra.storage_options)

    output = [zero(T)]
    doutput = [one(T)]

    with_stacksize(32 * 1024 * 1024) do
        autodiff(
            Reverse,
            evaluator,
            Duplicated(g.e.tree, g.extra.storage_tree),
            Duplicated(g.e.ctx.dataset, g.extra.storage_dataset),
            Duplicated(g.e.ctx.options, g.extra.storage_options),
            Duplicated(output, doutput),
        )
    end

    if G !== nothing
        extracted_gradient = extract_optimizable_gradient(
            g.extra.storage_tree, g.e.tree, g.e.refs
        )
        if length(extracted_gradient) != length(G)
            throw(
                DimensionMismatch(
                    "extracted $(length(extracted_gradient)) parameter gradients for " *
                    "an optimization vector of length $(length(G))",
                ),
            )
        end
        G .= extracted_gradient
    end
    return output[]
end

end
