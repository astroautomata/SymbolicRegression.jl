@testitem "Enzyme GradEvaluator uses optimizable parameter hooks" begin
    using SymbolicRegression
    using DynamicExpressions: OperatorEnum, Node, Expression
    using Enzyme: Enzyme
    using DifferentiationInterface: AutoEnzyme
    using SymbolicRegression.ConstantOptimizationModule:
        Evaluator, EvaluatorContext, GradEvaluator

    operators = OperatorEnum(2 => (+, *))
    options = Options(; operators, autodiff_backend=:Enzyme)
    dataset = Dataset(reshape([1.0, 2.0], 1, :), [0.0, 0.0])

    ex_plain = Expression(Node{Float64}(; val=3.0) * Node{Float64}(; feature=1); operators)
    _, refs_plain = SymbolicRegression.get_optimizable_parameters(ex_plain, options)
    g_plain = GradEvaluator(
        Evaluator(ex_plain, refs_plain, EvaluatorContext(dataset, options, nothing)),
        AutoEnzyme(),
    )
    G_plain = zeros(1)
    @test g_plain(nothing, G_plain, [4.0]) ≈ 40.0
    @test G_plain ≈ [20.0]

    structure = TemplateStructure{(:f,),(:p,)}(
        ((; f), (; p), (x,)) -> f(x) * p[1]; num_parameters=(; p=1)
    )
    ex_template = TemplateExpression(
        (; f=ComposableExpression(Node{Float64}(; val=3.0); operators));
        structure,
        operators,
        parameters=(; p=[2.0]),
    )
    _, refs_template = SymbolicRegression.get_optimizable_parameters(ex_template, options)
    g_template = GradEvaluator(
        Evaluator(ex_template, refs_template, EvaluatorContext(dataset, options, nothing)),
        AutoEnzyme(),
    )
    G_template = zeros(2)
    @test g_template(nothing, G_template, [4.0, 5.0]) ≈ 400.0
    @test G_template ≈ [200.0, 160.0]

    struct EnzymeSubsetCombiner <: Function end
    (::EnzymeSubsetCombiner)(fs, params, (x,)) = fs.f(x) * params.p[1]
    struct EnzymeSubsetRefs{R}
        indices::Vector{Int}
        full::Vector{Float64}
        inner::R
    end
    function SymbolicRegression.get_optimizable_parameters(
        ::EnzymeSubsetCombiner, ex::TemplateExpression, opts
    )
        all_p, all_refs = invoke(
            SymbolicRegression.get_optimizable_parameters,
            Tuple{Any,TemplateExpression,Any},
            nothing,
            ex,
            opts,
        )
        indices = findall(>(2.5), all_p)
        return all_p[indices], EnzymeSubsetRefs(indices, copy(all_p), all_refs)
    end
    function SymbolicRegression.set_optimizable_parameters!(
        ex::TemplateExpression, x, refs::EnzymeSubsetRefs
    )
        full = copy(refs.full)
        full[refs.indices] .= x
        return SymbolicRegression.set_optimizable_parameters!(ex, full, refs.inner)
    end
    function SymbolicRegression.extract_optimizable_gradient(
        grad::TemplateExpression, ex::TemplateExpression, refs::EnzymeSubsetRefs
    )
        full_grad = SymbolicRegression.extract_optimizable_gradient(grad, ex, refs.inner)
        return full_grad[refs.indices]
    end

    st_subset = TemplateStructure{(:f,),(:p,)}(
        EnzymeSubsetCombiner(); num_features=(; f=1), num_parameters=(; p=1)
    )
    ex_subset = TemplateExpression(
        (; f=ComposableExpression(Node{Float64}(; val=3.0); operators));
        structure=st_subset,
        operators,
        parameters=(; p=[2.0]),
    )
    _, refs_subset = SymbolicRegression.get_optimizable_parameters(ex_subset, options)
    g_subset = GradEvaluator(
        Evaluator(ex_subset, refs_subset, EvaluatorContext(dataset, options, nothing)),
        AutoEnzyme(),
    )
    G_subset = zeros(1)
    @test g_subset(nothing, G_subset, [4.0]) ≈ 64.0
    @test G_subset ≈ [32.0]
end
