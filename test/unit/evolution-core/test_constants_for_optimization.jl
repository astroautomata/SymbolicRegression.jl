@testitem "Generic optimizable hooks aggregate constants and template parameters" begin
    using DynamicExpressions
    using SymbolicRegression

    operators = OperatorEnum(; unary_operators=(), binary_operators=(+, *))
    variable_names = ["x1"]
    options = Options(; operators)

    expr = parse_expression("x1 + 2.0"; operators, variable_names)
    flat = SymbolicRegression.get_optimizable_parameters(expr, options)[1]
    @test flat == [2.0]
    @test length(flat) == 1
    @test SymbolicRegression.count_optimizable_parameters(expr, options) == 1

    structure = TemplateStructure{(:f,),(:p,)}(
        ((; f), (; p), (x,)) -> f(x) * p[1]; num_parameters=(; p=1)
    )
    template = TemplateExpression(
        (; f=ComposableExpression(Node{Float64}(; val=3.0); operators, variable_names));
        structure,
        operators,
        variable_names,
        parameters=(; p=[2.0]),
    )

    params, refs = SymbolicRegression.get_optimizable_parameters(template, options)
    @test params == [3.0, 2.0]
    @test length(params) == 2
    @test SymbolicRegression.count_optimizable_parameters(template, options) == 2

    SymbolicRegression.set_optimizable_parameters!(template, [4.0, 5.0], refs)
    @test SymbolicRegression.get_optimizable_parameters(template, options)[1] == [4.0, 5.0]
end

@testitem "Generic optimizable hooks are options- and refs-aware" begin
    using SymbolicRegression

    mutable struct OptimizableBox{T}
        values::Vector{T}
    end
    struct OptimizableBoxRefs
        indices::Vector{Int}
    end

    function SymbolicRegression.count_optimizable_parameters(box::OptimizableBox, options)
        return count(options.active)
    end
    function SymbolicRegression.get_optimizable_parameters(box::OptimizableBox, options)
        refs = OptimizableBoxRefs(findall(options.active))
        return box.values[refs.indices], refs
    end
    function SymbolicRegression.set_optimizable_parameters!(
        box::OptimizableBox, x, refs::OptimizableBoxRefs
    )
        box.values[refs.indices] = x
        return box
    end
    function SymbolicRegression.extract_optimizable_gradient(
        grad, ::OptimizableBox, refs::OptimizableBoxRefs
    )
        return grad[refs.indices]
    end

    box = OptimizableBox([1.0, 2.0, 3.0])
    options = (; active=Bool[true, false, true])
    params, refs = SymbolicRegression.get_optimizable_parameters(box, options)

    @test SymbolicRegression.count_optimizable_parameters(box, options) == 2
    @test params == [1.0, 3.0]
    @test refs.indices == [1, 3]
    @test SymbolicRegression.extract_optimizable_gradient([0.1, 0.2, 0.3], box, refs) ==
        [0.1, 0.3]

    SymbolicRegression.set_optimizable_parameters!(box, [4.0, 5.0], refs)
    @test box.values == [4.0, 2.0, 5.0]
end

@testitem "Default optimize_constants handles custom optimizable expression state" begin
    using DynamicExpressions:
        DynamicExpressions,
        AbstractExpressionNode,
        AbstractOperatorEnum,
        EvalOptions,
        Metadata,
        Node,
        NodeTangent,
        OperatorEnum,
        get_contents,
        get_metadata,
        get_scalar_constants,
        set_scalar_constants!,
        extract_gradient
    using Optim: Optim
    using SymbolicRegression
    using SymbolicRegression: AbstractComposableExpression

    mutable struct WrappedExpression{T,N<:AbstractExpressionNode{T},D} <:
                   AbstractComposableExpression{T,N}
        tree::N
        metadata::Metadata{D}
    end

    function WrappedExpression(
        tree::AbstractExpressionNode{T};
        operators::Union{AbstractOperatorEnum,Nothing}=nothing,
        variable_names::Union{AbstractVector{<:AbstractString},Nothing}=nothing,
        eval_options::Union{EvalOptions,Nothing}=nothing,
        scale::T=one(T),
    ) where {T}
        return WrappedExpression(
            tree, Metadata((; operators, variable_names, eval_options, scale))
        )
    end

    DynamicExpressions.constructorof(::Type{<:WrappedExpression}) = WrappedExpression

    struct WrappedGradient{G,D}
        tree::G
        metadata::Metadata{D}
    end

    DynamicExpressions.get_contents(grad::WrappedGradient) = grad.tree
    DynamicExpressions.get_metadata(grad::WrappedGradient) = grad.metadata

    function SymbolicRegression.get_constants_for_optimization(
        ex::WrappedExpression{T}
    ) where {T}
        tree_params, tree_refs = get_scalar_constants(get_contents(ex))
        return vcat(tree_params, T[get_metadata(ex).scale]),
        (; tree_refs, n_tree=length(tree_params))
    end

    function SymbolicRegression.set_constants_for_optimization!(
        ex::WrappedExpression{T}, x, refs
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

    function SymbolicRegression.extract_gradient_for_optimization(
        grad, ex::WrappedExpression{T}
    ) where {T}
        tree_grad = extract_gradient(get_contents(grad), get_contents(ex))
        return vcat(tree_grad, T[get_metadata(grad).scale])
    end

    operators = OperatorEnum(; unary_operators=(), binary_operators=(+,))
    wrapped = WrappedExpression(
        Node{Float64}(; val=1.0);
        operators,
        variable_names=["x1"],
        eval_options=nothing,
        scale=-1.0,
    )

    initial_params, _ = SymbolicRegression.get_constants_for_optimization(wrapped)
    @test initial_params == [1.0, -1.0]

    gradient = WrappedGradient(
        NodeTangent(get_contents(wrapped), [-0.5]), Metadata((; scale=0.75))
    )
    @test SymbolicRegression.extract_gradient_for_optimization(gradient, wrapped) ==
        [-0.5, 0.75]

    function loss(
        ex::WrappedExpression{Float64}, _dataset::Dataset{Float64,Float64}, _options
    )
        c = get_contents(ex).val
        s = get_metadata(ex).scale
        return (c - 2.0)^2 + (s - 3.0)^2
    end

    dataset = Dataset(zeros(Float64, 1, 4), zeros(Float64, 4))
    options = Options(;
        binary_operators=(+,),
        unary_operators=(),
        deterministic=true,
        optimizer_nrestarts=0,
        autodiff_backend=nothing,
        optimizer_algorithm=Optim.BFGS(),
        optimizer_options=Optim.Options(; iterations=100),
        loss_function_expression=loss,
        parsimony=0.0,
    )

    generic_params, generic_refs = SymbolicRegression.get_optimizable_parameters(
        wrapped, options
    )
    @test generic_params == initial_params
    @test SymbolicRegression.extract_optimizable_gradient(
        gradient, wrapped, generic_refs
    ) == [-0.5, 0.75]
    SymbolicRegression.set_optimizable_parameters!(wrapped, [1.5, -0.5], generic_refs)
    @test SymbolicRegression.get_constants_for_optimization(wrapped)[1] == [1.5, -0.5]
    SymbolicRegression.set_optimizable_parameters!(wrapped, initial_params, generic_refs)

    initial_loss = loss(wrapped, dataset, options)
    member = PopMember(wrapped, initial_loss, initial_loss, options, 1; deterministic=true)

    new_member, _ = SymbolicRegression.optimize_constants(dataset, member, options)
    final_loss = loss(new_member.tree, dataset, options)
    final_params = SymbolicRegression.get_constants_for_optimization(new_member.tree)[1]

    @test final_loss < initial_loss
    @test final_params != initial_params
    @test get_contents(new_member.tree).val ≈ 2.0 atol = 1e-4
    @test get_metadata(new_member.tree).scale ≈ 3.0 atol = 1e-4
end
