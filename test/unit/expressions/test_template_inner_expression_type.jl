@testitem "TemplateExpressionSpec supports custom inner expression types" begin
    using DynamicExpressions:
        DynamicExpressions,
        AbstractExpressionNode,
        AbstractOperatorEnum,
        EvalOptions,
        Metadata,
        Node,
        OperatorEnum,
        get_contents,
        get_metadata
    using SymbolicRegression
    using SymbolicRegression: AbstractComposableExpression
    using SymbolicRegression.ExpressionBuilderModule: create_expression

    struct WrappedExpression{T,N<:AbstractExpressionNode{T},D} <:
           AbstractComposableExpression{T,N}
        tree::N
        metadata::Metadata{D}
    end

    function WrappedExpression(
        tree::AbstractExpressionNode{T};
        operators::Union{AbstractOperatorEnum,Nothing}=nothing,
        variable_names::Union{AbstractVector{<:AbstractString},Nothing}=nothing,
        eval_options::Union{EvalOptions,Nothing}=nothing,
        tag::Symbol=:wrapped,
    ) where {T}
        return WrappedExpression(
            tree, Metadata((; operators, variable_names, eval_options, tag))
        )
    end

    DynamicExpressions.constructorof(::Type{<:WrappedExpression}) = WrappedExpression

    operators = OperatorEnum(; unary_operators=(cos,), binary_operators=(+,))
    structure = TemplateStructure{(:f,)}(((; f), (x,)) -> f(x); num_features=(; f=1))
    spec = TemplateExpressionSpec(;
        structure,
        inner_expression_type=WrappedExpression,
        inner_expression_options=(; tag=:custom_inner),
    )

    parsed = parse_expression((; f="#1 + 1.0"); expression_spec=spec, operators)
    parsed_inner = first(values(get_contents(parsed)))
    @test parsed_inner isa WrappedExpression
    @test get_metadata(parsed_inner).tag == :custom_inner

    dataset = Dataset(randn(Float32, 1, 8), randn(Float32, 8))
    options = Options(; operators, expression_spec=spec, tournament_selection_n=5)
    created = create_expression(Node{Float32}(; val=0.0f0), options, dataset)
    created_inner = first(values(get_contents(created)))
    @test created_inner isa WrappedExpression
    @test get_metadata(created_inner).tag == :custom_inner
end

@testitem "TemplateExpressionSpec initializes template parameters" begin
    using Random: AbstractRNG
    using DynamicExpressions: Node, OperatorEnum, get_metadata
    using SymbolicRegression
    using SymbolicRegression: ParamVector
    using SymbolicRegression.ExpressionBuilderModule: create_expression, strip_metadata

    operators = OperatorEnum(; binary_operators=(+,))
    structure = TemplateStructure{(:f,),(:weights, :bias)}(
        ((; f), (; weights, bias), (x,)) -> f(x) + weights[1] + bias[1];
        num_features=(; f=1),
        num_parameters=(; weights=2, bias=1),
    )
    initializer_calls = Ref(0)
    parameter_initializer = function (rng, T, num_parameters)
        @test rng isa AbstractRNG
        @test T === Float32
        @test num_parameters == (; weights=2, bias=1)
        initializer_calls[] += 1
        return (; bias=T[-1], weights=T[2, 3])
    end
    spec = TemplateExpressionSpec(; structure, parameter_initializer)
    @test spec.parameter_initializer === parameter_initializer
    dataset = Dataset(randn(Float32, 1, 8), randn(Float32, 8))
    options = Options(; operators, expression_spec=spec, tournament_selection_n=5)

    created = create_expression(Node{Float32}(; val=0.0f0), options, dataset)
    created_parameters = get_metadata(created).parameters
    @test initializer_calls[] == 1
    @test created_parameters.weights isa ParamVector{Float32}
    @test created_parameters.bias isa ParamVector{Float32}
    @test collect(created_parameters.weights) == Float32[2, 3]
    @test collect(created_parameters.bias) == Float32[-1]

    copied = strip_metadata(created, options, dataset)
    copied_parameters = get_metadata(copied).parameters
    @test initializer_calls[] == 1
    @test copied_parameters == created_parameters
    @test copied_parameters.weights !== created_parameters.weights
    @test copied_parameters.bias !== created_parameters.bias

    default_spec = TemplateExpressionSpec(structure)
    @test default_spec.parameter_initializer === nothing
    default_options = Options(;
        operators, expression_spec=default_spec, tournament_selection_n=5
    )
    default_created = create_expression(
        Node{Float32}(; val=0.0f0), default_options, dataset
    )
    default_parameters = get_metadata(default_created).parameters
    @test default_parameters.weights isa ParamVector{Float32}
    @test default_parameters.bias isa ParamVector{Float32}
    @test length(default_parameters.weights) == 2
    @test length(default_parameters.bias) == 1
end

@testitem "TemplateExpressionSpec validates initialized template parameters" begin
    using DynamicExpressions: Node, OperatorEnum
    using SymbolicRegression
    using SymbolicRegression.ExpressionBuilderModule: create_expression

    operators = OperatorEnum(; binary_operators=(+,))
    structure = TemplateStructure{(:f,),(:weights, :bias)}(
        ((; f), (; weights, bias), (x,)) -> f(x) + weights[1] + bias[1];
        num_features=(; f=1),
        num_parameters=(; weights=2, bias=1),
    )
    dataset = Dataset(randn(Float32, 1, 8), randn(Float32, 8))

    wrong_keys = TemplateExpressionSpec(;
        structure, parameter_initializer=(_, T, _) -> (; weights=T[2, 3], offset=T[-1])
    )
    wrong_keys_options = Options(;
        operators, expression_spec=wrong_keys, tournament_selection_n=5
    )
    @test_throws ArgumentError create_expression(
        Node{Float32}(; val=0.0f0), wrong_keys_options, dataset
    )

    wrong_length = TemplateExpressionSpec(;
        structure, parameter_initializer=(_, T, _) -> (; weights=T[2], bias=T[-1])
    )
    wrong_length_options = Options(;
        operators, expression_spec=wrong_length, tournament_selection_n=5
    )
    @test_throws DimensionMismatch create_expression(
        Node{Float32}(; val=0.0f0), wrong_length_options, dataset
    )
end
