@testitem "TemplateExpressionSpec supports custom inner expression types" begin
    using DynamicExpressions: DynamicExpressions, AbstractExpressionNode, AbstractOperatorEnum, EvalOptions, Metadata, Node, OperatorEnum, get_contents, get_metadata
    using SymbolicRegression
    using SymbolicRegression.ComposableExpressionModule: AbstractComposableExpression
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
        return WrappedExpression(tree, Metadata((; operators, variable_names, eval_options, tag)))
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
