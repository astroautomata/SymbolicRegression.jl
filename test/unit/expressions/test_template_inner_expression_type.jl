@testitem "TemplateExpressionSpec supports custom inner expression types" begin
    using DynamicExpressions: DynamicExpressions, AbstractExpressionNode, AbstractOperatorEnum, EvalOptions, Metadata, Node, OperatorEnum, get_contents, get_metadata
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

@testitem "TemplateExpression candidate-local shared state hooks" begin
    using DynamicExpressions:
        DynamicExpressions,
        AbstractExpressionNode,
        AbstractOperatorEnum,
        EvalOptions,
        Metadata,
        Node,
        OperatorEnum,
        get_contents,
        get_metadata,
        with_metadata
    using SymbolicRegression
    using SymbolicRegression: AbstractComposableExpression
    using SymbolicRegression.ExpressionBuilderModule: create_expression

    mutable struct SharedTemplateState
        value::Float64
    end

    struct SharedExpression{T,N<:AbstractExpressionNode{T},D} <:
           AbstractComposableExpression{T,N}
        tree::N
        metadata::Metadata{D}
    end

    function SharedExpression(
        tree::AbstractExpressionNode{T};
        operators::Union{AbstractOperatorEnum,Nothing}=nothing,
        variable_names::Union{AbstractVector{<:AbstractString},Nothing}=nothing,
        eval_options::Union{EvalOptions,Nothing}=nothing,
        state::SharedTemplateState=SharedTemplateState(0.0),
    ) where {T}
        return SharedExpression(
            tree, Metadata((; operators, variable_names, eval_options, state))
        )
    end

    DynamicExpressions.constructorof(::Type{<:SharedExpression}) = SharedExpression

    function Base.copy(ex::SharedExpression)
        meta = get_metadata(ex)
        return SharedExpression(
            copy(get_contents(ex));
            operators=meta.operators,
            variable_names=meta.variable_names,
            eval_options=meta.eval_options,
            state=meta.state,
        )
    end

    function DynamicExpressions.with_metadata(ex::SharedExpression; kws...)
        meta = get_metadata(ex)
        state = haskey(kws, :state) ? kws[:state] : meta.state
        operators = haskey(kws, :operators) ? kws[:operators] : meta.operators
        variable_names = haskey(kws, :variable_names) ? kws[:variable_names] : meta.variable_names
        eval_options = haskey(kws, :eval_options) ? kws[:eval_options] : meta.eval_options
        return SharedExpression(
            get_contents(ex), Metadata((; operators, variable_names, eval_options, state))
        )
    end

    struct PreallocatedSharedExpression{N}
        tree::N
    end

    DynamicExpressions.allocate_container(
        ex::SharedExpression, n::Union{Nothing,Integer}=nothing
    ) = PreallocatedSharedExpression(DynamicExpressions.allocate_container(get_contents(ex), n))

    function DynamicExpressions.copy_into!(
        dest::PreallocatedSharedExpression, src::SharedExpression
    )
        meta = get_metadata(src)
        return SharedExpression(
            DynamicExpressions.copy_into!(dest.tree, get_contents(src));
            operators=meta.operators,
            variable_names=meta.variable_names,
            eval_options=meta.eval_options,
            state=meta.state,
        )
    end

    SymbolicRegression.template_shared_state(
        ::Type{<:SharedExpression}, contents::NamedTuple, metadata::Metadata
    ) = SharedTemplateState(10.0)

    function SymbolicRegression.get_template_shared_state(
        ::Type{<:SharedExpression}, ex::TemplateExpression
    )
        states = SharedTemplateState[]
        for inner in values(get_contents(ex))
            state = get_metadata(inner).state
            any(existing -> existing === state, states) || push!(states, state)
        end
        @assert length(states) == 1
        return only(states)
    end

    SymbolicRegression.copy_template_shared_state(
        ::Type{<:SharedExpression}, state::SharedTemplateState
    ) = SharedTemplateState(state.value)

    function SymbolicRegression.attach_template_shared_state(
        ::Type{<:SharedExpression},
        inner::SharedExpression,
        state::SharedTemplateState,
        key::Symbol,
    )
        return with_metadata(inner; state)
    end

    operators = OperatorEnum(; unary_operators=(cos,), binary_operators=(+,))
    structure = TemplateStructure{(:f, :g)}(
        ((; f, g), (x,)) -> f(x) + g(x); num_features=(; f=1, g=1)
    )

    template = TemplateExpression(
        (;
            f=SharedExpression(Node{Float64}(; feature=1); operators),
            g=SharedExpression(Node{Float64}(; val=2.0); operators),
        );
        structure,
        operators,
    )
    states = map(inner -> get_metadata(inner).state, values(get_contents(template)))
    @test states[1] === states[2]
    @test states[1].value == 10.0

    copied = copy(template)
    copied_states = map(inner -> get_metadata(inner).state, values(get_contents(copied)))
    @test copied_states[1] === copied_states[2]
    @test copied_states[1] !== states[1]
    @test copied_states[1].value == states[1].value

    copied_into = DynamicExpressions.copy_into!(
        DynamicExpressions.allocate_container(template), template
    )
    copied_into_states = map(inner -> get_metadata(inner).state, values(get_contents(copied_into)))
    @test copied_into_states[1] === copied_into_states[2]
    @test copied_into_states[1] !== states[1]

    raw_f = SharedExpression(
        Node{Float64}(; feature=1); operators, state=SharedTemplateState(1.0)
    )
    raw_g = SharedExpression(
        Node{Float64}(; val=3.0); operators, state=SharedTemplateState(2.0)
    )
    raw = TemplateExpression((; f=raw_f, g=raw_g), get_metadata(template))
    raw_states = map(inner -> get_metadata(inner).state, values(get_contents(raw)))
    @test raw_states[1] !== raw_states[2]
    @test raw_states[1].value == 1.0
    @test raw_states[2].value == 2.0

    spec = TemplateExpressionSpec(;
        structure,
        inner_expression_type=SharedExpression,
    )
    parsed = parse_expression((; f="#1", g="#1"); expression_spec=spec, operators)
    parsed_states = map(inner -> get_metadata(inner).state, values(get_contents(parsed)))
    @test parsed_states[1] === parsed_states[2]

    dataset = Dataset(randn(Float64, 1, 8), randn(Float64, 8))
    options = Options(; operators, expression_spec=spec, tournament_selection_n=5)
    created = create_expression(Node{Float64}(; val=0.0), options, dataset)
    created_states = map(inner -> get_metadata(inner).state, values(get_contents(created)))
    @test created_states[1] === created_states[2]
end
