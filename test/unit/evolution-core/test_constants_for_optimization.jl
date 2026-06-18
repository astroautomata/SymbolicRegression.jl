@testitem "Optimizable parameter hooks aggregate constants and template parameters" begin
    using DynamicExpressions
    using SymbolicRegression

    operators = OperatorEnum(; unary_operators=(), binary_operators=(+, *))
    variable_names = ["x1"]

    expr = parse_expression("x1 + 2.0"; operators, variable_names)
    flat = SymbolicRegression.get_constants_for_optimization(expr)[1]
    @test flat == [2.0]
    @test length(flat) == 1

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

    params, refs = SymbolicRegression.get_constants_for_optimization(template)
    @test params == [3.0, 2.0]
    @test length(params) == 2

    SymbolicRegression.set_constants_for_optimization!(template, [4.0, 5.0], refs)
    @test SymbolicRegression.get_constants_for_optimization(template)[1] == [4.0, 5.0]
end

@testitem "ComposableExpression extracts optimization gradients from wrapped tree" begin
    using DynamicExpressions: NodeTangent, get_contents
    using SymbolicRegression

    operators = OperatorEnum(; unary_operators=(), binary_operators=(+,))
    ex = ComposableExpression(Node{Float64}(; val=1.0); operators)
    grad = (; tree=NodeTangent(get_contents(ex), [0.5]), metadata=nothing)

    @test SymbolicRegression.extract_gradient_for_optimization(grad, ex) == [0.5]
end

@testitem "TemplateExpression default inners extract optimization gradients" begin
    using DynamicExpressions:
        DynamicExpressions, Metadata, NodeTangent, get_contents, get_metadata
    using SymbolicRegression

    operators = OperatorEnum(; unary_operators=(), binary_operators=(+,))
    structure = TemplateStructure{(:f,),(:p,)}(
        ((; f), (; p), (x,)) -> f(x) + p[1]; num_parameters=(; p=1)
    )
    template = TemplateExpression(
        (; f=ComposableExpression(Node{Float64}(; val=1.0); operators));
        structure,
        operators,
        parameters=(; p=[2.0]),
    )
    inner = get_contents(template).f

    struct TemplateGradient{C,M}
        contents::C
        metadata::M
    end
    DynamicExpressions.get_contents(grad::TemplateGradient) = grad.contents
    DynamicExpressions.get_metadata(grad::TemplateGradient) = grad.metadata

    grad = TemplateGradient(
        (; f=(; tree=NodeTangent(get_contents(inner), [0.5]), metadata=nothing)),
        Metadata((;
            parameters=(; p=SymbolicRegression.TemplateExpressionModule.ParamVector([0.25]))
        )),
    )

    @test SymbolicRegression.extract_gradient_for_optimization(grad, template) ==
        [0.5, 0.25]

    structural_grad = (;
        trees=(; f=(; tree=NodeTangent(get_contents(inner), [0.5]), metadata=nothing)),
        metadata=(;
            _data=(;
                parameters=(;
                    p=SymbolicRegression.TemplateExpressionModule.ParamVector([0.25])
                )
            )
        ),
    )
    @test SymbolicRegression.extract_gradient_for_optimization(
        structural_grad, template
    ) == [0.5, 0.25]
end

@testitem "Template constants hooks can expose candidate-local state" begin
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

    mutable struct TemplateOptState
        value::Float64
    end

    struct TemplateOptExpression{T,N<:AbstractExpressionNode{T},D} <:
           AbstractComposableExpression{T,N}
        tree::N
        metadata::Metadata{D}
    end

    function TemplateOptExpression(
        tree::AbstractExpressionNode{T};
        operators::Union{AbstractOperatorEnum,Nothing}=nothing,
        variable_names::Union{AbstractVector{<:AbstractString},Nothing}=nothing,
        eval_options::Union{EvalOptions,Nothing}=nothing,
        state::TemplateOptState=TemplateOptState(1.0),
    ) where {T}
        return TemplateOptExpression(
            tree, Metadata((; operators, variable_names, eval_options, state))
        )
    end

    DynamicExpressions.constructorof(::Type{<:TemplateOptExpression}) =
        TemplateOptExpression

    function DynamicExpressions.with_metadata(ex::TemplateOptExpression; kws...)
        meta = get_metadata(ex)
        state = haskey(kws, :state) ? kws[:state] : meta.state
        operators = haskey(kws, :operators) ? kws[:operators] : meta.operators
        variable_names =
            haskey(kws, :variable_names) ? kws[:variable_names] : meta.variable_names
        eval_options = haskey(kws, :eval_options) ? kws[:eval_options] : meta.eval_options
        return TemplateOptExpression(
            get_contents(ex), Metadata((; operators, variable_names, eval_options, state))
        )
    end

    SymbolicRegression.template_shared_state(
        ::Type{<:TemplateOptExpression}, contents::NamedTuple, metadata::Metadata
    ) = TemplateOptState(1.0)

    function SymbolicRegression.get_template_shared_state(
        ::Type{<:TemplateOptExpression}, ex::TemplateExpression
    )
        states = TemplateOptState[]
        for inner in values(get_contents(ex))
            state = get_metadata(inner).state
            any(existing -> existing === state, states) || push!(states, state)
        end
        @assert length(states) == 1
        return only(states)
    end

    SymbolicRegression.copy_template_shared_state(
        ::Type{<:TemplateOptExpression}, state::TemplateOptState
    ) = TemplateOptState(state.value)

    function SymbolicRegression.attach_template_shared_state(
        ::Type{<:TemplateOptExpression},
        inner::TemplateOptExpression,
        state::TemplateOptState,
        key::Symbol,
    )
        return with_metadata(inner; state)
    end

    function SymbolicRegression.get_template_constants_for_optimization(
        ::Type{<:TemplateOptExpression}, ex::TemplateExpression{T}
    ) where {T}
        state = SymbolicRegression.get_template_shared_state(TemplateOptExpression, ex)
        params = get_metadata(ex).parameters
        return T[state.value, params.p[1]], (; parameter_keys=[:p])
    end

    function SymbolicRegression.set_template_constants_for_optimization!(
        ::Type{<:TemplateOptExpression}, ex::TemplateExpression, x, refs
    )
        state = SymbolicRegression.get_template_shared_state(TemplateOptExpression, ex)
        state.value = x[1]
        get_metadata(ex).parameters.p._data[1] = x[2]
        return ex
    end

    function SymbolicRegression.extract_template_gradient_for_optimization(
        ::Type{<:TemplateOptExpression}, grad, ex::TemplateExpression{T}
    ) where {T}
        state = SymbolicRegression.get_template_shared_state(TemplateOptExpression, grad)
        return T[state.value, get_metadata(grad).parameters.p[1]]
    end

    operators = OperatorEnum(; unary_operators=(), binary_operators=(+,))
    structure = TemplateStructure{(:f,),(:p,)}(
        ((; f), (; p), (x,)) -> f(x) + p[1]; num_parameters=(; p=1)
    )
    template = TemplateExpression(
        (; f=TemplateOptExpression(Node{Float64}(; feature=1); operators));
        structure,
        operators,
        parameters=(; p=[2.0]),
    )

    params, refs = SymbolicRegression.get_constants_for_optimization(template)
    @test params == [1.0, 2.0]
    @test SymbolicRegression.ConstantOptimizationModule.count_constants_for_optimization(
        template
    ) == length(params)

    SymbolicRegression.set_constants_for_optimization!(template, [3.0, 4.0], refs)
    @test SymbolicRegression.get_constants_for_optimization(template)[1] == [3.0, 4.0]
    @test get_metadata(first(values(get_contents(template)))).state.value == 3.0
    @test get_metadata(template).parameters.p[1] == 4.0

    grad_inner = TemplateOptExpression(
        Node{Float64}(; feature=1); operators, state=TemplateOptState(0.5)
    )
    grad = TemplateExpression(
        (; f=grad_inner),
        Metadata((;
            structure,
            operators,
            variable_names=nothing,
            parameters=(;
                p=SymbolicRegression.TemplateExpressionModule.ParamVector([0.25])
            ),
        )),
    )
    @test SymbolicRegression.extract_gradient_for_optimization(grad, template) ==
        [0.5, 0.25]
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
