module InterfacesModule

using Interfaces: Interfaces, @interface, @implements, Arguments
using DynamicExpressions: AbstractExpression, Node, GraphNode, Expression
using ..CoreModule:
    AbstractPlugin,
    AbstractMutation,
    Options,
    ExpressionSpec,
    Dataset,
    RecordType,
    MutationEvent,
    MutationAcceptanceContext,
    MutationStepResult,
    ConstantMutation,
    OperatorMutation,
    FeatureMutation,
    SwapOperandsMutation,
    AddNodeMutation,
    InsertNodeMutation,
    DeleteNodeMutation,
    FormConnectionMutation,
    BreakConnectionMutation,
    RotateTreeMutation,
    BacksolveMutation,
    SimplifyMutation,
    RandomizeMutation,
    OptimizeMutation,
    DoNothingMutation,
    max_features,
    init_plugin_state,
    on_search_start!,
    on_search_end!,
    on_generation_end!,
    on_cycle_end!,
    on_mutation_end!,
    init_member,
    tournament_cost_multiplier,
    mutation_acceptance_multiplier,
    fork_plugin_state,
    refresh_worker_plugin_state,
    wrap_mutation_step,
    on_cycle_start!,
    prepare_mutation_context,
    condition_mutation!
using ..MutateModule: mutate!, condition_mutation_weights!, MutationResult
using ..PopMemberModule: PopMember
using ..PopulationModule: Population
using ..HallOfFameModule: HallOfFame
using ..AdaptiveParsimonyModule: AdaptiveParsimonyPlugin
using ..AdaptiveMutationWeightsModule: AdaptiveMutationWeightsPlugin
using ..MutationBurstModule: MutationBurstPlugin
using ..SimulatedAnnealingModule: SimulatedAnnealingPlugin

struct _FallbackPlugin <: AbstractPlugin end

const _PLUGIN_FALLBACKS = (;
    (on_search_start!)=which(on_search_start!, Tuple{Any,_FallbackPlugin,Any,Any,Any}),
    (on_search_end!)=which(on_search_end!, Tuple{Any,_FallbackPlugin,Any,Any,Any,Any}),
    (on_generation_end!)=which(
        on_generation_end!, Tuple{Any,_FallbackPlugin,Any,Any,Any,Any,Any}
    ),
    (on_cycle_end!)=which(on_cycle_end!, Tuple{Any,_FallbackPlugin,Any,Any,Any,Any}),
    (on_mutation_end!)=which(
        on_mutation_end!, Tuple{Any,_FallbackPlugin,AbstractMutation,MutationEvent,Any,Any}
    ),
    init_member=which(init_member, Tuple{Any,_FallbackPlugin,Any,Any}),
    tournament_cost_multiplier=which(
        tournament_cost_multiplier, Tuple{Any,_FallbackPlugin,Any,Any}
    ),
    mutation_acceptance_multiplier=which(
        mutation_acceptance_multiplier,
        Tuple{Any,_FallbackPlugin,MutationAcceptanceContext,Any},
    ),
    fork_plugin_state=which(fork_plugin_state, Tuple{Any,_FallbackPlugin,Any}),
    refresh_worker_plugin_state=which(
        refresh_worker_plugin_state, Tuple{Any,Any,_FallbackPlugin,Any}
    ),
    (on_cycle_start!)=which(on_cycle_start!, Tuple{Any,_FallbackPlugin,Int,Int,Any}),
    (condition_mutation!)=which(
        condition_mutation!, Tuple{Any,Any,_FallbackPlugin,AbstractMutation,Any}
    ),
    wrap_mutation_step=which(wrap_mutation_step, Tuple{Any,_FallbackPlugin}),
    (condition_mutation_weights!)=which(
        condition_mutation_weights!,
        Tuple{AbstractVector,Any,_FallbackPlugin,Any,Any,Int,Int},
    ),
)

const _MUTATION_FALLBACK = which(mutate!, Tuple{Any,Any,AbstractMutation,Any})

function _get_argument(args::Arguments, name::Symbol, default)
    haskey(args, name) ? args[name] : default
end

function _has_specialized_method(f, fallback::Method, args...)
    return which(f, Tuple{map(typeof, args)...}) !== fallback
end

function _has_state_specific_override(f, fallback::Method, state_positions, call_args...)
    query_types = ntuple(length(call_args)) do i
        i in state_positions ? Any : typeof(call_args[i])
    end
    query = Core.apply_type(Tuple, typeof(f), query_types...)
    return any(methods(f)) do method
        method !== fallback && typeintersect(method.sig, query) !== Union{}
    end
end

function _plugin_state_compatible(f, fallback::Method, state_positions, call_args...)
    which(f, Tuple{map(typeof, call_args)...}) !== fallback && return true
    return !_has_state_specific_override(f, fallback, state_positions, call_args...)
end

function _head_plugin_state(args::Arguments)
    init_plugin_state(args.plugin, args.options, args.dataset)
end

function _worker_plugin_state(args::Arguments)
    head_state = _head_plugin_state(args)
    worker_state = fork_plugin_state(head_state, args.plugin, args.dataset)
    return refresh_worker_plugin_state(worker_state, head_state, args.plugin, args.dataset)
end

_population(args::Arguments) = Population([args.member])

function _check_init_plugin_state(args::Arguments)
    _head_plugin_state(args)
    return true
end

function _check_on_search_start!(args::Arguments)
    state = _head_plugin_state(args)
    runtime_options = _get_argument(args, :runtime_options, nothing)
    call_args = (state, args.plugin, args.dataset, args.options, runtime_options)
    _plugin_state_compatible(
        on_search_start!, _PLUGIN_FALLBACKS.on_search_start!, (1,), call_args...
    ) || return false
    return on_search_start!(call_args...) === nothing
end

function _check_on_search_end!(args::Arguments)
    state = _head_plugin_state(args)
    search_state = _get_argument(args, :search_state, nothing)
    runtime_options = _get_argument(args, :runtime_options, nothing)
    call_args = (
        state, args.plugin, search_state, args.dataset, args.options, runtime_options
    )
    _plugin_state_compatible(
        on_search_end!, _PLUGIN_FALLBACKS.on_search_end!, (1,), call_args...
    ) || return false
    return on_search_end!(call_args...) === nothing
end

function _check_on_generation_end!(args::Arguments)
    state = _head_plugin_state(args)
    search_state = _get_argument(args, :search_state, nothing)
    runtime_options = _get_argument(args, :runtime_options, nothing)
    returned_pop = _get_argument(args, :returned_pop, _population(args))
    call_args = (
        state,
        args.plugin,
        search_state,
        args.dataset,
        args.options,
        runtime_options,
        returned_pop,
    )
    _plugin_state_compatible(
        on_generation_end!, _PLUGIN_FALLBACKS.on_generation_end!, (1,), call_args...
    ) || return false
    return on_generation_end!(call_args...) === nothing
end

function _check_on_cycle_end!(args::Arguments)
    state = _worker_plugin_state(args)
    pop = _get_argument(args, :population, _population(args))
    hof = _get_argument(args, :hall_of_fame, HallOfFame(args.options, args.dataset))
    call_args = (state, args.plugin, pop, args.dataset, hof, args.options)
    _plugin_state_compatible(
        on_cycle_end!, _PLUGIN_FALLBACKS.on_cycle_end!, (1,), call_args...
    ) || return false
    return on_cycle_end!(call_args...) === nothing
end

function _check_on_mutation_end!(args::Arguments)
    state = _worker_plugin_state(args)
    event = _get_argument(
        args,
        :mutation_event,
        MutationEvent(
            true, args.member.cost, args.member.cost, args.member.loss, args.member.loss, 1
        ),
    )
    call_args = (state, args.plugin, args.mutation, event, args.dataset, args.options)
    _plugin_state_compatible(
        on_mutation_end!, _PLUGIN_FALLBACKS.on_mutation_end!, (1,), call_args...
    ) || return false
    return on_mutation_end!(call_args...) === nothing
end

function _check_init_member(args::Arguments)
    state = _head_plugin_state(args)
    call_args = (state, args.plugin, args.dataset, args.options)
    _plugin_state_compatible(
        init_member, _PLUGIN_FALLBACKS.init_member, (1,), call_args...
    ) || return false
    member = init_member(call_args...)
    return isnothing(member) || member isa AbstractExpression
end

function _valid_multiplier(multiplier)
    return multiplier isa Real && multiplier >= zero(multiplier)
end

function _check_tournament_cost_multiplier(args::Arguments)
    state = _worker_plugin_state(args)
    call_args = (state, args.plugin, args.member, args.options)
    _plugin_state_compatible(
        tournament_cost_multiplier,
        _PLUGIN_FALLBACKS.tournament_cost_multiplier,
        (1,),
        call_args...,
    ) || return false
    return _valid_multiplier(tournament_cost_multiplier(call_args...))
end

function _check_mutation_acceptance_multiplier(args::Arguments)
    state = _worker_plugin_state(args)
    context = _get_argument(
        args,
        :mutation_acceptance_context,
        MutationAcceptanceContext(
            args.member, copy(args.member.tree), args.member.cost, args.member.cost
        ),
    )
    call_args = (state, args.plugin, context, args.options)
    _plugin_state_compatible(
        mutation_acceptance_multiplier,
        _PLUGIN_FALLBACKS.mutation_acceptance_multiplier,
        (1,),
        call_args...,
    ) || return false
    return _valid_multiplier(mutation_acceptance_multiplier(call_args...))
end

function _check_fork_plugin_state(args::Arguments)
    state = _head_plugin_state(args)
    call_args = (state, args.plugin, args.dataset)
    _plugin_state_compatible(
        fork_plugin_state, _PLUGIN_FALLBACKS.fork_plugin_state, (1,), call_args...
    ) || return false
    fork_plugin_state(call_args...)
    return true
end

function _check_refresh_worker_plugin_state(args::Arguments)
    state = _head_plugin_state(args)
    worker_state = fork_plugin_state(state, args.plugin, args.dataset)
    call_args = (worker_state, state, args.plugin, args.dataset)
    _plugin_state_compatible(
        refresh_worker_plugin_state,
        _PLUGIN_FALLBACKS.refresh_worker_plugin_state,
        (1, 2),
        call_args...,
    ) || return false
    refresh_worker_plugin_state(call_args...)
    return true
end

function _check_on_cycle_start!(args::Arguments)
    state = _worker_plugin_state(args)
    call_args = (state, args.plugin, 1, 2, args.options)
    _plugin_state_compatible(
        on_cycle_start!, _PLUGIN_FALLBACKS.on_cycle_start!, (1,), call_args...
    ) || return false
    return on_cycle_start!(call_args...) === nothing
end

function _check_condition_mutation!(args::Arguments)
    state = _worker_plugin_state(args)
    context = _get_argument(
        args, :mutation_context, prepare_mutation_context(args.mutation)
    )
    call_args = (context, state, args.plugin, args.mutation, args.options)
    _plugin_state_compatible(
        condition_mutation!, _PLUGIN_FALLBACKS.condition_mutation!, (2,), call_args...
    ) || return false
    return condition_mutation!(call_args...) === nothing
end

function _check_wrap_mutation_step(args::Arguments)
    state = _worker_plugin_state(args)
    call_args = (state, args.plugin)
    _plugin_state_compatible(
        wrap_mutation_step, _PLUGIN_FALLBACKS.wrap_mutation_step, (1,), call_args...
    ) || return false
    wrapper = wrap_mutation_step(call_args...)
    isnothing(wrapper) && return true
    observed_results = MutationStepResult[]
    next_step = function (parent)
        result = MutationStepResult(parent, true, length(observed_results) + 1, 0.0)
        push!(observed_results, result)
        return result
    end
    applicable(wrapper, args.member, next_step) || return false
    result = wrapper(args.member, next_step)
    return result isa MutationStepResult &&
           !isempty(observed_results) &&
           any(isequal(result), observed_results)
end

function _check_condition_mutation_weights!(args::Arguments)
    state = _worker_plugin_state(args)
    weights = copy(args.options.mutations)
    call_args = (
        weights,
        state,
        args.plugin,
        args.member,
        args.options,
        args.options.maxsize,
        max_features(args.dataset, args.options),
    )
    _plugin_state_compatible(
        condition_mutation_weights!,
        _PLUGIN_FALLBACKS.condition_mutation_weights!,
        (2,),
        call_args...,
    ) || return false
    condition_mutation_weights!(call_args...) === nothing || return false
    return all(weights) do pair
        pair isa Pair{<:AbstractMutation,<:Real} && last(pair) >= 0
    end && any(pair -> last(pair) > 0, weights)
end

#! format: off
const plugin_components = (
    mandatory = (
        init_plugin_state = "constructs plugin state for one output" => _check_init_plugin_state,
        on_search_start! = "handles search startup" => _check_on_search_start!,
        on_search_end! = "handles search teardown" => _check_on_search_end!,
        on_generation_end! = "observes a returned worker population" => _check_on_generation_end!,
        on_cycle_end! = "observes the end of an evolution cycle" => _check_on_cycle_end!,
        on_mutation_end! = "observes a completed mutation" => _check_on_mutation_end!,
        init_member = "provides an initial expression" => _check_init_member,
        tournament_cost_multiplier = "returns a nonnegative tournament multiplier" => _check_tournament_cost_multiplier,
        mutation_acceptance_multiplier = "returns a nonnegative mutation-acceptance multiplier" => _check_mutation_acceptance_multiplier,
        fork_plugin_state = "constructs worker state from head state" => _check_fork_plugin_state,
        refresh_worker_plugin_state = "refreshes persistent worker state" => _check_refresh_worker_plugin_state,
        on_cycle_start! = "observes the start of an evolution cycle" => _check_on_cycle_start!,
        condition_mutation! = "conditions a selected mutation context" => _check_condition_mutation!,
        wrap_mutation_step = "wraps mutation steps and returns an engine-produced result" => _check_wrap_mutation_step,
        condition_mutation_weights! = "conditions mutation weights without invalidating them" => _check_condition_mutation_weights!,
    ),
    optional = (;),
)
#! format: on

const plugin_description = """
Defines the interface for `AbstractPlugin` implementations.

Tests receive an `Interfaces.Arguments` value with `plugin`, `options`,
`dataset`, `member`, and `mutation` fields. Additional fields can provide
`runtime_options`, `search_state`, `population`, `returned_pop`,
`hall_of_fame`, `mutation_event`, `mutation_acceptance_context`, or
`mutation_context` values for hooks that require custom concrete types. Every
hook is tested, and default hook implementations satisfy the interface. Head
and worker hooks are tested with the states produced by `init_plugin_state`,
`fork_plugin_state`, and `refresh_worker_plugin_state`.
"""

@interface(PluginInterface, AbstractPlugin, plugin_components, plugin_description,)

function _check_mutate!(args::Arguments)
    call_args = (args.new_tree, args.parent_member, args.mutation, args.options)
    _has_specialized_method(mutate!, _MUTATION_FALLBACK, call_args...) || return false
    result = mutate!(
        call_args...;
        recorder=args.recorder,
        context=args.context,
        dataset=args.dataset,
        cost=args.cost,
        loss=args.loss,
        parent_ref=args.parent_ref,
        curmaxsize=args.curmaxsize,
        nfeatures=args.nfeatures,
        plugin_states=args.plugin_states,
        population_for_backsolve=args.population_for_backsolve,
    )
    N = typeof(args.new_tree)
    P = typeof(args.parent_member)
    result isa MutationResult{N,P} || return false
    isfinite(result.num_evals) && result.num_evals >= 0 || return false
    return if result.return_immediately
        isnothing(result.tree) && result.member isa P
    else
        result.tree isa N && isnothing(result.member)
    end
end

function _check_prepare_mutation_context(args::Arguments)
    call_args = (args.mutation,)
    context = prepare_mutation_context(call_args...)
    isnothing(context) && return true
    next_context = prepare_mutation_context(call_args...)
    return Base.ismutable(context) && context !== next_context
end

const mutation_components = (
    mandatory=(
        (mutate!)="accepts the engine mutation context and returns a valid MutationResult" =>
            _check_mutate!,
        prepare_mutation_context="constructs a fresh per-call mutation context" =>
            _check_prepare_mutation_context,
    ),
    optional=(;),
)

const mutation_description = """
Defines the interface for `AbstractMutation` implementations.

Tests receive an `Interfaces.Arguments` value containing the four positional
arguments to `mutate!` and every keyword supplied by the mutation
engine. The `mutation` field must contain the mutation implementation being
tested. The default `prepare_mutation_context` implementation satisfies the
interface.
"""

@interface(MutationInterface, AbstractMutation, mutation_components, mutation_description,)

function _plugin_test_arguments(plugin::AbstractPlugin)
    options = Options(;
        binary_operators=(+, *),
        plugins=(plugin,),
        default_plugins=(),
        default_mutations=(),
        mutations=(DoNothingMutation() => 1.0,),
        use_frequency=false,
        use_frequency_in_tournament=false,
        annealing=false,
        deterministic=true,
    )
    dataset = Dataset(zeros(2, 8), zeros(8))
    member = PopMember(dataset, Node(Float64; feature=1), options; deterministic=true)
    return Arguments(; plugin, options, dataset, member, mutation=ConstantMutation())
end

function _mutation_fixture(mutation::Union{FormConnectionMutation,BreakConnectionMutation})
    options = Options(;
        binary_operators=(+, *),
        unary_operators=(cos,),
        expression_spec=ExpressionSpec(; node_type=GraphNode),
        maxsize=30,
        default_plugins=(),
        default_mutations=(),
        mutations=(mutation => 1.0,),
        deterministic=true,
    )
    x1 = GraphNode(Float64; feature=1)
    x2 = GraphNode(Float64; feature=2)
    tree = if mutation isa FormConnectionMutation
        cos(x1 * x2 + 1.5)
    else
        shared = cos(x1 + 1.5) * x2
        shared + shared
    end
    return options,
    Expression(tree; operators=options.operators, variable_names=["x1", "x2"])
end

function _mutation_fixture(mutation::AbstractMutation)
    options = Options(;
        binary_operators=(+, *),
        unary_operators=(cos,),
        maxsize=30,
        default_plugins=(),
        default_mutations=(),
        mutations=(mutation => 1.0,),
        deterministic=true,
    )
    x1 = Node(Float64; feature=1)
    x2 = Node(Float64; feature=2)
    tree = if mutation isa BacksolveMutation
        Node(Float64; val=1.5)
    else
        cos(x1 + 1.5) * x2
    end
    return options,
    Expression(tree; operators=options.operators, variable_names=["x1", "x2"])
end

function _mutation_test_arguments(mutation::AbstractMutation)
    options, expression = _mutation_fixture(mutation)
    X = [
        1.0 2.0 3.0 4.0 5.0 6.0 7.0 8.0
        2.0 3.0 4.0 5.0 6.0 7.0 8.0 9.0
    ]
    dataset = Dataset(X, vec(sum(X; dims=1)))
    member = PopMember(dataset, expression, options; deterministic=true)
    return Arguments(;
        mutation,
        new_tree=copy(member.tree),
        parent_member=member,
        options,
        recorder=RecordType(),
        context=prepare_mutation_context(mutation),
        dataset,
        cost=member.cost,
        loss=member.loss,
        parent_ref=member.ref,
        curmaxsize=options.maxsize,
        nfeatures=size(X, 1),
        plugin_states=(),
        population_for_backsolve=nothing,
    )
end

@implements(
    PluginInterface,
    AdaptiveParsimonyPlugin,
    [_plugin_test_arguments(AdaptiveParsimonyPlugin())],
)
@implements(
    PluginInterface,
    AdaptiveMutationWeightsPlugin,
    [_plugin_test_arguments(AdaptiveMutationWeightsPlugin())],
)
@implements(
    PluginInterface, MutationBurstPlugin, [_plugin_test_arguments(MutationBurstPlugin())],
)
@implements(
    PluginInterface,
    SimulatedAnnealingPlugin,
    [_plugin_test_arguments(SimulatedAnnealingPlugin())],
)

@implements(
    MutationInterface, ConstantMutation, [_mutation_test_arguments(ConstantMutation())],
)
for (mutation_type, mutation) in (
    OperatorMutation => OperatorMutation(),
    FeatureMutation => FeatureMutation(),
    SwapOperandsMutation => SwapOperandsMutation(),
    AddNodeMutation => AddNodeMutation(),
    InsertNodeMutation => InsertNodeMutation(),
    DeleteNodeMutation => DeleteNodeMutation(),
    FormConnectionMutation => FormConnectionMutation(),
    BreakConnectionMutation => BreakConnectionMutation(),
    RotateTreeMutation => RotateTreeMutation(),
    BacksolveMutation => BacksolveMutation(),
    SimplifyMutation => SimplifyMutation(),
    RandomizeMutation => RandomizeMutation(),
    OptimizeMutation => OptimizeMutation(),
    DoNothingMutation => DoNothingMutation(),
)
    @eval @implements(
        MutationInterface, $mutation_type, [_mutation_test_arguments($mutation)],
    )
end

end
