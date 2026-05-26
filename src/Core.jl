module CoreModule

function create_expression end

include("Utils.jl")
include("ProgramConstants.jl")
include("Dataset.jl")
include("Mutations.jl")
include("MutationWeights.jl")
include("OptionsStruct.jl")
include("Operators.jl")
include("ExpressionSpec.jl")
include("Plugin.jl")
include("Options.jl")
include("InterfaceDataTypes.jl")

using .ProgramConstantsModule: RecordType, DATA_TYPE, LOSS_TYPE
using .DatasetModule:
    Dataset,
    BasicDataset,
    SubDataset,
    is_weighted,
    has_units,
    max_features,
    batch,
    get_indices,
    get_full_dataset,
    dataset_fraction
using .MutationWeightsModule: AbstractMutationWeights, MutationWeights, sample_mutation
using .MutationsModule:
    AbstractMutation,
    MutateConstant,
    MutateConstantContext,
    MutateOperator,
    MutateFeature,
    SwapOperands,
    AddNode,
    InsertNode,
    DeleteNode,
    FormConnection,
    BreakConnection,
    RotateTree,
    Backsolve,
    Simplify,
    Randomize,
    Optimize,
    DoNothing,
    default_mutations
using .OptionsStructModule:
    AbstractOptions,
    Options,
    ComplexityMapping,
    specialized_options,
    operator_specialization,
    WarmStartIncompatibleError,
    check_warm_start_compatibility
using .OperatorsModule:
    get_safe_op,
    plus,
    sub,
    mult,
    square,
    cube,
    pow,
    safe_pow,
    safe_log,
    safe_log2,
    safe_log10,
    safe_log1p,
    safe_sqrt,
    safe_asin,
    safe_acos,
    safe_acosh,
    safe_atanh,
    neg,
    greater,
    less,
    greater_equal,
    less_equal,
    cond,
    relu,
    logical_or,
    logical_and,
    gamma,
    erf,
    erfc,
    atanh_clip
using .ExpressionSpecModule:
    AbstractExpressionSpec,
    ExpressionSpec,
    get_expression_type,
    get_expression_options,
    get_node_type
using .InterfaceDataTypesModule: init_value, sample_value, mutate_value
using .PluginModule:
    AbstractPlugin,
    AbstractPluginState,
    NoPluginState,
    MutationEvent,
    init_plugin_state,
    on_search_start!,
    on_search_end!,
    on_generation_end!,
    on_cycle_end!,
    on_mutation_end!,
    init_member,
    tournament_cost_multiplier,
    mutation_acceptance_multiplier,
    fork_worker_state,
    wrap_mutation_step,
    on_cycle_start!,
    prepare_mutation_context,
    condition_mutation!,
    invoke_init_member,
    default_adaptive_parsimony_plugin,
    default_adaptive_mutation_weights_plugin,
    default_mutation_loop_plugin,
    default_simulated_annealing_plugin

end
