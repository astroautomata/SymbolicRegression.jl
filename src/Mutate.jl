module MutateModule

using DispatchDoctor: @unstable
using DynamicExpressions:
    AbstractExpression,
    copy_into!,
    get_tree,
    preserve_sharing,
    count_scalar_constants,
    simplify_tree!,
    combine_operators,
    allocate_container
using ..CoreModule:
    AbstractOptions,
    AbstractMutationWeights,
    AbstractMutation,
    MutateConstant,
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
    Dataset,
    RecordType,
    sample_mutation,
    max_features,
    dataset_fraction,
    AbstractPlugin,
    AbstractPluginState,
    NoPluginState,
    MutationEvent,
    on_mutation_end!,
    mutation_acceptance_multiplier
using ..ComplexityModule: compute_complexity
using ..LossFunctionsModule: eval_cost, loss_to_cost
using ..CheckConstraintsModule: check_constraints
using ..PopMemberModule: AbstractPopMember, PopMember, create_child
using ..MutationFunctionsModule:
    mutate_constant,
    mutate_operator,
    mutate_feature,
    swap_operands,
    append_random_op,
    prepend_random_op,
    insert_random_op,
    delete_random_op!,
    crossover_trees,
    form_random_connection!,
    break_random_connection!,
    randomly_rotate_tree!,
    randomize_tree,
    backsolve_rewrite_random_node
using ..ConstantOptimizationModule: optimize_constants
using ..RecorderModule: @recorder

abstract type AbstractMutationResult{N<:AbstractExpression,P<:AbstractPopMember} end

"""
    MutationResult{N<:AbstractExpression,P<:AbstractPopMember}

Represents the result of a mutation operation in the genetic programming algorithm. This struct is used to return values from `mutate!` functions.

# Fields

- `tree::Union{N, Nothing}`: The mutated expression tree, if applicable. Either `tree` or `member` must be set, but not both.
- `member::Union{P, Nothing}`: The mutated population member, if applicable. Either `member` or `tree` must be set, but not both.
- `num_evals::Float64`: The number of evaluations performed during the mutation, which is automatically set to `0.0`. Only used for things like `optimize`.
- `return_immediately::Bool`: If `true`, the mutation process should return immediately, bypassing further checks, used for things like `simplify` or `optimize` where you already know the loss value of the result.

# Usage

This struct encapsulates the result of a mutation operation. Either a new expression tree or a new population member is returned, but not both.

Return the `member` if you want to return immediately, and have
computed the loss value as part of the mutation.
"""
struct MutationResult{N<:AbstractExpression,P<:AbstractPopMember} <:
       AbstractMutationResult{N,P}
    tree::Union{N,Nothing}
    member::Union{P,Nothing}
    num_evals::Float64
    return_immediately::Bool

    # Explicit constructor with keyword arguments
    function MutationResult{_N,_P}(;
        tree::Union{_N,Nothing}=nothing,
        member::Union{_P,Nothing}=nothing,
        num_evals::Float64=0.0,
        return_immediately::Bool=false,
    ) where {_N<:AbstractExpression,_P<:AbstractPopMember}
        @assert(
            (tree === nothing) ⊻ (member === nothing),
            "Mutation result must return either a tree or a pop member, not both"
        )
        return new{_N,_P}(tree, member, num_evals, return_immediately)
    end
end

"""
    _set_weight!(weights, ::Type{M}, value)

Set the weight of every entry whose mutation is `<: M` to `value` (in place).
Helper for `condition_mutation_weights!`.
"""
function _set_weight!(
    weights::AbstractVector, ::Type{M}, value::Real
) where {M<:AbstractMutation}
    for i in eachindex(weights)
        m, _ = weights[i]
        if m isa M
            weights[i] = m => Float64(value)
        end
    end
    return nothing
end

"""
    condition_mutation_weights!(weights, member::AbstractPopMember, options, curmaxsize, nfeatures)

Adjust the mutation `weights` (a `Vector{Pair{AbstractMutation,Float64}}`)
based on the properties of the current member and options — e.g. disable
operator-mutation when the tree has no operators, disable simplify when
`options.should_simplify` is false, etc.

Plugin overloads should use `_set_weight!(weights, MyMutation, w)` to
modify the per-mutation weight in place.
"""
function condition_mutation_weights!(
    weights::AbstractVector,
    member::P,
    options::AbstractOptions,
    curmaxsize::Int,
    nfeatures::Int,
) where {T,L,N<:AbstractExpression,P<:AbstractPopMember{T,L,N}}
    tree = get_tree(member.tree)
    if !preserve_sharing(typeof(member.tree))
        _set_weight!(weights, FormConnection, 0.0)
        _set_weight!(weights, BreakConnection, 0.0)
    end
    if tree.degree == 0
        _set_weight!(weights, MutateOperator, 0.0)
        _set_weight!(weights, SwapOperands, 0.0)
        _set_weight!(weights, DeleteNode, 0.0)
        _set_weight!(weights, Simplify, 0.0)
        if !tree.constant
            _set_weight!(weights, Optimize, 0.0)
            _set_weight!(weights, MutateConstant, 0.0)
        else
            _set_weight!(weights, MutateFeature, 0.0)
        end
        return nothing
    end

    if !any(node -> node.degree == 2, tree)
        _set_weight!(weights, SwapOperands, 0.0)
    end

    condition_mutate_constant!(typeof(member.tree), weights, member, options, curmaxsize)

    if nfeatures <= 1
        _set_weight!(weights, MutateFeature, 0.0)
    end

    complexity = compute_complexity(member, options)
    if complexity >= curmaxsize
        _set_weight!(weights, AddNode, 0.0)
        _set_weight!(weights, InsertNode, 0.0)
    end

    if !options.should_simplify
        _set_weight!(weights, Simplify, 0.0)
    end

    return nothing
end

"""
    condition_mutation_weights!(weights, state, plugin, member, options, curmaxsize, nfeatures)

Plugin-dispatched method: called once per plugin in tuple order after the
engine's legality conditioning. Default is a no-op.

!!! warning "Experimental"
"""
function condition_mutation_weights!(
    weights::AbstractVector,
    ::AbstractPluginState,
    ::AbstractPlugin,
    member,
    options,
    curmaxsize,
    nfeatures,
)
    return nothing
end

"""
Use this to modify how `mutate_constant` changes for an expression type.
"""
function condition_mutate_constant!(
    ::Type{<:AbstractExpression},
    weights::AbstractVector,
    member::AbstractPopMember,
    options::AbstractOptions,
    curmaxsize::Int,
)
    n_constants = count_scalar_constants(member.tree)
    factor = min(8, n_constants) / 8.0
    for i in eachindex(weights)
        m, w = weights[i]
        if m isa MutateConstant
            weights[i] = m => w * factor
        end
    end
    return nothing
end

# Go through one simulated options.annealing mutation cycle
@inline function _fire_on_mutation_end!(
    options::AbstractOptions,
    plugin_states::Tuple,
    mutation::AbstractMutation,
    event::MutationEvent,
    dataset,
)
    for (plugin, pstate) in zip(options.plugins, plugin_states)
        on_mutation_end!(pstate, plugin, mutation, event, dataset, options)
    end
    return nothing
end

#  exp(-delta/T) defines probability of accepting a change
@unstable function next_generation(
    dataset::D,
    member::P,
    temperature,
    curmaxsize::Int,
    options::AbstractOptions;
    tmp_recorder::RecordType,
    plugin_states::Tuple=(),
    population_for_backsolve=nothing,
)::Tuple{
    P,Bool,Float64
} where {T,L,D<:Dataset{T,L},N<:AbstractExpression{T},P<:AbstractPopMember{T,L,N}}
    parent_ref = member.ref
    num_evals = 0.0

    #TODO - reconsider this
    before_cost, before_loss = member.cost, member.loss

    nfeatures = max_features(dataset, options)

    weights = copy(options.mutations)

    condition_mutation_weights!(weights, member, options, curmaxsize, nfeatures)
    for (plugin, pstate) in zip(options.plugins, plugin_states)
        condition_mutation_weights!(
            weights, pstate, plugin, member, options, curmaxsize, nfeatures
        )
    end

    mutation_choice = sample_mutation(weights)

    successful_mutation = false
    attempts = 0
    max_attempts = 10
    node_storage = allocate_container(member.tree)

    #############################################
    # Mutations
    #############################################
    # local tree
    rtree = Ref{N}()
    while (!successful_mutation) && attempts < max_attempts
        rtree[] = copy_into!(node_storage, member.tree)

        mutation_result = mutate!(
            rtree[],
            member,
            mutation_choice,
            weights,
            options;
            recorder=tmp_recorder,
            temperature,
            dataset,
            cost=before_cost,
            loss=before_loss,
            parent_ref,
            curmaxsize,
            nfeatures,
            plugin_states,
            population_for_backsolve,
        )
        mutation_result::AbstractMutationResult{N,P}
        num_evals += mutation_result.num_evals::Float64

        if mutation_result.return_immediately
            @assert(
                mutation_result.member isa P,
                "Mutation result must return a `PopMember` if `return_immediately` is true"
            )
            _fire_on_mutation_end!(
                options,
                plugin_states,
                mutation_choice,
                MutationEvent(
                    true,
                    Float64(before_loss),
                    Float64(mutation_result.member.loss),
                ),
                dataset,
            )
            return mutation_result.member::P, true, num_evals
        else
            @assert(
                mutation_result.tree isa N,
                "Mutation result must return a tree if `return_immediately` is false"
            )
            rtree[] = mutation_result.tree::N
            successful_mutation = check_constraints(rtree[], options, curmaxsize)
            attempts += 1
        end
    end

    tree = rtree[]

    if !successful_mutation
        @recorder begin
            tmp_recorder["result"] = "reject"
            tmp_recorder["reason"] = "failed_constraint_check"
        end
        mutation_accepted = false
        _fire_on_mutation_end!(
            options,
            plugin_states,
            mutation_choice,
            MutationEvent(false, Float64(before_loss), NaN),
            dataset,
        )
        return (
            create_child(
                member,
                copy_into!(node_storage, member.tree),
                before_cost,
                before_loss,
                options;
                parent_ref=parent_ref,
                mutation_choice=mutation_choice,
            ),
            mutation_accepted,
            num_evals,
        )
    end

    after_cost, after_loss = eval_cost(dataset, tree, options)
    num_evals += dataset_fraction(dataset)

    if isnan(after_cost)
        @recorder begin
            tmp_recorder["result"] = "reject"
            tmp_recorder["reason"] = "nan_loss"
        end
        mutation_accepted = false
        _fire_on_mutation_end!(
            options,
            plugin_states,
            mutation_choice,
            MutationEvent(false, Float64(before_loss), NaN),
            dataset,
        )
        return (
            create_child(
                member,
                copy_into!(node_storage, member.tree),
                before_cost,
                before_loss,
                options;
                parent_ref=parent_ref,
                mutation_choice=mutation_choice,
            ),
            mutation_accepted,
            num_evals,
        )
    end

    probChange = 1.0
    if options.annealing
        # TODO: Try using log(after_cost) - log(before_cost) here
        delta = after_cost - before_cost
        probChange *= exp(-delta / (temperature * options.alpha))
    end
    for (plugin, pstate) in zip(options.plugins, plugin_states)
        probChange *= mutation_acceptance_multiplier(pstate, plugin, member, tree, options)
    end

    if probChange < rand()
        @recorder begin
            tmp_recorder["result"] = "reject"
            tmp_recorder["reason"] = "annealing_or_frequency"
        end
        mutation_accepted = false
        _fire_on_mutation_end!(
            options,
            plugin_states,
            mutation_choice,
            MutationEvent(false, Float64(before_loss), Float64(after_loss)),
            dataset,
        )
        return (
            create_child(
                member,
                copy_into!(node_storage, member.tree),
                before_cost,
                before_loss,
                options;
                parent_ref=parent_ref,
            ),
            mutation_accepted,
            num_evals,
        )
    else
        @recorder begin
            tmp_recorder["result"] = "accept"
            tmp_recorder["reason"] = "pass"
        end
        mutation_accepted = true
        new_member = create_child(
            member, tree, after_cost, after_loss, options; parent_ref=parent_ref
        )
        _fire_on_mutation_end!(
            options,
            plugin_states,
            mutation_choice,
            MutationEvent(true, Float64(before_loss), Float64(after_loss)),
            dataset,
        )
        return (new_member, mutation_accepted, num_evals)
    end
end

"""
    mutate!(
        new_tree::N,
        parent_member::P,
        mutation::AbstractMutation,
        mutations::AbstractVector{<:Pair{<:AbstractMutation,<:Real}},
        options::AbstractOptions;
        kws...,
    ) where {N<:AbstractExpression,P<:AbstractPopMember}

Perform `mutation` on the offspring `new_tree` (a fresh scratch copy of the
parent's tree). `parent_member` carries parent metadata (cost, loss, ref, etc.)
that some mutations need.

Add a new mutation by defining a struct subtyping
[`AbstractMutation`](@ref) and a matching `mutate!` method.

# Keywords

- `temperature`: The temperature parameter for annealing-based mutations.
- `dataset::Dataset`: The dataset used for scoring.
- `cost`: The cost of `parent_member` before mutation.
- `loss`: The loss of `parent_member` before mutation.
- `curmaxsize`: The current maximum size constraint, which may differ from `options.maxsize`.
- `nfeatures`: The number of features in the dataset.
- `parent_ref`: Reference to `parent_member`'s parent (used for lineage logging).
- `recorder::RecordType`: A recorder to log mutation details.
- `plugin_states::Tuple`: The active worker plugin states, in tuple order matching
  `options.plugins`.

# Returns

A `MutationResult{N,P}` object containing the mutated tree or member (but not both),
the number of evaluations performed, if any, and whether to return immediately from
the mutation function, or to let the `next_generation` function handle accepting or
rejecting the mutation. For example, a `simplify` operation will not change the loss,
so it can always return immediately.
"""
function mutate!(
    ::N,
    ::P,
    m::AbstractMutation,
    ::AbstractVector,
    ::AbstractOptions;
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    return error("Unknown mutation type: $(typeof(m))")
end

function mutate!(
    new_tree::N,
    parent_member::P,
    ::MutateConstant,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    temperature,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    new_tree = mutate_constant(new_tree, temperature, options)
    @recorder recorder["type"] = "mutate_constant"
    return MutationResult{N,P}(; tree=new_tree)
end

function mutate!(
    new_tree::N,
    parent_member::P,
    ::MutateOperator,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    new_tree = mutate_operator(new_tree, options)
    @recorder recorder["type"] = "mutate_operator"
    return MutationResult{N,P}(; tree=new_tree)
end

function mutate!(
    new_tree::N,
    parent_member::P,
    ::MutateFeature,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    nfeatures,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    new_tree = mutate_feature(new_tree, nfeatures)
    @recorder recorder["type"] = "mutate_feature"
    return MutationResult{N,P}(; tree=new_tree)
end

function mutate!(
    new_tree::N,
    parent_member::P,
    ::SwapOperands,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    new_tree = swap_operands(new_tree)
    @recorder recorder["type"] = "swap_operands"
    return MutationResult{N,P}(; tree=new_tree)
end

function mutate!(
    new_tree::N,
    parent_member::P,
    ::AddNode,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    nfeatures,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    if rand() < 0.5
        new_tree = append_random_op(new_tree, options, nfeatures)
        @recorder recorder["type"] = "add_node:append"
    else
        new_tree = prepend_random_op(new_tree, options, nfeatures)
        @recorder recorder["type"] = "add_node:prepend"
    end
    return MutationResult{N,P}(; tree=new_tree)
end

function mutate!(
    new_tree::N,
    parent_member::P,
    ::InsertNode,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    nfeatures,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    new_tree = insert_random_op(new_tree, options, nfeatures)
    @recorder recorder["type"] = "insert_node"
    return MutationResult{N,P}(; tree=new_tree)
end

function mutate!(
    new_tree::N,
    parent_member::P,
    ::DeleteNode,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    new_tree = delete_random_op!(new_tree)
    @recorder recorder["type"] = "delete_node"
    return MutationResult{N,P}(; tree=new_tree)
end

function mutate!(
    new_tree::N,
    parent_member::P,
    ::FormConnection,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    new_tree = form_random_connection!(new_tree)
    @recorder recorder["type"] = "form_connection"
    return MutationResult{N,P}(; tree=new_tree)
end

function mutate!(
    new_tree::N,
    parent_member::P,
    ::BreakConnection,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    new_tree = break_random_connection!(new_tree)
    @recorder recorder["type"] = "break_connection"
    return MutationResult{N,P}(; tree=new_tree)
end

function mutate!(
    new_tree::N,
    parent_member::P,
    ::RotateTree,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    new_tree = randomly_rotate_tree!(new_tree)
    @recorder recorder["type"] = "rotate_tree"
    return MutationResult{N,P}(; tree=new_tree)
end

function mutate!(
    new_tree::N,
    parent_member::P,
    m::Backsolve,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    dataset::Dataset,
    population_for_backsolve=nothing,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    new_tree = backsolve_rewrite_random_node(
        new_tree, dataset, options;
        backsolve_options=m.options,
        population_for_backsolve=population_for_backsolve,
    )
    @recorder recorder["type"] = "backsolve"
    return MutationResult{N,P}(; tree=new_tree)
end

# Handle mutations that require early return
function mutate!(
    new_tree::N,
    parent_member::P,
    ::Simplify,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    dataset::Dataset,
    parent_ref,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    @assert options.should_simplify
    simplify_tree!(new_tree, options.operators)
    new_tree = combine_operators(new_tree, options.operators)
    simplified_complexity = compute_complexity(new_tree, options)
    simplified_cost = loss_to_cost(
        parent_member.loss,
        dataset.use_baseline,
        dataset.baseline_loss,
        new_tree,
        options,
        simplified_complexity,
    )
    @recorder recorder["type"] = "simplify"
    new_member = create_child(
        parent_member,
        new_tree,
        simplified_cost,
        parent_member.loss,
        options;
        complexity=simplified_complexity,
        parent_ref=parent_ref,
    )
    return MutationResult{N,P}(; member=new_member, return_immediately=true)
end

function mutate!(
    new_tree::N,
    ::P,
    ::Randomize,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    curmaxsize,
    nfeatures,
    kws...,
) where {T,N<:AbstractExpression{T},P<:AbstractPopMember}
    new_tree = randomize_tree(new_tree, curmaxsize, options, nfeatures)
    @recorder recorder["type"] = "randomize"
    return MutationResult{N,P}(; tree=new_tree)
end

function mutate!(
    new_tree::N,
    parent_member::P,
    ::Optimize,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    dataset::Dataset,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    cur_member, new_num_evals = optimize_constants(dataset, parent_member, options)
    @recorder recorder["type"] = "optimize"
    return MutationResult{N,P}(;
        member=cur_member, num_evals=new_num_evals, return_immediately=true
    )
end

function mutate!(
    new_tree::N,
    parent_member::P,
    ::DoNothing,
    ::AbstractVector,
    options::AbstractOptions;
    recorder::RecordType,
    parent_ref,
    kws...,
) where {N<:AbstractExpression,P<:AbstractPopMember}
    @recorder begin
        recorder["type"] = "identity"
        recorder["result"] = "accept"
        recorder["reason"] = "identity"
    end
    return MutationResult{N,P}(;
        member=create_child(
            parent_member, new_tree, parent_member.cost, parent_member.loss, options; parent_ref=parent_ref
        ),
        return_immediately=true,
    )
end

"""Generate a generation via crossover of two members."""
function crossover_generation(
    member1::P,
    member2::P,
    dataset::D,
    curmaxsize::Int,
    options::AbstractOptions;
    recorder::RecordType=RecordType(),
)::Tuple{P,P,Bool,Float64} where {T,L,D<:Dataset{T,L},N,P<:AbstractPopMember{T,L,N}}
    tree1 = member1.tree
    tree2 = member2.tree
    crossover_accepted = false

    # We breed these until constraints are no longer violated:
    child_tree1, child_tree2 = crossover_trees(tree1, tree2)
    num_tries = 1
    max_tries = 10
    num_evals = 0.0
    afterSize1 = -1
    afterSize2 = -1
    while true
        afterSize1 = compute_complexity(child_tree1, options)
        afterSize2 = compute_complexity(child_tree2, options)
        # Both trees satisfy constraints
        if check_constraints(child_tree1, options, curmaxsize, afterSize1) &&
            check_constraints(child_tree2, options, curmaxsize, afterSize2)
            break
        end
        if num_tries > max_tries
            @recorder begin
                recorder["result"] = "reject"
                recorder["reason"] = "failed_constraint_check"
            end
            crossover_accepted = false
            return member1, member2, crossover_accepted, num_evals  # Fail.
        end
        child_tree1, child_tree2 = crossover_trees(tree1, tree2)
        num_tries += 1
    end
    after_cost1, after_loss1 = eval_cost(
        dataset, child_tree1, options; complexity=afterSize1
    )
    after_cost2, after_loss2 = eval_cost(
        dataset, child_tree2, options; complexity=afterSize2
    )
    num_evals += 2 * dataset_fraction(dataset)

    baby1 = create_child(
        (member1, member2),
        child_tree1::AbstractExpression,
        after_cost1,
        after_loss1,
        options;
        complexity=afterSize1,
        parent_ref=member1.ref,
    )::P
    baby2 = create_child(
        (member1, member2),
        child_tree2::AbstractExpression,
        after_cost2,
        after_loss2,
        options;
        complexity=afterSize2,
        parent_ref=member2.ref,
    )::P

    @recorder begin
        recorder["result"] = "accept"
        recorder["reason"] = "pass"
    end

    crossover_accepted = true
    return baby1, baby2, crossover_accepted, num_evals
end

end  # module MutateModule
