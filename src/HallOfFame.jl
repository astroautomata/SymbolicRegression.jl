module HallOfFameModule

using StyledStrings: @styled_str
using DynamicExpressions:
    AbstractExpression, string_tree, get_tree, count_depth, count_scalar_constants
using ..UtilsModule: split_string, AnnotatedIOBuffer, dump_buffer
using ..CoreModule:
    AbstractOptions, Dataset, DATA_TYPE, LOSS_TYPE, relu, create_expression, init_value
using ..ComplexityModule: compute_complexity
using ..PopMemberModule: AbstractPopMember, PopMember
using ..CheckConstraintsModule: check_constraints
using ..InterfaceDynamicExpressionsModule: format_dimensions, WILDCARD_UNIT_STRING
using Printf: @sprintf

"""Abstract strategy for hall-of-fame keying."""
abstract type AbstractHallOfFameCriteria end

"""Built-in hall-of-fame criteria defined by axis symbols.

The first axis must be `:complexity`.
"""
struct HallOfFameCriteria{N} <: AbstractHallOfFameCriteria
    axes::NTuple{N,Symbol}
end

function HallOfFameCriteria(axes::Vararg{Symbol,N}) where {N}
    isempty(axes) && throw(ArgumentError("HallOfFameCriteria requires at least one axis"))
    first(axes) == :complexity ||
        throw(ArgumentError("HallOfFameCriteria must start with :complexity as first axis"))
    return HallOfFameCriteria{N}(axes)
end

@inline function _criterion_value(axis::Symbol, member, options)::Int
    if axis === :complexity
        return compute_complexity(member, options)
    elseif axis === :depth
        return count_depth(get_tree(member.tree))
    elseif axis === :nconsts
        return count_scalar_constants(member.tree)
    else
        throw(ArgumentError("Unsupported HallOfFameCriteria axis: $(axis)"))
    end
end

function hof_key(criteria::HallOfFameCriteria{N}, member, options)::NTuple{N,Int} where {N}
    return ntuple(i -> _criterion_value(criteria.axes[i], member, options), Val(N))
end
"""
    HallOfFame{T<:DATA_TYPE,L<:LOSS_TYPE,N<:AbstractExpression{T},PM<:AbstractPopMember{T,L,N}}

List of the best members seen all time.

For compatibility this preserves legacy fields:
- `members::Array{PM,1}`: best member per complexity (for convenience/backward compatibility)
- `exists::Array{Bool,1}`: whether each complexity slot has at least one member

Actual archive cells are stored in `cells` keyed by tuple keys produced by criteria.
"""
struct HallOfFame{
    T<:DATA_TYPE,L<:LOSS_TYPE,N<:AbstractExpression{T},PM<:AbstractPopMember{T,L,N}
}
    criteria::AbstractHallOfFameCriteria
    cells::Vector{Dict{Tuple,PM}}
    members::Array{PM,1}
    exists::Array{Bool,1}
end

function Base.show(
    io::IO, mime::MIME"text/plain", hof::HallOfFame{T,L,N,PM}
) where {T,L,N,PM}
    println(io, "HallOfFame{...}:")
    for i in eachindex(hof.members, hof.exists)
        s_member, s_exists = if hof.exists[i]
            sprint((io, m) -> show(io, mime, m), hof.members[i]), "true"
        else
            "undef", "false"
        end
        println(io, " "^4 * ".exists[$i] = $s_exists")
        print(io, " "^4 * ".members[$i] =")
        splitted = split(strip(s_member), '\n')
        if length(splitted) == 1
            println(io, " " * s_member)
        else
            println(io)
            foreach(line -> println(io, " "^8 * line), splitted)
        end
    end
    return nothing
end

function Base.eltype(::Union{HOF,Type{HOF}}) where {T,L,N,PM,HOF<:HallOfFame{T,L,N,PM}}
    return PM
end

"""
    HallOfFame(options::AbstractOptions, dataset::Dataset{T,L}) where {T<:DATA_TYPE,L<:LOSS_TYPE}

Construct an empty HallOfFame.

If the passed options have `hall_of_fame_criteria`, that criteria is used;
otherwise defaults to `( :complexity, )`.
"""
function HallOfFame(
    options::AbstractOptions, dataset::Dataset{T,L}
) where {T<:DATA_TYPE,L<:LOSS_TYPE}
    criteria = if hasproperty(options, :hall_of_fame_criteria)
        maybe = getproperty(options, :hall_of_fame_criteria)
        maybe isa AbstractHallOfFameCriteria ? maybe : HallOfFameCriteria(:complexity)
    else
        HallOfFameCriteria(:complexity)
    end
    return HallOfFame(options, dataset, criteria)
end

function HallOfFame(
    options::AbstractOptions, dataset::Dataset{T,L}, criteria::AbstractHallOfFameCriteria
) where {T<:DATA_TYPE,L<:LOSS_TYPE}
    base_tree = create_expression(init_value(T), options, dataset)
    PM = options.popmember_type

    # Create a prototype member to get the concrete type
    prototype = PM(
        copy(base_tree),
        L(0),
        L(Inf),
        options,
        1;  # complexity
        parent=-1,
        deterministic=options.deterministic,
    )

    PMtype = typeof(prototype)
    key = hof_key(criteria, prototype, options)
    key isa Tuple || throw(ArgumentError("`hof_key` must return a tuple"))

    cells = [Dict{Tuple,PMtype}() for _ in 1:(options.maxsize)]
    empty_members = [copy(prototype) for _ in 1:(options.maxsize)]

    return HallOfFame{T,L,typeof(base_tree),PMtype}(
        criteria, cells, empty_members, [false for _ in 1:(options.maxsize)]
    )
end

function Base.copy(hof::HallOfFame{T,L,N,PM}) where {T,L,N,PM}
    cells = [Dict(k => copy(member) for (k, member) in d) for d in hof.cells]
    return HallOfFame{T,L,N,PM}(
        hof.criteria,
        cells,
        [copy(member) for member in hof.members],
        [exists for exists in hof.exists],
    )
end

"""Iterate over all `(key, member)` pairs that are populated."""
struct DefinedCells{H}
    hall_of_fame::H
end

function Base.iterate(dc::DefinedCells, state=(1, nothing))
    hof = dc.hall_of_fame
    i, inner = state
    while i <= length(hof.cells)
        d = hof.cells[i]
        step = if inner === nothing
            iterate(d)
        else
            iterate(d, inner)
        end
        if step === nothing
            i += 1
            inner = nothing
            continue
        else
            kv, inner2 = step
            return ((kv[1], kv[2]), (i, inner2))
        end
    end
    return nothing
end

Base.IteratorEltype(::Type{<:DefinedCells}) = Base.EltypeUnknown()
Base.IteratorSize(::Type{<:DefinedCells}) = Base.SizeUnknown()
Base.length(dc::DefinedCells) = sum(length, dc.hall_of_fame.cells)

"""Return an iterator over members which have been set in the hall of fame."""
defined_cells(hall_of_fame::HallOfFame) = DefinedCells(hall_of_fame)

"""Iterate over members which have been set in the hall of fame."""
struct DefinedMembers{H}
    hall_of_fame::H
end

function Base.iterate(dm::DefinedMembers, state::Int=1)
    hof = dm.hall_of_fame
    for i in state:lastindex(hof.members)
        hof.exists[i] && return (hof.members[i], i + 1)
    end
    return nothing
end

Base.IteratorEltype(::Type{<:DefinedMembers}) = Base.HasEltype()
Base.eltype(::Type{DefinedMembers{H}}) where {T,L,N,PM,H<:HallOfFame{T,L,N,PM}} = PM
Base.IteratorSize(::Type{<:DefinedMembers}) = Base.SizeUnknown()
Base.length(dm::DefinedMembers) = count(_ -> true, dm)

defined_members(hall_of_fame::HallOfFame) = DefinedMembers(hall_of_fame)

"""Pareto dominance for minimization objectives (complexity, loss)."""
@inline function dominates(a_complexity::Int, a_loss, b_complexity::Int, b_loss)
    return (a_complexity <= b_complexity) &&
           (a_loss <= b_loss) &&
           ((a_complexity < b_complexity) || (a_loss < b_loss))
end

"""Return the dominating (non-dominated) set from the hall of fame.

This corresponds to the Pareto frontier in objectives `(complexity, loss)`.
"""
function dominating_members(hall_of_fame::HallOfFame{T,L,N,PM}) where {T,L,N,PM}
    dominating = PM[]
    best_loss = typemax(L)
    for complexity in eachindex(hall_of_fame.members)
        hall_of_fame.exists[complexity] || continue
        member = hall_of_fame.members[complexity]
        if member.loss < best_loss
            push!(dominating, copy(member))
            best_loss = member.loss
        end
    end
    return dominating
end

"""Backward-compatible API: compute the Pareto frontier of a HallOfFame.

This preserves the historical behavior (dominance based on
`(complexity, loss)`), and does not require passing a `Dataset`.
"""
calculate_pareto_frontier(hallOfFame::HallOfFame) = dominating_members(hallOfFame)

function _sync_best_member!(hof::HallOfFame{T,L,N,PM}, complexity) where {T,L,N,PM}
    bucket = hof.cells[complexity]
    if isempty(bucket)
        hof.exists[complexity] = false
        return nothing
    end
    best = nothing
    for member in values(bucket)
        best = if best === nothing || member.cost < best.cost
            member
        else
            best
        end
    end
    hof.members[complexity] = copy(best)
    hof.exists[complexity] = true
    return nothing
end

"""Update a hall of fame with a single population member."""
function update_hall_of_fame!(
    hall_of_fame::HallOfFame, member::AbstractPopMember, options::AbstractOptions
)
    size = compute_complexity(member, options)
    valid_size = 0 < size <= options.maxsize
    valid_size || return nothing

    check_constraints(member.tree, options, options.maxsize, size) || return nothing

    key = hof_key(hall_of_fame.criteria, member, options)
    if key === nothing
        @error("`hof_key` returned `nothing`; skipping update")
        return nothing
    end
    key[1] == size ||
        throw(ArgumentError("HallOfFame criteria must produce key[1] == complexity"))

    slot = hall_of_fame.cells[size]
    old = get(slot, key, nothing)
    if old === nothing || member.cost < old.cost
        slot[key] = copy(member)
        _sync_best_member!(hall_of_fame, size)
    end
    return nothing
end

"""Update a hall of fame with a collection of population members."""
function update_hall_of_fame!(hall_of_fame::HallOfFame, members, options::AbstractOptions)
    for member in members
        update_hall_of_fame!(hall_of_fame, member, options)
    end
    return nothing
end

let header_parts = (
        rpad(styled"{bold:{underline:Complexity}}", 10),
        rpad(styled"{bold:{underline:Loss}}", 9),
        rpad(styled"{bold:{underline:Score}}", 9),
        styled"{bold:{underline:Equation}}",
    )
    @eval const HEADER = join($(header_parts), "  ")
    @eval const HEADER_WITHOUT_SCORE = join($(header_parts[[1, 2, 4]]), "  ")
end

show_score_column(options::AbstractOptions) = options.loss_scale == :log

function string_dominating_pareto_curve(
    hallOfFame, dataset, options; width::Union{Integer,Nothing}=nothing, pretty::Bool=true
)
    terminal_width = (width === nothing) ? 100 : max(100, width::Integer)
    buffer = AnnotatedIOBuffer(IOBuffer())
    println(buffer, '─'^(terminal_width - 1))
    if show_score_column(options)
        println(buffer, HEADER)
    else
        println(buffer, HEADER_WITHOUT_SCORE)
    end

    formatted = format_hall_of_fame(hallOfFame, options)
    for (tree, score, loss, complexity) in
        zip(formatted.trees, formatted.scores, formatted.losses, formatted.complexities)
        eqn_string = string_tree(
            tree,
            options;
            display_variable_names=dataset.display_variable_names,
            X_sym_units=dataset.X_sym_units,
            y_sym_units=dataset.y_sym_units,
            pretty,
        )
        prefix = make_prefix(tree, options, dataset)
        eqn_string = prefix * eqn_string
        stats_columns_string = if show_score_column(options)
            @sprintf("%-10d  %-8.3e  %-8.3e  ", complexity, loss, score)
        else
            @sprintf("%-10d  %-8.3e  ", complexity, loss)
        end
        left_cols_width = length(stats_columns_string)
        print(buffer, stats_columns_string)
        print(
            buffer,
            wrap_equation_string(
                eqn_string, left_cols_width + length(prefix), terminal_width
            ),
        )
    end
    print(buffer, '─'^(terminal_width - 1))
    return dump_buffer(buffer)
end
function make_prefix(::AbstractExpression, ::AbstractOptions, dataset::Dataset)
    y_prefix = dataset.y_variable_name
    unit_str = format_dimensions(dataset.y_sym_units)
    y_prefix *= unit_str
    if dataset.y_sym_units === nothing && dataset.X_sym_units !== nothing
        y_prefix *= WILDCARD_UNIT_STRING
    end
    return y_prefix * " = "
end

function wrap_equation_string(eqn_string, left_cols_width, terminal_width)
    dots = "..."
    equation_width = (terminal_width - 1) - left_cols_width - length(dots)

    buffer = AnnotatedIOBuffer(IOBuffer())

    forced_split_eqn = split(eqn_string, '\n')
    print_pad = false
    for piece in forced_split_eqn
        subpieces = split_string(piece, equation_width)
        for (i, subpiece) in enumerate(subpieces)
            # We don't need dots on the last subpiece, since it
            # is either the last row of the entire string, or it has
            # an explicit newline in it!
            requires_dots = i < length(subpieces)
            print(buffer, ' '^(print_pad * left_cols_width))
            print(buffer, subpiece)
            if requires_dots
                print(buffer, dots)
            end
            println(buffer)
            print_pad = true
        end
    end
    return dump_buffer(buffer)
end

function format_hall_of_fame(hof::HallOfFame{T,L}, options) where {T,L}
    dominating = calculate_pareto_frontier(hof)

    # Only check for negative losses if using logarithmic scaling
    options.loss_scale == :log && for member in dominating
        if member.loss < 0.0
            throw(
                DomainError(
                    member.loss,
                    "Your loss function must be non-negative. To allow negative losses, set the `loss_scale` to linear, or consider wrapping your loss inside an exponential.",
                ),
            )
        end
    end

    trees = [member.tree for member in dominating]
    losses = [member.loss for member in dominating]
    complexities = [compute_complexity(member, options) for member in dominating]
    scores = Array{L}(undef, length(dominating))

    cur_loss = typemax(L)
    last_loss = cur_loss
    last_complexity = zero(eltype(complexities))

    for i in 1:length(dominating)
        complexity = complexities[i]
        cur_loss = losses[i]
        delta_c = complexity - last_complexity
        scores[i] = if i == 1
            zero(L)
        else
            if options.loss_scale == :linear
                compute_direct_score(cur_loss, last_loss, delta_c)
            else
                compute_zero_centered_score(cur_loss, last_loss, delta_c)
            end
        end
        last_loss = cur_loss
        last_complexity = complexity
    end
    return (; trees, scores, losses, complexities)
end
function compute_direct_score(cur_loss, last_loss, delta_c)
    delta = cur_loss - last_loss
    return relu(-delta / delta_c)
end
function compute_zero_centered_score(cur_loss, last_loss, delta_c)
    log_ratio = log(relu(cur_loss / last_loss) + eps(cur_loss))
    return relu(-log_ratio / delta_c)
end

function format_hall_of_fame(hof::AbstractVector{<:HallOfFame}, options)
    outs = [format_hall_of_fame(h, options) for h in hof]
    return (
        trees=[out.trees for out in outs],
        scores=[out.scores for out in outs],
        losses=[out.losses for out in outs],
        complexities=[out.complexities for out in outs],
    )
end
# TODO: Re-use this in `string_dominating_pareto_curve`

end
