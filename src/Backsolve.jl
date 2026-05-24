module BacksolveModule

using LinearAlgebra: SingularException, norm, pinv
using DispatchDoctor: @unstable
using DynamicExpressions:
    AbstractExpressionNode, constructorof, eval_tree_array, get_tree, string_tree

using ..CoreModule: AbstractOptions, DATA_TYPE, Dataset

const STLSQ_DATA_TYPE = Union{AbstractFloat,Complex{<:AbstractFloat}}

function _solve_library(
    theta::AbstractMatrix{T}, y::AbstractVector{T}
) where {T<:STLSQ_DATA_TYPE}
    try
        return theta \ y
    catch err
        err isa SingularException || rethrow()
        return pinv(theta) * y
    end
end

"""
    BasisLibrary(terms::Vector{N}, evaluated_terms::Matrix{T})

Basis terms and their evaluated values for the sparse-expression fit.
"""
struct BasisLibrary{T,N<:AbstractExpressionNode{T}}
    terms::Vector{N}
    evaluated_terms::Matrix{T}

    function BasisLibrary(
        terms::Vector{N}, evaluated_terms::Matrix{T}
    ) where {T,N<:AbstractExpressionNode{T}}
        size(evaluated_terms, 2) == length(terms) || throw(
            ArgumentError("BasisLibrary requires one evaluated_terms column per term.")
        )
        return new{T,N}(terms, evaluated_terms)
    end
end

"""
    stlsq(theta::AbstractMatrix{T}, y::AbstractVector{T}; lambda::Real, max_iter::Int) -> (coefficients::Vector{T}, success::Bool)

Sequential thresholded least squares for `theta * coefficients ~= y`.

# Arguments
- `theta::AbstractMatrix{T}`: Library matrix (n_samples x n_features)
- `y::AbstractVector{T}`: Target vector (n_samples)
- `lambda::Real`: Sparsification threshold (default: 0.01)
- `max_iter::Int`: Maximum number of iterations (default: 10)

# Returns
- `coefficients::Vector{T}`: Sparse coefficient vector
- `success::Bool`: Whether the algorithm succeeded (false if all coefficients are zero)

# References
- Brunton, S. L., Proctor, J. L., & Kutz, J. N. (2016). Discovering governing equations from data by sparse identification of nonlinear dynamical systems. PNAS, 113(15), 3932-3937.
"""
function stlsq(
    theta::AbstractMatrix{T}, y::AbstractVector{T}; lambda::Real=0.01, max_iter::Int=10
) where {T<:STLSQ_DATA_TYPE}
    n_samples, n_features = size(theta)
    R = typeof(float(real(zero(T))))
    tol = eps(R)
    threshold = R(lambda)

    if length(y) != n_samples
        return zeros(T, n_features), false
    end

    col_norms = vec(sqrt.(sum(abs2, theta; dims=1)))
    col_norms = max.(col_norms, tol)
    theta_normalised = theta ./ col_norms'

    coefficients = _solve_library(theta_normalised, y)

    for iter in 1:max_iter
        small_inds = abs.(coefficients) .< threshold
        active_inds = .!small_inds

        if !any(active_inds)
            return zeros(T, n_features), false
        end

        theta_active = theta_normalised[:, active_inds]
        coefficients_active = _solve_library(theta_active, y)

        coefficients_new = zeros(T, n_features)
        coefficients_new[active_inds] = coefficients_active

        if norm(coefficients_new - coefficients) < tol * 10
            coefficients = coefficients_new
            break
        end
        coefficients = coefficients_new
    end

    coefficients ./= col_norms
    success = any(abs.(coefficients) .> tol * 100)

    return coefficients, success
end

"""
    build_basis_library(
        tree_prototype::AbstractExpressionNode{T},
        dataset::Dataset{T},
        options::AbstractOptions,
        nfeatures::Int,
        population;
        max_library_size::Int=200,
        top_k::Int=10
    ) -> BasisLibrary

Build a basis library from seed terms and population subtrees.

!!! warning
    This API supports an experimental mutation and will change in minor version
    increments.

# Arguments
- `tree_prototype::AbstractExpressionNode{T}`: Prototype node for type information
- `dataset::Dataset{T}`: Dataset containing input features
- `options::AbstractOptions`: Options containing operator definitions
- `nfeatures::Int`: Number of input features
- `population`: Current population to extract subtrees from (duck-typed, must have `.members` and `.n`)
- `max_library_size::Int`: Maximum number of library terms (default: 200).
  Must be at least `1 + nfeatures` to include the constant and feature terms.
- `top_k::Int`: Number of top members to extract subtrees from (default: 10)

# Returns
- `BasisLibrary`: Basis terms and their evaluated values
"""
function build_basis_library(
    tree_prototype::AbstractExpressionNode{T},
    dataset::Dataset{T},
    options::AbstractOptions,
    nfeatures::Int,
    population;
    max_library_size::Int=200,
    top_k::Int=10,
) where {T<:DATA_TYPE}
    min_library_size = 1 + nfeatures
    if max_library_size < min_library_size
        throw(
            ArgumentError(
                "build_basis_library requires max_library_size >= 1 + nfeatures; got max_library_size=$(max_library_size), nfeatures=$(nfeatures).",
            ),
        )
    end

    terms = sizehint!(Vector{typeof(tree_prototype)}(), max_library_size)
    n_samples = size(dataset.X, 2)

    constant_tree = constructorof(typeof(tree_prototype))(; val=one(T))
    push!(terms, constant_tree)

    for i in 1:nfeatures
        feature_tree = constructorof(typeof(tree_prototype))(T; feature=i)
        push!(terms, feature_tree)
    end

    all_subtrees = sizehint!(Vector{typeof(tree_prototype)}(), max_library_size)
    if population !== nothing
        sorted_members = sort(population.members[1:population.n]; by=m -> m.loss)
        top_members = sorted_members[1:min(top_k, length(sorted_members))]
        all_subtrees = mapreduce(
            member -> collect(get_tree(member.tree)), vcat, top_members; init=all_subtrees
        )
    end

    seen_strings = Set{String}()
    unique_subtrees = sizehint!(Vector{typeof(tree_prototype)}(), max_library_size)
    for subtree in all_subtrees
        s = string_tree(subtree, options)
        if !(s in seen_strings)
            push!(seen_strings, s)
            push!(unique_subtrees, subtree)
        end
    end

    n_to_add = min(length(unique_subtrees), max_library_size - length(terms))
    for i in 1:n_to_add
        push!(terms, copy(unique_subtrees[i]))
    end

    evaluated_terms = zeros(T, n_samples, length(terms))
    valid_terms = sizehint!(Vector{typeof(tree_prototype)}(), length(terms))
    col = 0

    for term in terms
        evaluated_values, eval_success = eval_tree_array(term, dataset.X, options.operators)

        if eval_success && !any(isnan, evaluated_values) && !any(isinf, evaluated_values)
            col += 1
            evaluated_terms[:, col] = evaluated_values
            push!(valid_terms, term)
        end
    end
    evaluated_terms = evaluated_terms[:, 1:col]

    return BasisLibrary(valid_terms, evaluated_terms)
end

function _has_weighted_sum_operators(options::AbstractOptions)::Bool
    return (+) in options.operators.binops && (*) in options.operators.binops
end

"""
    combine_trees_weighted_sum(
        trees::Vector{N},
        coefficients::Vector{T},
        options::AbstractOptions
    ) -> Union{N, Nothing}

Combine expression terms into a weighted sum.

!!! warning
    This API supports an experimental mutation and will change in minor version
    increments.

# Arguments
- `trees::Vector{N}`: Vector of expression trees to combine
- `coefficients::Vector{T}`: Coefficients for each tree
- `options::AbstractOptions`: Options containing operator definitions

# Returns
- Combined expression tree, or `nothing` if combination fails

"""
@unstable function combine_trees_weighted_sum(
    trees::Vector{N}, coefficients::Vector{T}, options::AbstractOptions
)::Union{Nothing,N} where {T<:STLSQ_DATA_TYPE,N<:AbstractExpressionNode{T}}
    _has_weighted_sum_operators(options) || return nothing
    add_idx = something(findfirst(op -> op === (+), options.operators.binops))
    mult_idx = something(findfirst(op -> op === (*), options.operators.binops))

    R = typeof(float(real(zero(T))))
    tol = eps(R)

    active_indices = findall(abs.(coefficients) .> tol * 100)

    isempty(active_indices) && return nothing

    active_trees = trees[active_indices]
    active_coeffs = coefficients[active_indices]

    if length(active_indices) == 1
        tree = active_trees[1]
        coeff = active_coeffs[1]

        if abs(coeff - one(T)) < tol * 100
            return tree
        end

        coeff_node = constructorof(typeof(tree))(; val=coeff)
        return constructorof(typeof(tree))(; op=mult_idx, children=(coeff_node, tree))
    end

    weighted_trees = sizehint!(Vector{N}(), length(active_trees))
    for (tree, coeff) in zip(active_trees, active_coeffs)
        if abs(coeff - one(T)) < tol * 100
            push!(weighted_trees, tree)
        else
            coeff_node = constructorof(typeof(tree))(; val=coeff)
            weighted = constructorof(typeof(tree))(;
                op=mult_idx, children=(coeff_node, tree)
            )
            push!(weighted_trees, weighted)
        end
    end

    result = weighted_trees[1]
    for i in 2:length(weighted_trees)
        result = constructorof(typeof(result))(;
            op=add_idx, children=(result, weighted_trees[i])
        )
    end

    return result
end

"""
    fit_sparse_expression(
        tree_prototype::AbstractExpressionNode{T},
        target_values::AbstractVector{T},
        dataset::Dataset{T},
        options::AbstractOptions,
        nfeatures::Int;
        population_for_backsolve=nothing
    ) -> Union{AbstractExpressionNode{T}, Nothing}

Fit a sparse expression to backsolved target values.

!!! warning
    This API supports an experimental mutation and will change in minor version
    increments.

Returns `nothing` immediately if `+` and `*` are not both present in the
operator set, since the output is structurally a weighted sum.

# Arguments
- `tree_prototype`: Prototype node for creating trees
- `target_values`: Target values to fit
- `dataset`: Dataset containing input features
- `options`: Options containing operator definitions and backsolve configuration
- `nfeatures`: Number of input features
- `population_for_backsolve`: Optional population used to extract basis
  terms for the backsolve mutation.

# Returns
- Fitted expression tree, or `nothing` if fitting fails
"""
@unstable function fit_sparse_expression(
    tree_prototype::AbstractExpressionNode{T},
    target_values::AbstractVector{T},
    dataset::Dataset{T},
    options::AbstractOptions,
    nfeatures::Int;
    population_for_backsolve=nothing,
) where {T<:STLSQ_DATA_TYPE}
    _has_weighted_sum_operators(options) || return nothing
    backsolve_options = options.backsolve

    basis = build_basis_library(
        tree_prototype,
        dataset,
        options,
        nfeatures,
        population_for_backsolve;
        max_library_size=backsolve_options.max_library_size,
    )

    coefficients, stlsq_success = stlsq(
        basis.evaluated_terms,
        target_values;
        lambda=backsolve_options.lambda,
        max_iter=backsolve_options.max_iter,
    )

    if !stlsq_success
        return nothing
    end

    result_tree = combine_trees_weighted_sum(basis.terms, coefficients, options)
    result_tree === nothing && return nothing

    predicted, eval_success = eval_tree_array(result_tree, dataset.X, options.operators)

    if !eval_success || any(isnan, predicted) || any(isinf, predicted)
        return nothing
    end

    return result_tree
end

end
