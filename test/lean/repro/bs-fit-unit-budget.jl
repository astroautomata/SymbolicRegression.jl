using SymbolicRegression
using SymbolicRegression.BacksolveModule: combine_trees_weighted_sum, fit_sparse_expression

x = collect(1.0:12.0)
X = reshape(x, 1, :)
options = Options(; binary_operators=[+, *])
dataset = Dataset(X, copy(x))
feature = Node(Float64; feature=1)
mask = trues(length(x))
mutation = BacksolveMutation()
exact = combine_trees_weighted_sum([feature], [1.0], options)
values, valid = eval_tree_array(exact, X, options.operators)
@assert valid && values == x && compute_complexity(exact, options) == 1

fit = fit_sparse_expression(
    feature,
    x,
    dataset,
    options,
    1;
    backsolve_options=mutation,
    valid_mask=mask,
    max_complexity=1,
)
if isnothing(fit)
    println(
        "exact unit-coefficient fit has complexity=1 on 12 valid rows; fit returned nothing"
    )
    println("REPRODUCED bs-fit-unit-budget")
else
    error("The in-budget exact fit was not missed")
end
