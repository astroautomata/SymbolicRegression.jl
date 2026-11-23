using SymbolicRegression
using DynamicExpressions
const SR = SymbolicRegression
const BS = SR.BacksolveModule

# greedy_forward_selection_gram claims invariance to the scale of y (src/Backsolve.jl:184-187),
# but success is the absolute test any(abs.(coefficients) .> 100 eps) (src/Backsolve.jl:264).
# The one-column fit y = x scaled by eps() keeps the coefficient eps() yet reports failure.
kw = (; term_costs=[1], join_cost=1, budget=nothing, max_terms=1, min_improvement=1e-3)
G = reshape([1.0], 1, 1)
c1, ok1 = BS.greedy_forward_selection_gram(G, [1.0], 1.0; kw...)
s = eps()
c2, ok2 = BS.greedy_forward_selection_gram(G, [s], s^2; kw...)
println("y = x: ", (c1, ok1), "; y = eps() * x: ", (c2, ok2))

# End to end: fit_sparse_expression fits y = 2 x1 but returns nothing for y = 2e-15 x1.
opts = Options(; binary_operators=[+, *], mutations=[BacksolveMutation() => 1.0])
x1 = Node{Float64}(; feature=1)
xs = collect(1.0:20.0)
ds = SR.Dataset(reshape(xs, 1, :), 2 .* xs)
big = BS.fit_sparse_expression(x1, 2 .* xs, ds, opts, 1)
small = BS.fit_sparse_expression(
    x1, 2e-15 .* xs, SR.Dataset(reshape(xs, 1, :), 2e-15 .* xs), opts, 1
)
println(
    "fit of 2 x1: ",
    big === nothing ? "nothing" : string_tree(big, opts),
    "; fit of 2e-15 x1: ",
    small === nothing ? "nothing" : string_tree(small, opts),
)
if ok1 && !ok2 && c2[1] == s && big !== nothing && small === nothing
    println("REPRODUCED bs-greedy-scale")
end
