using SymbolicRegression
using DynamicExpressions
const SR = SymbolicRegression
const EI = SR.EvaluateInverseModule

# Tree 1 / atan(x1), targets [0, 1], inverting at x1. The first inverse step gives 1 / 0 = Inf
# on row 1 (masked invalid) and 1 on row 2 (valid), so the recursion continues and applies
# tan to every row, including Inf: tan(Inf) throws DomainError instead of masking the row
# (src/EvaluateInverse.jl:102-120,297-310).
opts = Options(;
    binary_operators=[+, *, /],
    unary_operators=[atan],
    mutations=[BacksolveMutation() => 1.0],
)
ops = opts.operators
x1 = Node{Float64}(; feature=1)
c1 = Node{Float64}(; val=1.0)
tree = Node(;
    op=findfirst(==(/), ops.binops),
    children=(c1, Node(; op=findfirst(==(atan), ops.unaops), children=(x1,))),
)
X = [2.0 3.0]
r = try
    EI.eval_inverse_tree_array_masked(tree, X, ops, x1, [0.0, 1.0])
catch e
    e
end
println("eval_inverse_tree_array_masked -> ", r)
if r isa DomainError
    println("REPRODUCED einv-no-throw")
end
