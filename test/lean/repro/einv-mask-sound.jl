using SymbolicRegression
using DynamicExpressions
const SR = SymbolicRegression
const EI = SR.EvaluateInverseModule

# Tree x1 / x2 on the sample x1 = 1, x2 = 0, target y = 3, inverting at x1.
# Fix2(/, 0) has approx_inverse y -> y * 0 = 0, which is finite, so the row is marked valid,
# but substituting x1 = 0 gives 0 / 0 = NaN, not the target 3 (src/EvaluateInverse.jl:102-120).
opts = Options(; binary_operators=[+, *, /], mutations=[BacksolveMutation() => 1.0])
ops = opts.operators
x1 = Node{Float64}(; feature=1)
x2 = Node{Float64}(; feature=2)
tree = Node(; op=findfirst(==(/), ops.binops), children=(x1, x2))
X = reshape([1.0, 0.0], 2, 1)
vals, valid = EI.eval_inverse_tree_array_masked(tree, X, ops, x1, [3.0])
rewritten = Node(;
    op=findfirst(==(/), ops.binops), children=(Node{Float64}(; val=vals[1]), x2)
)
out, _ = eval_tree_array(rewritten, X, ops)
println(
    "inverted value = ", vals[1], ", valid = ", valid[1], ", rewritten tree gives ", out[1]
)
if valid[1] && !(out[1] == 3.0)
    println("REPRODUCED einv-mask-sound")
end
