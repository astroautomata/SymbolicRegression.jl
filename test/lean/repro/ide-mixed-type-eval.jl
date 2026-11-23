using SymbolicRegression
using DynamicExpressions: eval_tree_array

# InterfaceDynamicExpressions.jl:91,110,122 assert the data's element type,
# while DE promotes the tree and data element types before returning.
options = Options(; binary_operators=[+])
tree = Node(Float64; val=1.0)
X = ones(Float32, 1, 2)
expected, complete = eval_tree_array(tree, X, options.operators)
@assert complete
@assert expected isa Vector{Float64}
@assert expected == [1.0, 1.0]
err = try
    eval_tree_array(tree, X, options)
    nothing
catch e
    e
end
println(
    "direct DE output type=",
    typeof(expected),
    "; SR wrapper=",
    typeof(err),
    "; error=",
    sprint(showerror, err),
)
@assert err isa TypeError
println("REPRODUCED ide-mixed-type-eval")
