using SymbolicRegression
using DynamicExpressions: string_tree

# InterfaceDynamicExpressions.jl:238-244 omits kws... on the default raw branch.
options = Options(; binary_operators=[+])
tree = Node(Float64; val=1.0)
custom = _ -> "CUSTOM"
actual = string_tree(tree, options; f_constant=custom)
expected = string_tree(tree, options.operators; f_constant=custom, pretty=false)
println(
    "raw string_tree with f_constant: actual=", repr(actual), "; expected=", repr(expected)
)
@assert actual == "1.0"
@assert expected == "CUSTOM"
@assert actual != expected
println("REPRODUCED ide-raw-keyword-forward")
