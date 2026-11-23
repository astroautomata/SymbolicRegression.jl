using SymbolicRegression
using DynamicExpressions: string_tree, print_tree

# InterfaceDynamicExpressions.jl:335,343 dispatch directly to the DE printer,
# bypassing the SR variable formatter at lines 282-286.
options = Options(; binary_operators=[+])
tree = Node(Float64; feature=1)
expected = string_tree(tree, options; pretty=true) * "\n"
io = IOBuffer()
returned = print_tree(io, tree, options; pretty=true)
actual = String(take!(io))
println(
    "pretty print_tree: actual=",
    repr(actual),
    "; expected=",
    repr(expected),
    "; return=",
    repr(returned),
)
@assert returned === nothing
@assert actual == "x1\n"
@assert expected == "x₁\n"
@assert actual != expected
println("REPRODUCED ide-print-pretty-consistency")
