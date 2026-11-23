using SymbolicRegression
using DynamicExpressions: Node, get_tree, get_contents, eval_tree_array

options = SymbolicRegression.Options(; binary_operators=[+])
x = Node(Float64; feature=1)
tree = Node(1, Node(1, x, Node(Float64; val=1.0)), Node(Float64; val=2.0))
inner = SymbolicRegression.ComposableExpression(tree; operators=options.operators)
structure = SymbolicRegression.TemplateStructure{(:f, :g)}(
    ((; f, g), (x,)) -> f(x) + g(x); num_features=(f=1, g=1)
)
ex = SymbolicRegression.TemplateExpression((f=inner, g=inner); structure)
X = reshape([3.0], 1, :)
function values_at(ex)
    [
        first(eval_tree_array(get_tree(e), X, options.operators))[1] for
        e in values(get_contents(ex))
    ]
end
before = values_at(ex)
combined = SymbolicRegression.combine_operators(ex, options.operators)
after = values_at(combined)
println(
    "template f=g=(x1+1)+2 at x1=3: before=",
    before,
    ", after=",
    after,
    "; f+g: ",
    sum(before),
    " -> ",
    sum(after),
)
if before == [6.0, 6.0] && after == [8.0, 8.0]
    println("REPRODUCED simp-template-shared")
end
