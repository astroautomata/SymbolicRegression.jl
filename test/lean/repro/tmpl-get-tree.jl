# Reproducer for registry entry `tmpl-get-tree` (SymReg/Templates/Template.lean).
# get_tree zips the inner expressions with the max(num_features) variable trees
# (src/TemplateExpression.jl:549-555), so a template with fewer keys than variables passes
# too few variables to its combiner; count_nodes fails the same way.
using SymbolicRegression
using SymbolicRegression: ComposableExpression, TemplateExpression, TemplateStructure
using DynamicExpressions: Node, OperatorEnum, get_tree, count_nodes

operators = OperatorEnum(1 => (sin,), 2 => (+, *))
x1 = ComposableExpression(Node{Float64}(; feature=1); operators)
st = TemplateStructure{(:f,)}(((; f), (a, b)) -> f(a, b))
ex = TemplateExpression((; f=x1); structure=st, operators)
println("num_features = ", st.num_features)
println("evaluation on two rows works: ", ex([1.0 2.0; 3.0 4.0]))
outcome(f) =
    try
        f()
    catch e
        e
    end
t = outcome(() -> get_tree(ex))
n = outcome(() -> count_nodes(ex))
println("get_tree(ex)    = ", t isa Exception ? typeof(t) : t, "  (expected the tree x1)")
println("count_nodes(ex) = ", n isa Exception ? typeof(n) : n, "  (expected 1)")
if t isa BoundsError && n isa BoundsError
    println("REPRODUCED tmpl-get-tree")
end
