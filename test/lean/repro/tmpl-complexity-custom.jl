# Reproducer for registry entry `tmpl-complexity-custom` (SymReg/Templates/TemplateOps.lean).
# compute_complexity(::TemplateExpression) sums compute_complexity over the inner expressions
# (src/TemplateExpression.jl:707-716), so a user complexity function is never called on the
# template, only on each inner ComposableExpression.
using SymbolicRegression
using SymbolicRegression:
    ComposableExpression, TemplateExpression, TemplateStructure, compute_complexity
using DynamicExpressions: Node

st = TemplateStructure{(:f, :g)}(((; f, g), (a,)) -> f(a) + g(a); num_features=(; f=1, g=1))
seen = Type[]
cfun(ex) = (push!(seen, typeof(ex)); ex isa TemplateExpression ? 1 : 1000)
opts = Options(;
    binary_operators=(+, *),
    complexity_mapping=cfun,
    expression_spec=TemplateExpressionSpec(; structure=st),
)
x1 = ComposableExpression(Node{Float64}(; feature=1); operators=opts.operators)
ex = TemplateExpression((; f=x1, g=x1); structure=st, operators=opts.operators)
c = compute_complexity(ex, opts)
println("complexity_mapping returns 1 for a TemplateExpression and 1000 otherwise")
println("compute_complexity(template) = ", c, "  (expected 1)")
println("argument types seen: ", unique(nameof.(seen)))
if c == 2000 && all(T -> T <: ComposableExpression, seen)
    println("REPRODUCED tmpl-complexity-custom")
end
