# Reproducer for registry entry `tmpl-set-mismatch-atomic` (SymReg/Templates/ConstantsProps.lean).
# set_scalar_constants! on a TemplateExpression with a too-short vector writes the inner
# constants and the first parameter before throwing (src/TemplateExpression.jl:468-484).
using SymbolicRegression
using SymbolicRegression: ComposableExpression, TemplateExpression, TemplateStructure
using DynamicExpressions: Node, OperatorEnum, get_scalar_constants, set_scalar_constants!

operators = OperatorEnum(1 => (sin,), 2 => (+, *))
c1 = ComposableExpression(Node{Float64}(; val=2.0); operators)
c2 = ComposableExpression(Node{Float64}(; val=3.0); operators)
st = TemplateStructure{(:f, :g),(:p,)}(
    ((; f, g), (; p), (a,)) -> f(a) + g(a) + p[1];
    num_features=(; f=1, g=1),
    num_parameters=(; p=2),
)
ex = TemplateExpression(
    (; f=c1, g=c2); structure=st, operators, parameters=(; p=[5.0, 7.0])
)
before, refs = get_scalar_constants(ex)
err = try
    set_scalar_constants!(ex, [1.0, 2.0, 3.0], refs)
    nothing
catch e
    e
end
after = get_scalar_constants(ex)[1]
println("constants before:        ", before)
println("set with [1.0, 2.0, 3.0] threw: ", typeof(err))
println("constants after the throw: ", after, "  (expected unchanged ", before, ")")
if err isa BoundsError && after == [1.0, 2.0, 3.0, 7.0]
    println("REPRODUCED tmpl-set-mismatch-atomic")
end
