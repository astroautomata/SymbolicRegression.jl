# Reproducer for registry entry `tmpl-parse-accepts` (SymReg/Templates/Macro.lean).
# parse_expression(::NamedTuple) parses each inner string on its own
# (src/TemplateExpression.jl:1406-1424); a string with a Float64 literal gives Node{Float64}
# and one without literals Node{Float32}, so the template constructor has no method.
using SymbolicRegression
using DynamicExpressions: DynamicExpressions as DE, OperatorEnum

operators = OperatorEnum(1 => (sin,), 2 => (+, *))
spec = @template_spec(expressions = (f, g)) do x, y
    f(x) + g(y)
end
outcome(guess) =
    try
        DE.parse_expression(guess; expression_spec=spec, operators)
    catch e
        e
    end
both = outcome((; f="#1 + 1.0", g="sin(#1) * 2.0"))
mixed = outcome((; f="#1 + 1.0", g="sin(#1)"))
println(
    "guess (f=\"#1 + 1.0\", g=\"sin(#1) * 2.0\") -> ",
    both isa Exception ? typeof(both) : typeof(both).name.name,
)
println(
    "guess (f=\"#1 + 1.0\", g=\"sin(#1)\")       -> ",
    mixed isa Exception ? typeof(mixed) : typeof(mixed).name.name,
    "  (expected a TemplateExpression)",
)
if !(both isa Exception) && mixed isa MethodError
    println("REPRODUCED tmpl-parse-accepts")
end
