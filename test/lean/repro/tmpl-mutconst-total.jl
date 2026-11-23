# Reproducer for registry entry `tmpl-mutconst-total` (SymReg/Templates/TemplateInit.lean).
# A template with a zero-length parameter vector is accepted by TemplateStructure and the
# constructor, but mutate_constant's parameter branch draws rand(rng, 1:num_params)
# (src/TemplateExpression.jl:1093), which throws on the empty range.
using SymbolicRegression
using SymbolicRegression: ComposableExpression, TemplateExpression, TemplateStructure
using SymbolicRegression.MutationFunctionsModule: mutate_constant
using SymbolicRegression.CoreModule: ConstantMutation
using DynamicExpressions: Node, OperatorEnum, get_metadata
using Random

operators = OperatorEnum(1 => (sin,), 2 => (+, *))
st = TemplateStructure{(:f,),(:p,)}(
    ((; f), (; p), (a,)) -> f(a); num_features=(; f=1), num_parameters=(; p=0)
)
ex = TemplateExpression(
    (; f=ComposableExpression(Node{Float64}(; feature=1); operators));
    structure=st,
    operators,
)
println("template built, parameters = ", get_metadata(ex).parameters)
opts = Options(;
    binary_operators=(+, *), expression_spec=TemplateExpressionSpec(; structure=st)
)
err = try
    mutate_constant(ex, 1.0, opts, ConstantMutation(), MersenneTwister(0))
    nothing
catch e
    e
end
println(
    "mutate_constant -> ",
    err === nothing ? "ok" : sprint(showerror, err),
    "  (expected a mutated template)",
)
if err isa ArgumentError
    println("REPRODUCED tmpl-mutconst-total")
end
