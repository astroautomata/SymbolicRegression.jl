# Reproducer for registry entry `tmpl-create-independent` (SymReg/Templates/Builder.lean).
# The generic extra_init_params returns options.expression_options itself
# (src/ExpressionBuilder.jl:84-93, "TODO: Potential aliasing here"), so every DE
# ParametricExpression created from one Options object holds the same parameter matrix.
using SymbolicRegression
using SymbolicRegression: create_expression
using DynamicExpressions: ParametricExpression, ParametricNode, get_metadata

P = ones(1, 2)
opts = Options(;
    binary_operators=(+,),
    expression_type=ParametricExpression,
    node_type=ParametricNode,
    expression_options=(; parameters=P, parameter_names=["p"]),
)
ds = Dataset(randn(1, 5), randn(5))
a = create_expression(1.0, opts, ds)
b = create_expression(2.0, opts, ds)
get_metadata(a).parameters[1, 1] = 42.0
println(
    "a and b share the parameter matrix: ",
    get_metadata(a).parameters === get_metadata(b).parameters,
)
println(
    "after writing 42.0 into a's parameters: b[1,1] = ",
    get_metadata(b).parameters[1, 1],
    ", options matrix P[1,1] = ",
    P[1, 1],
    "  (expected 1.0)",
)
if get_metadata(a).parameters === get_metadata(b).parameters &&
    get_metadata(b).parameters[1, 1] == 42.0
    println("REPRODUCED tmpl-create-independent")
end
