# Reproducer for registry entry `tmpl-embed-create` (SymReg/Templates/Builder.lean).
# create_expression(..., Val(true)) gives every inner expression of a template the dataset's
# variable names (src/TemplateExpression.jl:605), but embed_metadata only rewrites the template
# metadata (src/ExpressionBuilder.jl:105-109), so embedding a created template differs from
# creating it embedded.
using SymbolicRegression
using SymbolicRegression: TemplateStructure, create_expression
using SymbolicRegression.ExpressionBuilderModule: embed_metadata
using DynamicExpressions: Node, get_contents, get_metadata

st = TemplateStructure{(:f, :g)}(((; f, g), (a,)) -> f(a) + g(a); num_features=(; f=1, g=1))
opts = Options(;
    binary_operators=(+, *), expression_spec=TemplateExpressionSpec(; structure=st)
)
ds = Dataset(randn(1, 5), randn(5); variable_names=["z"])
t = Node{Float64}(; val=1.5)
embedded = embed_metadata(create_expression(t, opts, ds), opts, ds)
created = create_expression(t, opts, ds, Val(true))
inner_names(ex) = map(e -> get_metadata(e).variable_names, values(get_contents(ex)))
println(
    "template variable_names: embedded=",
    get_metadata(embedded).variable_names,
    " created=",
    get_metadata(created).variable_names,
)
println("inner variable_names after embed_metadata:   ", inner_names(embedded))
println(
    "inner variable_names from create(Val(true)): ",
    inner_names(created),
    "  (expected equal)",
)
if all(isnothing, inner_names(embedded)) && all(==(["z"]), inner_names(created))
    println("REPRODUCED tmpl-embed-create")
end
