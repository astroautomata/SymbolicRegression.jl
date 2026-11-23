# Reproducer for registry entry `tmpl-crossover-valid` (SymReg/Templates/TemplateMut.lean).
# crossover_trees(::TemplateExpression) samples a key independently in each parent
# (src/TemplateExpression.jl:1003-1004), so a subtree of `g` (two features) can land in `f`
# (one feature), giving a child with invalid variables from two valid parents.
using SymbolicRegression
using SymbolicRegression: ComposableExpression, TemplateExpression, TemplateStructure
using SymbolicRegression.TemplateExpressionModule: has_invalid_variables
using SymbolicRegression.MutationFunctionsModule: crossover_trees
using DynamicExpressions: Node, OperatorEnum, get_contents, get_tree
using Random

operators = OperatorEnum(1 => (sin,), 2 => (+, *))
st = TemplateStructure{(:f, :g)}(
    ((; f, g), (a, b)) -> f(a) + g(a, b); num_features=(; f=1, g=2)
)
function make()
    TemplateExpression(
        (;
            f=ComposableExpression(Node{Float64}(; feature=1); operators),
            g=ComposableExpression(Node{Float64}(; feature=2); operators),
        );
        structure=st,
        operators,
    )
end
p1, p2 = make(), make()
println("parents valid: ", !has_invalid_variables(p1), " ", !has_invalid_variables(p2))
found = false
for seed in 1:200
    c1, c2 = crossover_trees(p1, p2, MersenneTwister(seed))
    if has_invalid_variables(c1) || has_invalid_variables(c2)
        bad = has_invalid_variables(c1) ? c1 : c2
        println(
            "seed $seed: child f = ",
            get_tree(get_contents(bad).f),
            ", g = ",
            get_tree(get_contents(bad).g),
            "  (f may only use x1)",
        )
        global found = true
        break
    end
end
if found
    println("REPRODUCED tmpl-crossover-valid")
end
