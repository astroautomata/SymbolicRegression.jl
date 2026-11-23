using SymbolicRegression
const OM = SymbolicRegression.CoreModule.OptionsModule
const expected = Dict(
    :ConstantMutation => 0.0353,
    :OperatorMutation => 3.63,
    :FeatureMutation => 0.1,
    :SwapOperandsMutation => 0.00608,
    :RotateTreeMutation => 1.42,
    :AddNodeMutation => 0.0771,
    :InsertNodeMutation => 2.44,
    :DeleteNodeMutation => 0.369,
    :SimplifyMutation => 0.00148,
    :RandomizeMutation => 0.00695,
    :DoNothingMutation => 0.431,
    :OptimizeMutation => 0.0,
    :BacksolveMutation => 0.0,
    :FormConnectionMutation => 0.5,
    :BreakConnectionMutation => 0.1,
)
@assert occursin("ConstantMutation() => 0.0353", OM.OPTION_DESCRIPTIONS)
options = Options(; define_helper_functions=false)
actual = Dict(
    nameof(typeof(mutation)) => weight for (mutation, weight) in options.mutations
)
mismatches = sort!([name for name in keys(expected) if actual[name] != expected[name]])
for name in mismatches
    println(name, ": actual=", actual[name], " expected(docstring)=", expected[name])
end
@assert actual[:ConstantMutation] == 0.0346
@assert actual[:ConstantMutation] != expected[:ConstantMutation]
@assert length(mismatches) == 10
println("REPRODUCED opts-doc-mutation-defaults")
