using Random
using SymbolicRegression
using SymbolicRegression: Dataset, PopMember
using SymbolicRegression.MutateModule: next_generation
using DynamicExpressions: Node

X = reshape([1.0, 2.0, 3.0], 1, :)
dataset = Dataset(X, vec(X))
options = Options(;
    binary_operators=[+],
    mutations=[RotateTreeMutation() => nextfloat(0.0), DoNothingMutation() => 0.0],
    default_plugins=(),
    default_mutations=[],
)
parent = PopMember(dataset, Node(Float64; feature=1), options; deterministic=false)
state = Random.Xoshiro(0, 1, 2, 0x0000018000000000)
copy!(Random.default_rng(), state)
draw = rand()
copy!(Random.default_rng(), state)
trace = Dict{String,Any}()
_, accepted, count = next_generation(
    dataset, parent, 10, options; tmp_trace=trace, plugin_states=()
)
println(
    "draw = ",
    draw,
    "; mutation = ",
    trace["type"],
    "; accepted = ",
    accepted,
    "; evaluations = ",
    count,
)
if draw == 0.75 && trace["type"] == "identity" && accepted && count == 0.0
    println("REPRODUCED mutgen-ng-sampled-positive")
end
