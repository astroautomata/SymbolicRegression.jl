using SymbolicRegression
using SymbolicRegression: Dataset, PopMember, Node
using SymbolicRegression.CoreModule: SubDataset
using SymbolicRegression.ConstantOptimizationModule: _optimize_constants
using Random: MersenneTwister

const Optim = SymbolicRegression.ConstantOptimizationModule.Optim

function check_fraction(dataset, expected_fraction)
    calls = Ref(0)
    objective = function (ex, data, options)
        calls[] += 1
        return 1.0
    end
    options = Options(;
        binary_operators=[+],
        deterministic=true,
        optimizer_nrestarts=2,
        autodiff_backend=nothing,
        loss_function_expression=objective,
    )
    member = PopMember(dataset, Node(Float64; val=1.0), options; deterministic=true)
    calls[] = 0
    returned, reported = _optimize_constants(
        dataset,
        member,
        options,
        Optim.NelderMead(),
        Optim.Options(; iterations=0),
        MersenneTwister(17),
    )
    actual = calls[] * expected_fraction
    println(
        "fraction = ",
        expected_fraction,
        "; actual loss calls = ",
        calls[],
        "; reported full-data evaluations = ",
        reported,
        "; expected = ",
        actual,
        "; missing = ",
        actual - reported,
    )
    @assert returned === member
    @assert actual - reported == expected_fraction
    return actual > reported
end

dataset = Dataset(reshape([1.0, 2.0, 3.0, 4.0], 1, :), zeros(4))
full_ok = check_fraction(dataset, 1.0)
batch_ok = check_fraction(SubDataset(dataset, [1, 2]), 0.5)
if full_ok && batch_ok
    println("REPRODUCED copt-eval-accounting")
end
