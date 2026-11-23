using SymbolicRegression
using SymbolicRegression: Dataset, test_dataset_configuration

X = reshape([1.0, 2.0, 3.0], 1, :)
dataset = Dataset(X, zeros(3); weights=[1.0])
options = Options(; binary_operators=[+])
result = test_dataset_configuration(dataset, options, 0)
@assert dataset.n == 3 && length(dataset.weights) == 1
@assert result === nothing
println(
    "test_dataset_configuration accepted n=3 with one weight; expected dimension rejection"
)
println("REPRODUCED cfg-weights-shape")
println("REPRODUCED cfg-dataset-acceptance")
