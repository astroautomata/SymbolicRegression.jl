using SymbolicRegression
using SymbolicRegression: Dataset

plain = Dataset(reshape([1.0, 2.0], 1, :), [2.0, 4.0])
weighted = Dataset(reshape([1.0, 2.0], 1, :), [2.0, 4.0]; weights=[1.0, 3.0])
println(
    "plain avg_y=",
    plain.avg_y,
    " expected=3.0; weighted avg_y=",
    weighted.avg_y,
    " expected=3.5; eltype(y) isa Number=",
    eltype(plain.y) isa Number,
)
if plain.avg_y === nothing && weighted.avg_y === nothing
    println("REPRODUCED loss-dataset-average")
end
