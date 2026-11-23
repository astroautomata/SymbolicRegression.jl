# Reproducer for registry entry `mlj-pred-feature-table` (SymReg/MLJ/PredictProps.lean).
# `_predict` (src/MLJInterface.jl:570-576) treats any NamedTuple with a key `data` or `idx`
# as the `(data=..., idx=...)` selector. A feature table with a column named `data` fits,
# but predicting on the same table throws.
using SymbolicRegression
using SymbolicRegression: machine, fit!, predict
using SymbolicRegression.MLJInterfaceModule: SRTestRegressor
using Random

Random.seed!(0)
X = (; data=randn(30), x2=randn(30))
y = 2 .* X.data
model = SRTestRegressor(;
    binary_operators=[+, *],
    populations=1,
    population_size=20,
    ncycles_per_iteration=10,
    parallelism=:serial,
)
mach = machine(model, X, y)
fit!(mach; verbosity=0)
result = try
    predict(mach, X)
catch e
    e
end
println(
    "predict(mach, X) with columns (:data, :x2) returned: ",
    result isa Exception ? sprint(showerror, result) : result[1:3],
)
println("expected: a vector of 30 predictions")
if result isa AssertionError
    println("REPRODUCED mlj-pred-feature-table")
end
