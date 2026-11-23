using SymbolicRegression
using SymbolicRegression.CoreModule.UtilsModule: bottomk_fast
x = [0.0, Inf]
values, indices = bottomk_fast(x, 2)
println(
    "input=", x, " values=", values, " indices=", indices, " indexed values=", x[indices]
)
@assert values == [0.0, Inf]
@assert indices == [1, 1]
@assert x[indices] != values
println("REPRODUCED util-bottomk-sentinel")
