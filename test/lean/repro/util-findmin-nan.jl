using SymbolicRegression
using SymbolicRegression.CoreModule.UtilsModule: findmin_fast
x = [1.0, NaN, 0.0]
actual, expected = findmin_fast(x), findmin(x)
println("input=", x, " actual=", actual, " expected=", expected)
@assert isequal(actual, (0.0, 3))
@assert isequal(expected, (NaN, 2))
println("REPRODUCED util-findmin-nan")
