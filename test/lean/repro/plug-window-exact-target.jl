using SymbolicRegression
using SymbolicRegression.AdaptiveParsimonyModule: RunningSearchStatistics, move_window!

s = RunningSearchStatistics(2, [1.0000001, 3.0], [0.5, 0.5])
println("window = ", s.window_size, "; initial counts = ", s.frequencies)
move_window!(s)
println(
    "actual counts = ",
    s.frequencies,
    "; actual sum = ",
    sum(s.frequencies),
    "; expected sum = ",
    s.window_size,
)
@assert all(>=(1), s.frequencies)
@assert sum(s.frequencies) > s.window_size + 1
println("REPRODUCED plug-window-exact-target")
