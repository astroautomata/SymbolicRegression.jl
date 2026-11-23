# Reproducer for registry entry `mutgen-sample-infinite` (SymReg/MutateGen/SampleProps.lean).
# _sample_mutation (src/Mutate.jl:247-262) accepts an infinite weight (Inf >= 0.0), so the
# threshold rand() * total is Inf (or NaN when rand() == 0.0), no running sum exceeds it,
# and the fallback `lastindex(mutations)` returns the last entry even when its weight is 0.
# Finite weights whose sum overflows behave the same way.
using SymbolicRegression
using SymbolicRegression.MutateModule: _sample_mutation

inf_choice = _sample_mutation([:operator => Inf, :constant => 0.0])
overflow_choice = _sample_mutation([
    :operator => 1e308, :feature => 1e308, :constant => 0.0
])
println(
    "weights [Inf, 0.0] -> index ",
    inf_choice,
    "; weights [1e308, 1e308, 0.0] -> index ",
    overflow_choice,
)
if inf_choice == 2 && overflow_choice == 3
    println("REPRODUCED mutgen-sample-infinite")
end

include("plug-adaptive-weights-finite.jl")
