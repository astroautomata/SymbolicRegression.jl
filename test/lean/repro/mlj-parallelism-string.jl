# Reproducer for registry entry `mlj-parallelism-string` (SymReg/MLJ/FitProps.lean).
# The docstring (src/MLJInterface.jl:810-818) says "You may also pass a string instead of a
# symbol, like \"multithreading\"", but the struct field is `parallelism::Symbol`
# (src/MLJInterface.jl:74), so the keyword constructor rejects a string.
using SymbolicRegression
using SymbolicRegression.MLJInterfaceModule: SRRegressor

result = try
    SRRegressor(; parallelism="serial")
catch e
    e
end
println(
    "SRRegressor(; parallelism=\"serial\") returned: ",
    result isa Exception ? first(sprint(showerror, result), 160) : result.parallelism,
)
println("expected: a model with parallelism = :serial")
if result isa MethodError
    println("REPRODUCED mlj-parallelism-string")
end
