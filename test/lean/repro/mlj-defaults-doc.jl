# Reproducer for registry entry `mlj-defaults-doc` (SymReg/MLJ/FitProps.lean).
# The hyper-parameter docstring (src/MLJInterface.jl:808) says `niterations::Int=10`,
# but modelexpr builds SRRegressor and MultitargetSRRegressor with default 100
# (src/MLJInterface.jl:68,129-130).
using SymbolicRegression
using SymbolicRegression.MLJInterfaceModule: SRRegressor, MultitargetSRRegressor

doc = string(@doc SRRegressor)
i = findfirst("`niterations::Int=", doc)
documented = doc[i[1]:(i[1] + 20)]
println("docstring: ", documented)
println(
    "SRRegressor().niterations = ",
    SRRegressor().niterations,
    ", MultitargetSRRegressor().niterations = ",
    MultitargetSRRegressor().niterations,
)
if occursin("=10`", documented) && SRRegressor().niterations == 100
    println("REPRODUCED mlj-defaults-doc")
end
