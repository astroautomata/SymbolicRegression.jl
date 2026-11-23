using SymbolicRegression
const IF = SymbolicRegression.InverseFunctionsModule

# The approx_inverse docstring (src/InverseFunctions.jl:13-20) says `abs` has an approx_inverse
# of `abs`, but the method table returns `nothing` for it (src/InverseFunctions.jl:114).
g = IF.approx_inverse(abs)
println("approx_inverse(abs) = ", repr(g))
if g === nothing
    println("REPRODUCED inv-doc-local")
end
