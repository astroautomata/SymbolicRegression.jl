using SymbolicRegression
const SR = SymbolicRegression
const IF = SR.InverseFunctionsModule

# approx_inverse(Fix2(safe_pow, a)) = Fix2(safe_pow, inv(a)) (src/InverseFunctions.jl:139):
# safe_pow(-2.0, 3.0) = -8.0 is attained, but the inverse sends -8.0 to safe_pow(-8.0, 1/3),
# which is NaN for a negative base with a non-integer exponent, instead of -2.0.
f = Base.Fix2(SR.safe_pow, 3.0)
g = IF.approx_inverse(f)
y = f(-2.0)
x = g(y)
println("safe_pow(-2.0, 3.0) = ", y, "; approx_inverse(...)(", y, ") = ", x)
if y == -8.0 && isnan(x)
    println("REPRODUCED inv-pow-complete")
end
