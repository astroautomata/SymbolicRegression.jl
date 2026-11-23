using SymbolicRegression
wrapped = SymbolicRegression.HallOfFameModule.wrap_equation_string("abc", 100, 100)
println("wrap_equation_string(\"abc\", 100, 100)=", repr(String(wrapped)))
if isempty(wrapped)
    println("REPRODUCED hof-wrap-retains-equation")
end
