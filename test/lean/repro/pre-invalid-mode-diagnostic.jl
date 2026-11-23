using SymbolicRegression

caught = try
    SymbolicRegression.do_precompilation(Val(:invalid))
    nothing
catch e
    e
end
@assert caught isa MethodError
@assert caught.f === *
println(
    "\ndo_precompilation(Val(:invalid)) throws ",
    typeof(caught),
    " from string * nothing; expected ErrorException with Invalid value for mode",
)
println("REPRODUCED pre-invalid-mode-diagnostic")
