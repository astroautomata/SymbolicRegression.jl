using SymbolicRegression
using SymbolicRegression.ProgressBarsModule: format_for_meter

caught = try
    format_for_meter(("label", "a\nb"), 3)
    nothing
catch e
    e
end
@assert caught isa ArgumentError
@assert caught.msg == "can't repeat a character -7 times"
println(
    "format_for_meter((\"label\", \"a\\nb\"), 3) threw ",
    repr(caught),
    "; expected a formatted value at positive width",
)
println("REPRODUCED pbar-narrow-multiline")
