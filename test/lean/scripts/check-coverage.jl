using SymbolicRegression

lines = readlines(only(ARGS))
"AUDIT OK" in lines || error("Expected output from a successful Lean audit")
covered_files = Set(
    chopprefix(line, "COVER-FILE ") for line in lines if startswith(line, "COVER-FILE ")
)
covered_fns = Set(
    chopprefix(line, "COVER-FN ") for line in lines if startswith(line, "COVER-FN ")
)

repo_root = realpath(joinpath(@__DIR__, "..", "..", ".."))
realpath(pkgdir(SymbolicRegression)) == repo_root ||
    error("Expected the local SymbolicRegression checkout")
expected_files = Set(
    replace(relpath(joinpath(dir, file), repo_root), '\\' => '/') for
    source in ("src", "ext") for (dir, _, files) in walkdir(joinpath(repo_root, source)) for
    file in files if endswith(file, ".jl")
)
expected_fns = Set(String(n) for n in names(SymbolicRegression) if n != :SymbolicRegression)

for (label, missing) in (
    ("MISSING-FILE", setdiff(expected_files, covered_files)),
    ("MISSING-FN", setdiff(expected_fns, covered_fns)),
    ("UNKNOWN-FILE", setdiff(covered_files, expected_files)),
)
    for item in sort!(collect(missing))
        println(label, ' ', item)
    end
end
println(
    "FILES ", length(intersect(expected_files, covered_files)), '/', length(expected_files)
)
println("EXPORTS ", length(intersect(expected_fns, covered_fns)), '/', length(expected_fns))
isempty(setdiff(covered_files, expected_files)) || exit(1)
