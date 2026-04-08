@testitem "Options docstring attaches to Options constructor" begin
    using SymbolicRegression

    # `Base.Docs.hasdoc` was introduced after Julia 1.10.
    # This replicates the behavior we want for this regression test: check
    # whether a docstring is explicitly attached to the binding.
    hasdoc(mod, sym) = haskey(Base.Docs.meta(mod), Base.Docs.Binding(mod, sym))

    optmod = SymbolicRegression.CoreModule.OptionsModule
    @test hasdoc(optmod, :Options)

    doc = Base.Docs.doc(SymbolicRegression.Options)
    txt = sprint(show, doc)
    @test occursin("Construct options for `equation_search`", txt)

    # Regression: the Options docstring should not attach to effort-scaling constants.
    @test !hasdoc(optmod, :EFFORT_NITERATIONS_EXPONENT)
end
