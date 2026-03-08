@testitem "Options docstring attaches to Options constructor" begin
    using SymbolicRegression

    @test Base.Docs.hasdoc(SymbolicRegression, :Options)

    doc = Base.Docs.doc(SymbolicRegression.Options)
    txt = sprint(show, doc)
    @test occursin("Construct options for `equation_search`", txt)

    # Regression: the Options docstring should not attach to effort-scaling constants.
    @test !Base.Docs.hasdoc(
        SymbolicRegression.CoreModule.OptionsModule,
        :EFFORT_NITERATIONS_EXPONENT,
    )
end
