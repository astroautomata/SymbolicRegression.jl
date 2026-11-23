@testitem "Options compiles its body once for every keyword set" begin
    using SymbolicRegression
    using SymbolicRegression.CoreModule.OptionsModule: _build_options

    Options(; binary_operators=(+, *), maxsize=Int32(17), parsimony=0.5f0)
    Options(; binary_operators=[-], maxdepth=8, input_stream=devnull)

    @test only(Base.specializations(only(methods(_build_options)))).specTypes ==
        Tuple{typeof(_build_options),NamedTuple}
end
