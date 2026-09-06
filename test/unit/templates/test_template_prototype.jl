@testitem "Prototype-based num_features inference for custom types" begin
    using SymbolicRegression
    using SymbolicRegression: ValidVector

    struct Vec2
        a::Float64
        b::Float64
    end
    add_vectors(x::Vec2, y::Vec2) = Vec2(x.a + y.a, x.b + y.b)
    function add_vectors(x::ValidVector, y::ValidVector)
        return ValidVector(map(add_vectors, x.x, y.x), x.valid && y.valid)
    end

    structure = TemplateStructure{(:f, :g)}(
        ((; f, g), (x1, x2)) -> add_vectors(f(x1), g(x2)); prototype=Vec2(1.0, 2.0)
    )
    @test structure.num_features == (; f=1, g=1)

    spec = @template_spec(expressions = (f, g), prototype = Vec2(1.0, 2.0)) do x1, x2
        add_vectors(f(x1), g(x2))
    end
    @test spec.structure.num_features == (; f=1, g=1)
end

@testitem "Prototype-based inference with zero-argument subexpression" begin
    using SymbolicRegression
    using SymbolicRegression: ValidVector

    struct Vec2
        a::Float64
        b::Float64
    end
    add_vectors(x::Vec2, y::Vec2) = Vec2(x.a + y.a, x.b + y.b)
    function add_vectors(x::ValidVector, y::Vec2)
        return ValidVector(map(Base.Fix2(add_vectors, y), x.x), x.valid)
    end

    structure = TemplateStructure{(:f, :g)}(
        ((; f, g), (x1,)) -> add_vectors(f(x1), g()); prototype=Vec2(1.0, 2.0)
    )
    @test structure.num_features == (; f=1, g=0)
end

@testitem "Default Float64 inference is unchanged by prototype option" begin
    using SymbolicRegression

    structure = TemplateStructure{(:f, :g)}(((; f, g), (x1, x2, x3)) -> f(x1, x2) + g(x3))
    @test structure.num_features == (; f=2, g=1)

    # Zero-argument subexpressions still act as a Float64 zero:
    structure2 = TemplateStructure{(:f, :g)}(((; f, g), (x1,)) -> f(x1) + g())
    @test structure2.num_features == (; f=1, g=0)

    # Explicit num_features bypasses inference (combiner must not be called):
    structure3 = TemplateStructure{(:f,)}(
        ((; f), (x1,)) -> error("combiner should not run"); num_features=(; f=1)
    )
    @test structure3.num_features == (; f=1)
end

@testitem "TemplateStructure keyword order is irrelevant" begin
    using SymbolicRegression

    structure = TemplateStructure{(:f, :g),(:p, :q)}(
        ((; f, g), (; p, q), (x, y)) -> f(x, p) + g(y, q);
        num_features=(; g=1, f=2),
        num_parameters=(; q=4, p=3),
    )
    @test structure.num_features == (; f=2, g=1)
    @test structure.num_parameters == (; p=3, q=4)
end
@testitem "TemplateStructure requires disjoint expression and parameter names" begin
    using SymbolicRegression

    @test_throws ArgumentError TemplateStructure{(:f,),(:f,)}(
        ((; f), parameters, (x,)) -> f(x); num_features=(; f=1), num_parameters=(; f=1)
    )
end
