@testitem "Test utils" begin
    using SymbolicRegression
    using SymbolicRegression.UtilsModule: bottomk_fast, is_anonymous_function
    using Random

    function simple_bottomk(x, k)
        idx = sortperm(x)[1:k]
        return x[idx], idx
    end

    array_options = [
        (n=n, seed=seed, T=T) for
        n in (1, 5, 20, 50, 100, 1000), seed in 1:10, T in (Float32, Float64, Int)
    ]

    @testset "bottomk_fast" begin
        for opt in array_options, k in (1, 2, 3, 5, 10, 20, 50, 100)
            k > opt.n && continue
            x = rand(MersenneTwister(opt.seed), opt.T, opt.n) .* 2 .- 1
            @test bottomk_fast(x, k) == simple_bottomk(x, k)
        end
    end
end

@testitem "bottomk_fast with nonfinite and typemax values" begin
    using SymbolicRegression.UtilsModule: bottomk_fast

    for x in (
        [5.0, Inf],
        [Inf, 5.0],
        [5.0, 6.0, Inf],
        [Inf, Inf, Inf],
        [NaN, 5.0],
        [5.0, NaN],
        [NaN, Inf, 5.0],
        [NaN, NaN],
        [0.0, -0.0],
        [-0.0, 0.0],
        [0.0, -0.0, -0.0],
        [NaN, 0.0, -0.0],
        Float32[2.0f0, Inf32, NaN32],
        [typemax(Int), 1, typemax(Int)],
    )
        for k in 1:length(x)
            vals, idxs = bottomk_fast(x, k)
            expected_idxs = sortperm(x)[1:k]
            @test idxs == expected_idxs
            @test isequal(vals, x[expected_idxs])
        end
    end
end
