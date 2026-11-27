@testitem "Abstract numbers" begin
    using SymbolicRegression
    using Random
    include(joinpath(@__DIR__, "..", "..", "test_params.jl"))

    get_base_type(::Type{<:Complex{BT}}) where {BT} = BT
    early_stop(loss::L, c) where {L} = (
        (loss <= (L === Float16 ? L(1.2e-2) : L(1e-2))) && (c <= 15)
    )
    example_loss(prediction, target) = abs2(prediction - target)

    options = SymbolicRegression.Options(;
        binary_operators=[+, *, -, /],
        unary_operators=[cos],
        populations=20,
        early_stop_condition=early_stop,
        elementwise_loss=example_loss,
    )

    for T in (ComplexF16, ComplexF32, ComplexF64)
        L = get_base_type(T)
        @testset "Test search with $T type" begin
            X = randn(MersenneTwister(0), T, 1, 100)
            y = @. (2 - 0.5im) * cos((1 + 1im) * X[1, :]) |> T

            dataset = Dataset(X, y, L)
            hof = if T == ComplexF16
                equation_search([dataset]; options=options, niterations=1_000_000_000)
            else
                # Should automatically find correct type:
                equation_search(X, y; options=options, niterations=1_000_000_000)
            end

            dominating = calculate_pareto_frontier(hof)
            @test typeof(dominating[end].loss) == L
            output, _ = eval_tree_array(dominating[end].tree, X, options)
            @test typeof(output) <: AbstractArray{T}
            tol = T == ComplexF16 ? L(1.2e-2) : L(1e-2)
            @test sum(abs2, output .- y) / length(output) <= tol
        end
    end
end

@testitem "Testing error handling in InterfaceDataTypesModule" begin
    using SymbolicRegression:
        ConstantMutation, Options, init_value, sample_value, mutate_value
    using Random

    struct CustomTestType end

    rng = Random.MersenneTwister(0)
    options = Options()
    @test_throws "No `init_value` method defined for type" init_value(CustomTestType)
    @test_throws "No `sample_value` method defined for type" sample_value(
        rng, CustomTestType, options
    )
    @test_throws "No `mutate_value` method defined for type" mutate_value(
        rng, CustomTestType(), 0.5, ConstantMutation()
    )
end

@testitem "Custom value mutation receives the selected mutation" begin
    using SymbolicRegression
    using SymbolicRegression.MutationFunctionsModule: _mutate_value
    using Random
    using Test

    struct TemperatureAwareValue
        temperature::Float64
        perturbation_factor::Float64
        probability_flip_sign::Float64
    end

    function SymbolicRegression.mutate_value(
        rng::AbstractRNG,
        value::TemperatureAwareValue,
        temperature::Real,
        mutation::ConstantMutation,
    )
        return TemperatureAwareValue(
            Float64(temperature),
            mutation.perturbation_factor,
            mutation.probability_flip_sign,
        )
    end

    options = Options()
    mutation = ConstantMutation(; perturbation_factor=0.2)
    result = _mutate_value(
        Random.default_rng(), TemperatureAwareValue(1.0, 0.0, 0.0), 0.25, mutation, options
    )
    @test result == TemperatureAwareValue(0.25, 0.2, 0.99)
end

@testitem "Default constant mutation flips the sign at the default rate" begin
    using SymbolicRegression
    using SymbolicRegression.MutationFunctionsModule: mutate_factor
    using Random

    options = Options()
    @test options.probability_flip_constant_sign == 0.99257
    m = only(first(p) for p in options.mutations if first(p) isa ConstantMutation)
    rng = Xoshiro(0)
    n = 100_000
    flipped = count(_ -> mutate_factor(Float64, 1.0, m, rng) < 0, 1:n)
    @test abs(flipped / n - 0.99257) < 0.002
end
