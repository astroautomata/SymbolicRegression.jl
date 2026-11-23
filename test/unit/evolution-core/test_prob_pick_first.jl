@testitem "Test tournament selection" begin
    println("Testing whether tournament_selection_p works.")
    using SymbolicRegression
    using DynamicExpressions: with_type_parameters, @parse_expression
    using Test
    include(joinpath(@__DIR__, "..", "..", "test_params.jl"))

    n = 10

    options = Options(;
        default_params...,
        binary_operators=(+, -, *, /),
        unary_operators=(cos, sin),
        tournament_selection_p=0.999,
        tournament_selection_n=n,
    )

    for reverse in [false, true]
        T = Float32
        dataset = Dataset(zeros(T, 1, n), zeros(T, n))
        plugin_states = SymbolicRegression.init_plugin_states(options, dataset)

        # Generate members with scores from 0 to 1:
        members = [
            let
                ex = @parse_expression(
                    x1 * 3.2, operators = options.operators, variable_names = [:x1],
                )
                cost = Float32(i - 1) / (n - 1)
                if reverse
                    cost = 1 - cost
                end
                test_loss = 1.0f0  # (arbitrary for this test)
                PopMember(ex, cost, test_loss, options; deterministic=false)
            end for i in 1:n
        ]

        pop = Population(members)

        best_pop_member = [
            SymbolicRegression.best_of_sample(pop, options; plugin_states).cost for
            j in 1:100
        ]

        mean_value = sum(best_pop_member) / length(best_pop_member)

        # Make sure average cost is small
        @test mean_value < 0.1
    end

    println("Passed.")
end

@testitem "Tournament selection handles Inf and NaN costs" begin
    using SymbolicRegression
    using SymbolicRegression.PopulationModule: _best_of_sample
    using Random

    X = reshape([1.0, 2.0, 3.0, 4.0], 1, :)
    dataset = Dataset(X, vec(X))

    options_p1 = Options(;
        binary_operators=[+, *],
        default_plugins=(),
        tournament_selection_p=1.0,
        tournament_selection_n=2,
        population_size=10,
    )
    function make_member(c, options)
        m = PopMember(dataset, Node{Float64}(; feature=1), options; deterministic=false)
        m.cost = c
        return m
    end

    @test _best_of_sample(
        [make_member(NaN, options_p1), make_member(1.0, options_p1)],
        [1, 2],
        options_p1;
        plugin_states=(),
    ).cost == 1.0
    @test _best_of_sample(
        [make_member(NaN, options_p1), make_member(Inf, options_p1)],
        [1, 2],
        options_p1;
        plugin_states=(),
    ).cost == Inf

    Random.seed!(0)
    options_ranked = Options(;
        binary_operators=[+, *],
        default_plugins=(),
        tournament_selection_p=0.5,
        tournament_selection_n=2,
        population_size=10,
    )
    members_inf = [make_member(5.0, options_ranked), make_member(Inf, options_ranked)]
    picks_inf = count(
        _ ->
            _best_of_sample(members_inf, [1, 2], options_ranked; plugin_states=()) ===
            members_inf[2],
        1:300,
    )
    @test picks_inf > 0

    members_nan = [make_member(5.0, options_ranked), make_member(NaN, options_ranked)]
    picks_nan = count(
        _ ->
            _best_of_sample(members_nan, [1, 2], options_ranked; plugin_states=()) ===
            members_nan[2],
        1:300,
    )
    @test picks_nan > 0
end
