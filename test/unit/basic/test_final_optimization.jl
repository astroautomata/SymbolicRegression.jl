@testitem "Test final_optimizer_iterations default" begin
    using SymbolicRegression

    options = Options()
    @test options.final_optimizer_iterations == 0
    @test_throws AssertionError Options(; final_optimizer_iterations=-1)
end

@testitem "Test final_optimizer_iterations=0 is no-op" begin
    using SymbolicRegression
    using Random

    Random.seed!(42)
    X = randn(2, 30)
    y = 2.0 .* X[1, :] .+ X[2, :]

    options = Options(;
        binary_operators=[+, -, *],
        unary_operators=[],
        populations=3,
        population_size=33,
        final_optimizer_iterations=0,
        verbosity=0,
    )
    hof = equation_search(X, reshape(y, 1, :); niterations=1, options=options)
    @test sum(hof.exists) > 0
    for i in eachindex(hof.members, hof.exists)
        hof.exists[i] || continue
        @test isfinite(hof.members[i].loss)
    end
end

@testitem "Test final_optimizer_iterations>0 runs final pass" begin
    using SymbolicRegression
    using SymbolicRegression:
        HallOfFame, PopMember, create_expression, _final_constant_optimization!

    X = reshape(collect(range(-1.0, 1.0; length=30)), 1, :)
    y = 3.0 .* X[1, :]

    options = Options(;
        binary_operators=[*],
        unary_operators=[],
        final_optimizer_iterations=40,
        deterministic=true,
        verbosity=0,
    )
    dataset = Dataset(X, y)
    raw_tree = Node{Float64,2}(;
        op=1, children=(Node{Float64,2}(; val=0.5), Node{Float64,2}(; feature=1))
    )
    tree = create_expression(raw_tree, options, dataset)
    member = PopMember(dataset, tree, options; deterministic=true)
    initial_loss = member.loss

    hof = HallOfFame(options, dataset)
    hof.members[3] = member
    hof.exists[3] = true
    state = (; halls_of_fame=[hof])

    _final_constant_optimization!(state, [dataset], options)

    @test hof.members[3].loss < initial_loss
    @test hof.members[3].loss < 1.0e-10
end
