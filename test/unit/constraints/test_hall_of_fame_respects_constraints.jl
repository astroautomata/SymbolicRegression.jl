@testitem "Hall of Fame respects nested constraints" tags = [:part1] begin
    using SymbolicRegression

    options = Options(;
        binary_operators=(+, *),
        unary_operators=(),
        maxsize=15,
        nested_constraints=[(*) => [(*) => 0]],
    )
    @extend_operators options

    T = Float64
    X = randn(T, 3, 20)
    y = @. X[1, :] * X[2, :] * X[3, :]
    dataset = Dataset(X, y)

    # Construct an expression that violates the constraint (* inside *).
    x1, x2, x3 = [Node{T}(; feature=i) for i in 1:3]
    invalid_tree = (x1 * x2) * x3
    @test SymbolicRegression.check_constraints(invalid_tree, options) == false

    member = PopMember(
        dataset, invalid_tree, options; parent=-1, deterministic=options.deterministic
    )

    hof = HallOfFame(options, dataset)
    size = compute_complexity(member, options)
    @test 0 < size <= options.maxsize

    update_hall_of_fame!(hof, [member], options)
    @test !hof.exists[size]
end
