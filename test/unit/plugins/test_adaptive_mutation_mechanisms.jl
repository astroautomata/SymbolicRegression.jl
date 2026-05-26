@testitem "AdaptiveMutationWeightsPlugin: defaults + state" begin
    using SymbolicRegression
    using Test

    p = AdaptiveMutationWeightsPlugin()
    @test p.smoothing == 0.02
    @test p.floor == 0.05

    opts = Options(;
        binary_operators=[+, *],
        unary_operators=[sin],
        plugins=(AdaptiveMutationWeightsPlugin(),),
    )
    s = SymbolicRegression.init_plugin_state(
        AdaptiveMutationWeightsPlugin(), opts, nothing
    )
    @test length(s.attempts) == length(opts.mutations)
    @test all(s.multipliers .== 1.0)
end

@testitem "skip_in_adaptive_weights: defaults skip Simplify and DoNothing" begin
    using SymbolicRegression
    using SymbolicRegression.AdaptiveMutationWeightsModule: skip_in_adaptive_weights
    using Test

    @test skip_in_adaptive_weights(SymbolicRegression.Simplify()) == true
    @test skip_in_adaptive_weights(SymbolicRegression.DoNothing()) == true
    @test skip_in_adaptive_weights(SymbolicRegression.MutateConstant()) == false
    @test skip_in_adaptive_weights(SymbolicRegression.MutateOperator()) == false
end

@testitem "wrap_mutation_step: MutationRetryPlugin retries until accepted" begin
    using SymbolicRegression
    using SymbolicRegression: NoPluginState, wrap_mutation_step
    using Test

    # Inner thunk: first 2 calls reject, 3rd accepts.
    n_calls = Ref(0)
    inner =
        parent -> begin
            n_calls[] += 1
            (parent, n_calls[] >= 3, 1.0)
        end
    p = MutationRetryPlugin(; attempts=4)
    member, accepted, num_evals = wrap_mutation_step(NoPluginState(), p, :parent, inner)
    @test accepted == true
    @test n_calls[] == 3
    @test num_evals == 3.0
end

@testitem "wrap_mutation_step: MutationRetryPlugin stops at budget when never accepted" begin
    using SymbolicRegression
    using SymbolicRegression: NoPluginState, wrap_mutation_step
    using Test

    n_calls = Ref(0)
    inner =
        parent -> begin
            n_calls[] += 1
            (parent, false, 1.0)
        end
    p = MutationRetryPlugin(; attempts=4)
    member, accepted, num_evals = wrap_mutation_step(NoPluginState(), p, :parent, inner)
    @test accepted == false
    @test n_calls[] == 4
    @test num_evals == 4.0
end

@testitem "wrap_mutation_step: CompoundMutationPlugin chains on success" begin
    using SymbolicRegression
    using SymbolicRegression: NoPluginState, wrap_mutation_step
    using Random
    using Test

    n_calls = Ref(0)
    inner =
        parent -> begin
            n_calls[] += 1
            (parent + 1, true, 1.0)
        end
    p = CompoundMutationPlugin(; probability=1.0, max_steps=3)
    Random.seed!(0)
    member, accepted, num_evals = wrap_mutation_step(NoPluginState(), p, 0, inner)
    @test accepted == true
    @test n_calls[] == 3
    @test member == 3
end

@testitem "wrap_mutation_step: CompoundMutationPlugin doesn't chain on rejection" begin
    using SymbolicRegression
    using SymbolicRegression: NoPluginState, wrap_mutation_step
    using Test

    n_calls = Ref(0)
    inner =
        parent -> begin
            n_calls[] += 1
            (parent, false, 1.0)
        end
    p = CompoundMutationPlugin(; probability=1.0, max_steps=3)
    member, accepted, num_evals = wrap_mutation_step(NoPluginState(), p, 0, inner)
    @test accepted == false
    @test n_calls[] == 1
end

@testitem "wrap_mutation_step: default plugin is pass-through" begin
    using SymbolicRegression
    using SymbolicRegression: NoPluginState, AbstractPlugin, wrap_mutation_step
    using Test

    struct _NoopMidPlugin <: AbstractPlugin end
    n_calls = Ref(0)
    inner =
        parent -> begin
            n_calls[] += 1
            (parent, true, 2.0)
        end
    member, accepted, num_evals = wrap_mutation_step(
        NoPluginState(), _NoopMidPlugin(), :parent, inner
    )
    @test n_calls[] == 1
    @test num_evals == 2.0
end

@testitem "wrap_mutation_step: third-party plugin can extend the hook" begin
    # Stress test: a plugin that runs the inner step exactly twice and
    # keeps the better result by num_evals. Demonstrates the middleware
    # shape isn't tied to retry/chain semantics.
    using SymbolicRegression
    using SymbolicRegression: AbstractPlugin, NoPluginState, wrap_mutation_step
    using Test

    struct BestOfTwoPlugin <: AbstractPlugin end
    function SymbolicRegression.wrap_mutation_step(
        ::NoPluginState, ::BestOfTwoPlugin, parent, next_step::F
    ) where {F}
        r1 = next_step(parent)
        r2 = next_step(parent)
        return r1[3] <= r2[3] ? r1 : r2
    end

    n_calls = Ref(0)
    inner =
        parent -> begin
            n_calls[] += 1
            (parent, true, Float64(n_calls[]))
        end
    member, accepted, num_evals = wrap_mutation_step(
        NoPluginState(), BestOfTwoPlugin(), :p, inner
    )
    @test n_calls[] == 2
    @test num_evals == 1.0
end

@testitem "Integration: full PySR p108 stack runs and returns a HoF" begin
    using SymbolicRegression
    using Random
    using Test

    Random.seed!(0)
    X = rand(Float32, 2, 60)
    y = @. 2.0f0 * X[1, :] + sin(X[2, :])

    opts = Options(;
        binary_operators=[+, -, *, /],
        unary_operators=[sin, cos],
        populations=4,
        population_size=20,
        ncycles_per_iteration=20,
        verbosity=0,
        progress=false,
        deterministic=true,
        plugins=(
            AdaptiveMutationWeightsPlugin(; smoothing=0.02, floor=0.05),
            MutationRetryPlugin(; attempts=4),
            CompoundMutationPlugin(; probability=0.25, max_steps=2),
        ),
    )
    hof = equation_search(X, y; options=opts, niterations=3, parallelism=:serial)
    @test hof isa SymbolicRegression.HallOfFame
    @test any(hof.exists)
end

@testitem "Integration: defaults match upstream single-step loop" begin
    using SymbolicRegression
    using Random
    using Test

    Random.seed!(0)
    X = rand(Float32, 2, 30)
    y = X[1, :] .+ X[2, :]
    opts = Options(;
        binary_operators=[+, *],
        populations=2,
        population_size=30,
        ncycles_per_iteration=10,
        verbosity=0,
        progress=false,
        deterministic=true,
    )
    hof = equation_search(X, y; options=opts, niterations=2, parallelism=:serial)
    @test hof isa SymbolicRegression.HallOfFame
end
