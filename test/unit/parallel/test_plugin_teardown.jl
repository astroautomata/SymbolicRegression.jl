@testitem "Plugin interface: on_search_end! runs before owned workers are removed" begin
    using Distributed
    using DynamicExpressions: AbstractExpression, Node
    using SymbolicRegression
    using SymbolicRegression: AbstractPlugin
    using SymbolicRegression.CoreModule: RecordType
    using SymbolicRegression.SearchUtilsModule: AbstractRuntimeOptions, AbstractSearchState
    import SymbolicRegression.SearchUtilsModule: close_reader!
    using Test

    struct TeardownProbeExpression <: AbstractExpression{Float64,Node{Float64}} end
    struct TeardownProbeReader end
    close_reader!(::TeardownProbeReader) = nothing

    struct TeardownProbePlugin <: AbstractPlugin end
    struct TeardownProbeState
        called::Base.RefValue{Bool}
        workers_alive::Base.RefValue{Bool}
        outputs_ready::Base.RefValue{Bool}
    end
    function SymbolicRegression.on_search_end!(
        state::TeardownProbeState,
        ::TeardownProbePlugin,
        search_state,
        dataset,
        options,
        ropt,
    )
        state.called[] = true
        state.workers_alive[] = all(in(workers()), search_state.procs)
        state.outputs_ready[] = all(isready, Iterators.flatten(search_state.worker_output))
        return nothing
    end

    struct TeardownProbeRuntimeOptions <: AbstractRuntimeOptions
        parallelism::Symbol
    end
    struct TeardownProbeSearchState <:
           AbstractSearchState{Float64,Float64,TeardownProbeExpression}
        procs::Vector{Int}
        we_created_procs::Bool
        worker_output::Vector{Vector{Future}}
        plugin_states::Vector{Tuple{TeardownProbeState}}
        stdin_reader::TeardownProbeReader
        record::Base.RefValue{RecordType}
    end

    called = Ref(false)
    workers_alive = Ref(false)
    outputs_ready = Ref(false)
    plugin_state = TeardownProbeState(called, workers_alive, outputs_ready)
    options = Options(;
        binary_operators=[+, *],
        use_frequency=false,
        use_frequency_in_tournament=false,
        save_to_file=false,
        plugins=(TeardownProbePlugin(),),
    )
    ropt = TeardownProbeRuntimeOptions(:multiprocessing)

    proc = only(addprocs(1))
    try
        future = remotecall(sleep, proc, 0.25)
        search_state = TeardownProbeSearchState(
            [proc],
            true,
            [[future]],
            [(plugin_state,)],
            TeardownProbeReader(),
            Ref(RecordType()),
        )

        SymbolicRegression._tear_down!(search_state, [nothing], ropt, options)

        @test called[]
        @test outputs_ready[]
        @test workers_alive[]
        @test proc ∉ workers()
    finally
        proc in workers() && rmprocs(proc)
    end
end
