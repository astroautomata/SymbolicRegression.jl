module SymbolicRegressionPythonCallExt

using PrecompileTools: @compile_workload
using ProgressMeter: ProgressMeter
using PythonCall: PythonCall
using Serialization: Serialization
using SymbolicRegression: SymbolicRegression

precompile(Tuple{Type{PythonCall.PyArray},PythonCall.Py})
precompile(Tuple{typeof(PythonCall.JlWrap.pyjlany_getattr),Module,PythonCall.Py})
precompile(Tuple{typeof(PythonCall.JlWrap.pyjlany_getattr),VersionNumber,PythonCall.Py})
for T in (
    SymbolicRegression.Options,
    SymbolicRegression.OperatorEnum,
    SymbolicRegression.ExpressionSpec,
    SymbolicRegression.ExternalStop,
    PythonCall.PyArray,
    IOBuffer,
    Symbol,
)
    precompile(
        Tuple{typeof(PythonCall.JlWrap.pyjlany_call),Type{T},PythonCall.Py,PythonCall.Py}
    )
end
for f in (
    isa,
    copy,
    take!,
    Serialization.serialize,
    PythonCall.pybytes,
    PythonCall.pyconvert,
)
    precompile(
        Tuple{typeof(PythonCall.JlWrap.pyjlany_call),typeof(f),PythonCall.Py,PythonCall.Py}
    )
end
precompile(
    Tuple{
        typeof(PythonCall.JlWrap.pyjlany_call_nogil),
        typeof(SymbolicRegression.equation_search),
        PythonCall.Py,
        PythonCall.Py,
    },
)
if isdefined(PythonCall, :Wrap) && isdefined(PythonCall.Wrap, :pyarray_get_size)
    for N in (1, 2)
        precompile(
            Tuple{
                typeof(PythonCall.Wrap.pyarray_get_size),
                PythonCall.Wrap.PyArraySource_ArrayStruct,
                Val{N},
            },
        )
    end
end
let mapping_rule = PythonCall.Convert.pyconvert_fix(
        Dict{Symbol,Any}, PythonCall.Convert.pyconvert_rule_mapping
    )
    precompile(Tuple{typeof(mapping_rule),PythonCall.Py})
end
for (T, rule_fn) in (
    (Integer, PythonCall.Convert.pyconvert_rule_int),
    (Bool, PythonCall.Convert.pyconvert_rule_bool),
)
    rule = PythonCall.Convert.pyconvert_fix(T, rule_fn)
    precompile(Tuple{typeof(rule),PythonCall.Py})
end
for T in (Vector{PythonCall.Py}, Vector{Any}, Vector, Tuple, NamedTuple)
    rule = PythonCall.Convert.pyconvert_fix(T, PythonCall.Convert.pyconvert_rule_iterable)
    precompile(Tuple{typeof(rule),PythonCall.Py})
end
if isdefined(PythonCall.Convert, :pyconvert_get_rules)
    for T in (
        Any,
        Array,
        Int,
        Integer,
        Float64,
        Bool,
        String,
        Symbol,
        Dict{Symbol,Any},
        Vector,
        Tuple,
        NamedTuple,
    )
        precompile(Tuple{typeof(PythonCall.Convert.pyconvert_get_rules),Type{T},PythonCall.Py})
        if isdefined(PythonCall.Convert, :_pyconvert_get_rules)
            precompile(
                Tuple{typeof(PythonCall.Convert._pyconvert_get_rules),Type{T},PythonCall.Py}
            )
        end
    end
end
precompile(Tuple{typeof(PythonCall.pyconvert),Type{Array},PythonCall.Py})
precompile(
    Tuple{
        typeof(PythonCall.Convert._pyconvert_rule_iterable),
        Vector{String},
        PythonCall.Py,
        Type{Any},
    },
)
for N in (1, 2)
    precompile(Tuple{typeof(copy),PythonCall.PyArray{Float32,N,true,true,Float32}})
end
precompile(Tuple{typeof(ProgressMeter.printover),Base.IOStream,String,Symbol})
if isdefined(Base, :AnnotatedString)
    precompile(
        Tuple{typeof(ProgressMeter.printover),Base.IOStream,Base.AnnotatedString{String},Symbol}
    )
end

function pysr_shaped_workload(
    mode, operators=SymbolicRegression.OperatorEnum(((), (+, -, /, *)))
)
    SymbolicRegression.do_precompilation(
        mode;
        operator_kwargs=(; operators=operators),
        search_kwargs=(;
            external_stop=SymbolicRegression.ExternalStop(),
            variable_names=["x0", "x1", "x2"],
            display_variable_names=["x0", "x1", "x2"],
            y_variable_names=nothing,
            X_units=nothing,
            y_units=nothing,
            logger=nothing,
            run_id="precompile",
            progress=true,
            runtests=true,
            parallelism="multithreading",
            verbosity=1,
        ),
        precompile_serialization=true,
    )
    # Also precompile file-saving (`save_frontier_if_changed!` + raw `string_tree`)
    # and batched `SubDataset` evaluation used by PySR's default `save_to_file=true`
    # and `batching=true` / `N>1000` runs.
    @compile_workload begin
        mktempdir() do tmpdir
            X = randn(Float32, 3, 30)
            y = randn(Float32, 30)
            opts_save = SymbolicRegression.Options(;
                operators=operators,
                populations=2,
                population_size=12,
                tournament_selection_n=4,
                ncycles_per_iteration=2,
                define_helper_functions=false,
                optimizer_probability=0.05,
                save_to_file=true,
                output_directory=tmpdir,
                batching=true,
                batch_size=10,
            )
            SymbolicRegression.equation_search(
                X,
                y;
                niterations=1,
                options=opts_save,
                return_state=true,
                external_stop=SymbolicRegression.ExternalStop(),
                variable_names=["x0", "x1", "x2"],
                display_variable_names=["x0", "x1", "x2"],
                run_id="precompile_save",
                progress=false,
                runtests=false,
                parallelism="multithreading",
                verbosity=0,
            )
        end
    end
    return nothing
end

redirect_stdout(devnull) do
    redirect_stderr(devnull) do
        return pysr_shaped_workload(Val(:precompile))
    end
end

end
