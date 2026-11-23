module SymbolicRegressionPythonCallExt

using PythonCall: PythonCall
using SymbolicRegression: SymbolicRegression

precompile(Tuple{Type{PythonCall.PyArray},PythonCall.Py})
for T in (
    SymbolicRegression.Options,
    SymbolicRegression.OperatorEnum,
    SymbolicRegression.ExpressionSpec,
    SymbolicRegression.ExternalStop,
    IOBuffer,
    Symbol,
)
    precompile(
        Tuple{typeof(PythonCall.JlWrap.pyjlany_call),Type{T},PythonCall.Py,PythonCall.Py}
    )
end
let mapping_rule = PythonCall.Convert.pyconvert_fix(
        Dict{Symbol,Any}, PythonCall.Convert.pyconvert_rule_mapping
    )
    precompile(Tuple{typeof(mapping_rule),PythonCall.Py})
end
for T in (Vector{PythonCall.Py}, Vector{Any}, Vector, Tuple, NamedTuple)
    rule = PythonCall.Convert.pyconvert_fix(T, PythonCall.Convert.pyconvert_rule_iterable)
    precompile(Tuple{typeof(rule),PythonCall.Py})
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

# Conversions and calls PySR makes from Python that the workload below cannot.
for (T, rule) in (
    (Integer, PythonCall.Convert.pyconvert_rule_int),
    (Bool, PythonCall.Convert.pyconvert_rule_bool),
)
    precompile(Tuple{typeof(PythonCall.Convert.pyconvert_fix(T, rule)),PythonCall.Py})
end
for T in (String, Tuple{Int64,Int64})
    precompile(Tuple{Type{Vector{T}},Vector{Union{}}})
end
precompile(
    Tuple{
        typeof(PythonCall.Convert._pyconvert_rule_iterable),
        Vector{Tuple{Int64,Int64}},
        PythonCall.Py,
        Type{Any},
    },
)

# Julia functions and types that PySR calls or indexes directly from Python.
for f in (
    isa,
    copy,
    take!,
    SymbolicRegression.SearchUtilsModule.generate_run_id,
    SymbolicRegression.Serialization.serialize,
    PythonCall.PyArray,
    Dict{Int64,Vector},
)
    precompile(
        Tuple{
            typeof(PythonCall.JlWrap.pyjlany_call),
            Core.Typeof(f),
            PythonCall.Py,
            PythonCall.Py,
        },
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
precompile(Tuple{typeof(PythonCall.JlWrap.pyjltype_getitem),Type,PythonCall.Py})
precompile(
    Tuple{
        typeof(PythonCall.JlWrap.pyjldict_setitem),
        Dict{Int64,Vector},
        PythonCall.Py,
        PythonCall.Py,
    },
)
# NumPy reads serialized search state through the buffer protocol.
precompile(
    Tuple{
        typeof(PythonCall.JlWrap.Cjl._pyjl_get_buffer_impl),
        Ptr{PythonCall.C.PyObject},
        Ptr{PythonCall.C.Py_buffer},
        Int32,
        Vector{UInt8},
        typeof(PythonCall.JlWrap.pyjlarray_buffer_info),
    },
)
# PySR converts Python lists with `PythonCall.pyconvert(Array, list)`, which
# receives the list wrapped as a `PyList`.
precompile(
    Tuple{
        typeof(PythonCall.JlWrap.pyjlany_call),
        typeof(PythonCall.pyconvert),
        PythonCall.Py,
        PythonCall.Py,
    },
)
precompile(Tuple{typeof(PythonCall.pyconvert),Type{Array},PythonCall.PyList{PythonCall.Py}})

# The workload below prints to devnull, but in a terminal the progress bar
# writes styled text to a `Base.TTY`.
let AnnotatedString = SymbolicRegression.UtilsModule.AnnotatedString{String}
    precompile(
        Tuple{
            typeof(SymbolicRegression.ProgressBarsModule.ProgressMeter.printover),
            Base.TTY,
            AnnotatedString,
            Symbol,
        },
    )
    precompile(Tuple{typeof(print),Base.TTY,AnnotatedString,String})
end

function pysr_shaped_workload(
    mode, operators=SymbolicRegression.OperatorEnum(((), (+, -, /, *)))
)
    return SymbolicRegression.do_precompilation(
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
end

redirect_stdout(devnull) do
    redirect_stderr(devnull) do
        SymbolicRegression.do_precompilation(Val(:precompile))
        return pysr_shaped_workload(Val(:precompile))
    end
end

# PySR always passes `constraints`, which runs a part of `Options` that the
# searches above skip. This compiles it without changing their `Options` type.
SymbolicRegression.@compile_workload begin
    SymbolicRegression.Options(;
        operators=SymbolicRegression.OperatorEnum(((), (+, -, /, *))),
        constraints=Dict{Int,Vector}(1 => [], 2 => fill((-1, -1), 4)),
    )
end

end
