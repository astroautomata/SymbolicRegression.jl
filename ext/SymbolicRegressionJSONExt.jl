module SymbolicRegressionJSONExt

using JSON: JSON
import SymbolicRegression.UtilsModule: json_write

function json_write(trace, tracing_file; append::Bool)
    open(tracing_file, append ? "a" : "w") do io
        JSON.json(io, trace; allownan=true)
        write(io, '\n')
    end
end

end
