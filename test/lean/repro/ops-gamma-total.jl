using SymbolicRegression
const O = SymbolicRegression.CoreModule.OperatorsModule

function reproduces()
    x = -1.0
    base_error = try
        O.SpecialFunctions.gamma(x)
        false
    catch error
        error isa DomainError
    end
    wrapper_error = try
        O.gamma(x)
        false
    catch error
        println("gamma(-1.0) throws ", typeof(error), "; expected NaN at the pole")
        error isa DomainError
    end
    @assert base_error && wrapper_error
    @assert isnan(O.gamma(0.0))
    return true
end

reproduces() && println("REPRODUCED ops-gamma-total")
