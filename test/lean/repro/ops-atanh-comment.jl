using SymbolicRegression
const O = SymbolicRegression.CoreModule.OperatorsModule

function reproduces()
    x = -2.0
    actual = O.atanh_clip(x)
    @assert mod(x + 1, 2) == 1.0
    @assert (x + 1) % 2 == -1.0
    comment_throws = try
        atanh((x + 1) % 2 - 1)
        false
    catch error
        error isa DomainError
    end
    @assert actual == 0.0
    @assert comment_throws
    println(
        "atanh_clip(-2.0) = ", actual, "; comment's percent/rem formula throws DomainError"
    )
    return true
end

reproduces() && println("REPRODUCED ops-atanh-comment")
