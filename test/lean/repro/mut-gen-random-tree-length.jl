using SymbolicRegression, DynamicExpressions, Random
using SymbolicRegression.MutationFunctionsModule:
    append_random_op, insert_random_op, prepend_random_op

# rand(rng) is 0.0; every other draw comes from an inner Xoshiro.
struct ZeroFloatRNG <: Random.AbstractRNG
    inner::Xoshiro
end
function Random.rand(
    r::ZeroFloatRNG, ::Random.SamplerType{S}
) where {S<:Union{Bool,Base.BitInteger}}
    rand(r.inner, S)
end
Random.rand(r::ZeroFloatRNG, ::Random.SamplerTrivial{Random.CloseOpen01{Float64}}) = 0.0
Random.rng_native_52(::ZeroFloatRNG) = UInt64
using SymbolicRegression.MutationFunctionsModule: gen_random_tree

options = Options(; binary_operators=[], unary_operators=[cos])
control = gen_random_tree(1, options, 1, Float64, Xoshiro(1))
@assert count_nodes(control) == 2
caught = try
    gen_random_tree(1, options, 1, Float64, ZeroFloatRNG(Xoshiro(1)))
    nothing
catch e
    e
end
println(
    "Unary operators only: an ordinary draw yields ",
    count_nodes(control),
    " nodes; a zero draw yields ",
    caught,
)
@assert caught isa ArgumentError
println("REPRODUCED mut-gen-random-tree-length")
