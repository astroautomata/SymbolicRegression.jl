# Reproducer for registry entry `mut-pick-degree-has-operator` (SymReg/Mutations/Refute.lean).
# append_random_op, insert_random_op and prepend_random_op pick a degree with
# `scaled_rand > csum[i] && scaled_rand <= csum[i + 1]` (src/MutationFunctions.jl:237,278,325).
# When rand(rng) returns 0.0 (a value Xoshiro can produce: (rand(UInt64) >>> 11) * 2^-53 == 0
# for one in 2^53 draws), every test fails and @nif takes the last degree D even if it has no
# operator, so rand(rng, 1:0) throws. Unary operators only: nops == (1, 0).
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

options = Options(; binary_operators=[], unary_operators=[cos])
println("nops = ", options.nops)
failures = 0
for (name, f) in [
    ("append_random_op", append_random_op),
    ("insert_random_op", insert_random_op),
    ("prepend_random_op", prepend_random_op),
]
    tree = Node(Float64; feature=1)
    try
        out = f(tree, options, 1, ZeroFloatRNG(Xoshiro(1)))
        println(name, " returned ", out)
    catch e
        println(name, " threw ", sprint(showerror, e)[1:min(end, 120)])
        e isa ArgumentError && (global failures += 1)
    end
end
if failures > 0
    println("REPRODUCED mut-pick-degree-has-operator")
end
