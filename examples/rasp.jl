#! format: off

#literate_begin file="src/examples/rasp.md"
#=
# Evolving RASP-like Programs with Custom Types

[RASP](https://arxiv.org/abs/2106.06981) ("Restricted Access Sequence Processing
Language", Weiss et al. 2021) is a computational model of Transformer
architectures: programs operate over fixed-length _sequences_ with operations
like `map` (elementwise transforms), `indices`, `select` (build a 0/1 attention
mask from a predicate over keys and queries), `aggregate` (combine values over
selected positions, broadcast back), and `selector_width` (count selected
positions). The same operator family shows up in DeepMind's
[Tracr](https://arxiv.org/abs/2301.05062) compiler and in work on decompiling
Transformers back into RASP programs.

Let's evolve RASP-like programs directly with SymbolicRegression.jl,
using a custom input type.

First, we define our type. In RASP, most values are sequences, but a few
operations are inherently _scalar_: `aggregate` combines the selected values
into a single number, `selector_width` counts selected positions, and `length`
is just a number. Scalars then broadcast against sequences in later
operations. To be faithful to this, our type is a union payload: a value that
is either a single scalar **or** a fixed-length sequence of tokens:
=#

using SymbolicRegression
using DynamicExpressions: GenericOperatorEnum
using MLJBase: machine, fit!, report, MLJBase
using Random

"""Fixed length of every token sequence in our dataset."""
const SEQ_LEN = 8

"""
A RASP value: either a single scalar (e.g. the output of `aggregate`,
`selector_width`, or `length`), or a sequence of `SEQ_LEN` tokens.
Scalars broadcast against sequences in binary operations.
"""
struct RASPVal
    data::Union{Float64,Vector{Float64}}
end

"""Promote a scalar to a constant sequence; sequences pass through unchanged."""
toseq(v::RASPVal) = v.data isa Vector{Float64} ? v.data : fill(v.data, SEQ_LEN)

#=
Now, our RASP-inspired operator set. Every operator maps `RASPVal`(s) to an
`RASPVal`, so the expression type is uniform — the scalar/sequence distinction
lives inside the payload and is handled by broadcasting (`toseq`), exactly
like RASP's broadcasting semantics.

First, the elementwise `map` operations. These lift over both payload kinds:
applied to each token of a sequence, or directly to a scalar. We also include
the RASP primitives `indices` (a sequence) and `length` (a scalar):
=#

"""Lift an elementwise function over either payload kind."""
function lift1(f, v::RASPVal)
    return RASPVal(v.data isa Vector{Float64} ? f.(v.data) : f(v.data))
end

"""RASP `map`: square each token (or scalar)."""
map_sqr(v::RASPVal) = lift1(x -> x^2, v)

"""RASP `map`: negate each token (or scalar)."""
map_neg(v::RASPVal) = lift1(-, v)

"""RASP `map`: clamp each token (or scalar) to [0, 1]."""
map_clamp01(v::RASPVal) = lift1(x -> clamp(x, 0.0, 1.0), v)

"""RASP `indices`: the position sequence [0, 1, ..., n-1]."""
indices_seq(::RASPVal) = RASPVal(collect(Float64(0):Float64(SEQ_LEN - 1)))

"""RASP `length`: the sequence length n, as a _scalar_."""
length_seq(::RASPVal) = RASPVal(Float64(SEQ_LEN))

#=
Next, the heart of RASP: `select` and `aggregate`. A `select` compares keys
and queries elementwise to produce a 0/1 mask — a sequence — broadcasting any
scalar input against the other side (a full-attention selector, in Tracr
terms). An `aggregate` combines the values at selected positions into a
_scalar_. `agg_sum` of a mask is RASP's `selector_width`:
=#

"""RASP `select` with predicate `<`: 1.0 where a < b, else 0.0. Scalars broadcast."""
sel_lt(a::RASPVal, b::RASPVal) = RASPVal(Float64.(toseq(a) .< toseq(b)))

"""RASP `select` with predicate `>`: 1.0 where a > b, else 0.0. Scalars broadcast."""
sel_gt(a::RASPVal, b::RASPVal) = RASPVal(Float64.(toseq(a) .> toseq(b)))

"""RASP `select` with predicate `==`: 1.0 where a == b, else 0.0. Scalars broadcast."""
sel_eq(a::RASPVal, b::RASPVal) = RASPVal(Float64.(toseq(a) .== toseq(b)))

"""RASP `aggregate`: mean of v over positions where m > 0.5 (0 if none). Returns a scalar."""
function agg_mean(v::RASPVal, m::RASPVal)
    tokens = toseq(v)
    sel = toseq(m) .> 0.5
    n = sum(sel)
    return RASPVal(n > 0 ? sum(tokens[sel]) / n : 0.0)
end

"""RASP `aggregate` with sum; of a mask, this is `selector_width`. Returns a scalar."""
function agg_sum(v::RASPVal, m::RASPVal)
    tokens = toseq(v)
    sel = toseq(m) .> 0.5
    return RASPVal(sum(tokens[sel]))
end

#=
Now let's create a dataset from a fixed ground-truth RASP program. Our target
deliberately requires _composition_ of the RASP primitives — a `select` whose
comparison threshold is itself the result of an `aggregate`, counted by a
second `aggregate` (a `selector_width`):

> _the number of tokens greater than the mean of the sequence_

In our operator tree, this is

```
agg_sum(sel_gt(x, agg_mean(x, sel_eq(x, x))), sel_eq(x, x))
```

where `sel_eq(x, x)` builds the all-ones "select everything" mask. The inner
`agg_mean` computes the sequence mean (a scalar), `sel_gt` broadcasts that
scalar against every token to build a mask of above-average positions, and the
outer `agg_sum` counts them — a genuine select → aggregate → select pipeline
that no elementwise map or constant can reproduce:
=#

function ground_truth(x::RASPVal)
    select_all = sel_eq(x, x)
    mean_token = agg_mean(x, select_all)
    above_mean = sel_gt(x, mean_token)
    return agg_sum(above_mean, select_all)
end

function single_instance(rng=Random.default_rng())
    x = RASPVal(rand(rng, SEQ_LEN))
    y = ground_truth(x)
    return (; X=(; x), y)
end

dataset = let rng = Random.MersenneTwister(0)
    [single_instance(rng) for _ in 1:128]
end

#=
We'll get them in the right format for MLJ:
=#

X = [d.X for d in dataset]
y = [d.y for d in dataset];

#=
To actually get this working with SymbolicRegression, we need to overload the
custom type interface, exactly as for the string example. Each overload must
handle both payload kinds (scalar and sequence).

First, we say that a single RASP value is one "scalar" constant:
=#

import DynamicExpressions: count_scalar_constants
count_scalar_constants(::RASPVal) = 1

#=
Next, an initializer (normally `0.0` for numeric types):
=#

import SymbolicRegression: init_value
init_value(::Type{RASPVal}) = RASPVal(0.0)

#=
Next, a random sampler for generating initial random leafs. We mostly sample
scalars — scalar constants give the search building blocks such as comparison
thresholds — and random token sequences the rest of the time:
=#

using Random: AbstractRNG
import SymbolicRegression: sample_value
function sample_value(rng::AbstractRNG, ::Type{RASPVal}, _)
    return rand(rng) < 0.7 ? RASPVal(randn(rng)) : RASPVal(randn(rng, SEQ_LEN))
end

#=
We also define a pretty printer, so it is easier to read constants of either
payload kind:
=#

import SymbolicRegression.InterfaceDynamicExpressionsModule: string_constant
function string_constant(val::RASPVal, ::Val{precision}, _) where {precision}
    if val.data isa Vector{Float64}
        return "[" * join((round(v; sigdigits=precision) for v in val.data), " ") * "]"
    else
        return string(round(val.data; sigdigits=precision))
    end
end

#=
We disable constant optimization for RASP values, since it is not really
defined:
=#

import SymbolicRegression.ConstantOptimizationModule: can_optimize
can_optimize(::Type{RASPVal}, _) = false

#=
Finally, `mutate_value`, so any constant can be iteratively mutated into any
other of the same payload kind. Scalars are perturbed by Gaussian noise (with
the occasional resample); sequences get a Poisson number of positions
resampled, with the rate scaled by the temperature:
=#

using SymbolicRegression.UtilsModule: poisson_sample

import SymbolicRegression: mutate_value

function mutate_value(rng::AbstractRNG, val::RASPVal, T, options)
    if val.data isa Vector{Float64}
        lambda_max = 2.0
        λ = max(nextfloat(0.0), lambda_max * clamp(float(T), 0, 1))
        n_edits = clamp(poisson_sample(rng, λ), 0, SEQ_LEN)
        tokens = copy(val.data)
        for _ in 1:n_edits
            tokens[rand(rng, eachindex(tokens))] = randn(rng)
        end
        return RASPVal(tokens)
    else
        scale = max(clamp(float(T), 0, 1), 0.01)
        return RASPVal(rand(rng) < 0.2 ? randn(rng) : val.data + scale * randn(rng))
    end
end

#=
This concludes the custom type interface. Now let's actually use it!

For the loss, we use the mean squared error over the token vectors. Because
our ground truth (and many candidate expressions) produce _scalars_, we
promote both sides with `toseq` first — a scalar is treated as a constant
sequence, so search gradients still flow through scalar-valued expressions:
=#

function elementwise_loss(a::RASPVal, b::RASPVal)::Float64
    return sum(abs2, toseq(a) .- toseq(b)) / SEQ_LEN
end

#=
Next, let's create our regressor object. We pass `GenericOperatorEnum`,
because we are dealing with non-numeric types, and manually set the
`loss_type`. We keep the operator set focused on the RASP primitives we need
(the `select`/`aggregate` family, plus a few `map`s) — every extra operator
multiplies the search space. We also set a seed and run in serial so the
search is fully deterministic and reproducible:
=#

binary_operators = (sel_lt, sel_gt, sel_eq, agg_mean, agg_sum)
unary_operators = (map_sqr, map_neg, map_clamp01, indices_seq, length_seq)
hparams = (;
    batching=true,
    batch_size=32,
    maxsize=25,
    parsimony=0.01,
    adaptive_parsimony_scaling=20.0,
    early_stop_condition=(l, c) -> l < 1e-12 && c <= 13,  #src
    niterations=600,
    timeout_in_seconds=420.0,
    seed=0,
    deterministic=true,
    parallelism=:serial,
)
model = SRRegressor(;
    binary_operators,
    unary_operators,
    operator_enum_constructor=GenericOperatorEnum,
    elementwise_loss=elementwise_loss,
    loss_type=Float64,
    hparams...,
);

mach = machine(model, X, y; scitype_check_level=0)

#=
At this point, you would run `fit!(mach)` as usual.
Ignore the MLJ warnings about `scitype`s.
```julia
fit!(mach)
```
=#

#literate_end

using Test

fit!(mach)

ŷ = report(mach).equations[end](MLJBase.matrix(X; transpose=true))
mean_loss = sum(map(elementwise_loss, y, ŷ)) / length(y)
@info "Mean token-vector loss" mean_loss
@test mean_loss <= 1e-10
#! format: on
