# SymbolicRegression.jl in Lean

This Lean 4 project models the Julia code at commit `103f5d4299222fa4af70110f4886ced4f3fdac1b`. It reuses the DynamicExpressions.jl Lean model at commit [`097eaa54`](https://github.com/SymbolicML/DynamicExpressions.jl/tree/097eaa548dcf7525dd1f9aa4d1504beb2795f467/test/lean).

The [property registry](registry.tsv) lists 813 properties: 524 proven about the model under their stated assumptions, 89 refuted by counterexamples, and 200 open. The [bug reports](bugs/) and [Julia reproducers](repro/) describe and demonstrate the corresponding behaviour in the Julia package.

The Lean model is maintained separately from the Julia implementation. A Julia source change does not rebuild or recheck the model. Update the matching Lean definitions and proofs when changing modelled behaviour.

## Build and audit

Install [Elan](https://github.com/leanprover/elan) and Python 3. Elan selects the Lean version from `lean-toolchain`. From the repository root:

```sh
cd test/lean
lake build
./scripts/audit.sh
```

See [ARCHITECTURE.md](ARCHITECTURE.md) for the modelling rules, coverage check and bug report validator.

## Run the Julia reproducers

With Julia 1.12 or later, run from the repository root:

```sh
./test/lean/scripts/run-repros.sh
```

The runner uses this checkout of SymbolicRegression.jl. To run an individual check, instantiate the Julia project with `./test/lean/scripts/run-repros.sh --instantiate`, then run, for example:

```sh
julia --project=test/lean/repro test/lean/repro/loss-baseline-average.jl
```
