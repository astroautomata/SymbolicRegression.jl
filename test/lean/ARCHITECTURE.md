# Lean formalization of SymbolicRegression.jl

This directory models the Julia package in `../../src` at commit
`103f5d4299222fa4af70110f4886ced4f3fdac1b` in Lean 4. It uses the Lean
standard library and reuses the runtime model, trees, node heap, traversals,
sampling and registry types from the pinned DynamicExpressions.jl project
in `lakefile.toml`.

Properties are **proven** when Lean checks a proof, **refuted** when Lean
checks a counterexample and a Julia script reproduces the corresponding
behaviour, or **todo** when neither has been established.

Follow the modelling rules in the
[DynamicExpressions.jl architecture guide](https://github.com/SymbolicML/DynamicExpressions.jl/blob/097eaa548dcf7525dd1f9aa4d1504beb2795f467/test/lean/ARCHITECTURE.md).
Mirror the Julia control flow with `file:line` citations, never fix Julia
in the model, quantify each property over its
inputs, state reasonable-input preconditions explicitly and show them satisfiable with an
`example`, and never write `sorry`, `admit` or `native_decide` anywhere in a `.lean` file.
The only allowed axioms are `propext`, `Classical.choice`, `Quot.sound` and those in
`DynExpr.Runtime.Axioms`.

## Layout

| Path | Contents |
|---|---|
| `SymReg/HeapLemmas.lean` | Public lemmas about DE's node heap (`unfold_succ`, `getChildren_active`, `tmrH_plain`, ...). |
| `SymReg/Complexity.lean`, `SymReg/Constraints*.lean`, `SymReg/Crossover*.lean` | First slices: `compute_complexity`, `check_constraints`, `crossover_trees`. |
| `SymReg/<Slice>.lean`, `SymReg/<Slice>/` | One slice per group of Julia files; the slice root imports its files and defines `SymReg.<Slice>.entries`. |
| Slices | `Loss` (`LossFunctions.jl`), `HofMig` (`HallOfFame.jl`, `Migration.jl`), `SimpCons` (simplification wrappers, remaining `CheckConstraints.jl`), `Population` (`Population.jl`, `RegularizedEvolution.jl`), `MutateGen` (`Mutate.jl`, `MutationWeights.jl`), `Mutations` (`MutationFunctions.jl`), `Search` (`SymbolicRegression.jl`, `SearchUtils.jl`), `Plugins` (`Plugin.jl`, `plugins/`), `Options` (`Options.jl`, `OptionsStruct.jl`), `MLJ` (`MLJInterface.jl`), `Templates` (`TemplateExpression*.jl`, `ComposableExpression.jl`, `ExpressionBuilder.jl`, `ExpressionSpec.jl`), `ConstOpt` (`ConstantOptimization.jl`), `Interface` (`InterfaceDynamicExpressions.jl`, `InterfaceDataTypes.jl`), `Ext` (`ext/SymbolicRegression*Ext.jl`: Enzyme, Mooncake, SymbolicUtils, JSON, Tables, PythonCall), `Operators` (`Operators.jl`), `Infra` (`Configure.jl`, `Logging.jl`, `Tracing.jl`, `ProgressBars.jl`, `deprecates.jl`, `precompile.jl`), `CrossMut` (`Crossover.jl`, `Crossovers.jl`, `Mutations.jl`, `Utils.jl`; `Core.jl` and `ProgramConstants.jl` have nothing input-dependent), `Units` (`DimensionalAnalysis.jl`, `InterfaceDynamicQuantities.jl`), `Backsolve` (`Backsolve.jl`, `EvaluateInverse.jl`, `InverseFunctions.jl`). |
| `SymReg/Registry.lean` | Every registry entry (`SymReg.Registry.all`), concatenating the slices. |
| `SymReg/Registry/AuditCore.lean` | The audit checks (`SymReg.Registry.audit`). |
| `Audit.lean`, `Report.lean`, `Restating.lean` | Registry audit, tab-separated report, and checks for overlapping properties. |
| `bugs/` | YAML reports for refuted properties, with observed Julia output. |
| `registry.tsv` | Generated registry table (id, status, kind, quantified variables, file, statement, preconditions). |
| `QUESTIONS.md` | Open questions about the intended behaviour of the Julia code. |
| `repro/` | Julia project using this checkout, with scripts that print `REPRODUCED <id>` for each counterexample they reproduce. |
| `scripts/` | Audit, proof-escape, short-circuit, bug report, coverage and reproducer checks. |

## Building and running

See [README.md](README.md) for build and reproducer commands. To report which
Julia files and public exports the registry names, run the audit, instantiate
the reproducer project, then run from the repository root:

```sh
julia --project=test/lean/repro test/lean/scripts/check-coverage.jl test/lean/.lake/audit.out
```

Coverage counts registry references, including open properties. It reports
missing entries without requiring full coverage.

## Audit

`scripts/audit.sh` builds the model, scans Lean code for proof escapes,
rejects new short-circuit hoists, and checks the registry. The audit checks
the types and axioms of proofs and refutations, reports open `todo` entries,
and fails on `stuck` entries. For a monadic action on the right of a Julia
`&&` or `||`, use Lean's `<&&>` or `<||>` so the action runs only when Julia
would run it.

After changing registry entries, run the audit and copy
`test/lean/.lake/registry.tsv` to `test/lean/registry.tsv`.

`Restating.lean` reports definitionally equal properties and partially
matching properties to review. Its results are advisory.

## Bug reports

Use `bugs/schema.yaml.example` as a template for `bugs/<id>.yaml`. The id
must be a refuted registry entry with a matching `repro/<id>.jl`. Record
the Julia version, SR commit and DE version under `runtime` and keep the
runtime output verbatim under `runtime.output`. Record the declaration
names under `lean.property` and `lean.theorem`. If one report covers more
refuted entries with the same cause, record those ids under `covers` and
exercise each in the reproducer. Validate reports from `test/lean/`:

```bash
uv run --no-project --with pyyaml python scripts/check_bugs.py
```

- **P0**: Crash, hang, memory unsafety, or a silently wrong result on inputs
  that ordinary code produces.
- **P1**: Silently wrong result or a missing promised error on edge inputs
  that real code can plausibly reach, such as empty collections or extreme
  integers.
- **P2**: Wrong exception type, inconsistent behaviour between methods, or
  silently wrong results only on contrived inputs.
- **P3**: Documentation contradicts arguably correct behaviour, or the
  problem is cosmetic.
