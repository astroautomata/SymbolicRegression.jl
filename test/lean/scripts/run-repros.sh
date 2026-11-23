#!/usr/bin/env bash
# Run the reproducers against this SymbolicRegression.jl checkout.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

if [[ $# -gt 0 && ( $# != 1 || $1 != --instantiate ) ]]; then
    echo "usage: scripts/run-repros.sh [--instantiate]" >&2
    exit 2
fi
julia --startup-file=no --project=repro -e '
    using Pkg
    Pkg.instantiate()
    using SymbolicRegression
    realpath(pkgdir(SymbolicRegression)) == realpath("../..") || error("Expected the local SymbolicRegression checkout")
    using DynamicExpressions
    println("RUNTIME julia=", VERSION, " de=", pkgversion(DynamicExpressions))
'
if [[ $# -eq 1 ]]; then exit 0; fi

shopt -s nullglob
scripts=(repro/*.jl)
if [[ ${#scripts[@]} -eq 0 ]]; then
    echo "FAIL no reproducers in repro/" >&2
    exit 1
fi

succeeded=0
for script in "${scripts[@]}"; do
    id=${script##*/}
    id=${id%.jl}
    status=0
    output=$(julia --startup-file=no --project=repro "$script" </dev/null 2>&1) || status=$?
    printf '%s\n' "$output"
    if [[ $status -ne 0 ]]; then
        echo "FAIL $id: Julia exited $status" >&2
    elif grep -Fxq "REPRODUCED $id" <<<"$output"; then
        succeeded=$((succeeded + 1))
    else
        echo "FAIL $id: expected 'REPRODUCED $id'" >&2
    fi
done
echo "REPROS $succeeded/${#scripts[@]}"
[[ $succeeded -eq ${#scripts[@]} ]]
