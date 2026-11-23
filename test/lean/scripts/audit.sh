#!/usr/bin/env bash
# Build the Lean project, run source checks, and audit the registry.
# Writes test/lean/.lake/audit.out and test/lean/.lake/registry.tsv.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

python3 scripts/check-proof-escapes.py
python3 scripts/check-hoist.py
lake build

lake env lean Audit.lean | tee .lake/audit.out
lake env lean -M8000 Report.lean > .lake/registry.tsv
cat .lake/registry.tsv
awk '
    /^ENTRIES [0-9]+$/ { entries = $2 }
    /^STATUS / { sub(/^.*\./, "", $2); counts[$2] = $3 }
    END {
        if (entries == "" || entries != counts["proven"] + counts["refuted"] + counts["todo"] + counts["stuck"]) {
            print "FAIL inconsistent registry audit counts" > "/dev/stderr"
            exit 1
        }
        printf "REGISTRY entries=%d proven=%d refuted=%d todo=%d\n", entries, counts["proven"], counts["refuted"], counts["todo"]
    }
' .lake/audit.out
