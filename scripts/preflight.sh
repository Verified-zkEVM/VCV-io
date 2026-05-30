#!/usr/bin/env bash
# Run the same checks CI runs, in the same order, fail-fast.
# Intended as a single pre-push gate for contributors.

set -euo pipefail

cd "$(dirname "$0")/.."

section() {
  printf '\n\033[1;34m==> %s\033[0m\n' "$1"
}

section "lake build"
lake build

section "lake lint (batteries/runLinter)"
lake lint

section "lake exe mathlib/lint-style"
lake exe mathlib/lint-style ToMathlib VCVio FFI LatticeCrypto Examples VCVioWidgets Interop

section "lake exe mk_all --check (per library)"
for lib in ToMathlib VCVio FFI LatticeCrypto Examples VCVioWidgets Interop; do
  printf '  -- %s\n' "$lib"
  lake exe mk_all --lib "$lib" --check
done

section "scripts/check-interop-isolation.sh"
bash scripts/check-interop-isolation.sh

section "scripts/check-agent-docs.py"
python3 scripts/check-agent-docs.py

section "scripts/extract-doc-fragments.py --check"
python3 scripts/extract-doc-fragments.py --check

printf '\n\033[1;32mAll preflight checks passed\033[0m\n'
