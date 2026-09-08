#!/usr/bin/env bash
# scripts/validate.sh
#
# Routine local validation: the fast checks shared with CI, in CI order, from one command. Flags
# add the slower test, environment-lint, axiom, and native-FFI passes. Nothing here builds the native
# FFI test executables unless `--ffi` is given (that path compiles the vendored C backends).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

run_lint=0
run_test=0
run_ffi=0
run_axioms=0

usage() {
  cat <<'EOF'
Usage: ./scripts/validate.sh [--lint] [--test] [--ffi] [--axioms]

Default fast checks (shared with per-PR CI):
  - lake build of the seven proof libraries, with the non-sorry warning budget
  - ./scripts/check-imports.sh (generated umbrella modules are current)
  - the boundary ratchets: PolyFun, PMF/SPMF, broad expose, complexity backend,
    Extern and Interop isolation
  - lake exe lint-style on every library and test module
  - python3 ./scripts/check-agent-docs.py and extract-doc-fragments.py --check

Optional checks:
  --lint    Batteries environment linters, one process per proof library as in CI
  --test    lake test (test libraries, the SLH-DSA test executables, the smoke test)
  --ffi     with --test: also the native ML-KEM / ML-DSA / Falcon executables
            (initialises the third_party/ submodules; slow)
  --axioms  ./scripts/test-axiomsweep.sh, then lake exe axiomsweep --check
EOF
}

for arg in "$@"; do
  case "$arg" in
    --lint) run_lint=1 ;;
    --test) run_test=1 ;;
    --ffi) run_ffi=1 ;;
    --axioms) run_axioms=1 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "ERROR: unknown flag: $arg" >&2; usage >&2; exit 1 ;;
  esac
done

if (( run_ffi )) && ! (( run_test )); then
  echo "ERROR: --ffi needs --test." >&2
  exit 1
fi

PROOF_LIBS=(ToMathlib VCVio LatticeCrypto Extern HashSig Examples VCVioWidgets)
BUILD_LOG="$(mktemp "${TMPDIR:-/tmp}/vcvio-validate-build.XXXXXX")"
trap 'rm -f "$BUILD_LOG"' EXIT

echo "# Building the proof libraries"
lake build "${PROOF_LIBS[@]}" 2>&1 | tee "$BUILD_LOG"

echo ""
echo "# Checking the warning budget"
warning_args=()
for lib in "${PROOF_LIBS[@]}"; do
  warning_args+=(--path-prefix "$lib/" --path-prefix "$lib.lean")
done
python3 ./scripts/check-warning-log.py "$BUILD_LOG" "${warning_args[@]}" \
  --exclude-substring 'declaration uses `sorry`' \
  --label 'repository non-sorry warnings'

echo ""
echo "# Checking generated umbrella modules"
python3 ./scripts/test-check-imports.py
./scripts/check-imports.sh

echo ""
echo "# Checking boundaries"
bash scripts/test-polyfun-boundary.sh
bash scripts/check-polyfun-boundary.sh
bash scripts/test-pmf-boundary.sh
bash scripts/check-pmf-boundary.sh
if [[ -f scripts/check-expose-boundary.sh ]]; then
  bash scripts/test-expose-boundary.sh
  bash scripts/check-expose-boundary.sh
fi
bash scripts/test-complexity-backend-isolation.sh
bash scripts/check-complexity-backend-isolation.sh
bash scripts/check-extern-isolation.sh
bash scripts/check-interop-isolation.sh

echo ""
echo "# Running the text-based style linters"
# `lake exe lint-style` resolves to Mathlib's linter (the project defines no `lint-style` exe, so
# no FFI backend is linked). Libraries are passed by name; the test modules are expanded from git
# because `HashSigTest` has no umbrella and `LatticeCryptoTest.lean` is curated.
test_modules=()
while IFS= read -r module; do
  test_modules+=("$module")
done < <(git ls-files 'VCVioTest/*.lean' 'LatticeCryptoTest/*.lean' \
  'HashSigTest/*.lean' | sed -e 's/\.lean$//' -e 's#/#.#g')
lake exe lint-style "${PROOF_LIBS[@]}" Interop "${test_modules[@]}"

echo ""
echo "# Checking the agent documentation"
python3 ./scripts/check-agent-docs.py
python3 ./scripts/extract-doc-fragments.py --check

if (( run_lint )); then
  echo ""
  echo "# Running the environment linters"
  # One process per library bounds peak memory. A single `lake lint` process retains each imported
  # environment and has exceeded the hosted runner's memory after a full build.
  for lib in "${PROOF_LIBS[@]}"; do
    lake exe runLinter --no-build "$lib"
  done
fi

if (( run_test )); then
  echo ""
  echo "# Running lake test"
  if (( run_ffi )); then
    git submodule update --init --recursive
    lake test -- --ffi
  else
    lake test
  fi
fi

if (( run_axioms )); then
  echo ""
  echo "# Checking axiom and sorry debt"
  ./scripts/test-axiomsweep.sh
  lake exe axiomsweep --check
fi

echo ""
echo "validate: OK."
