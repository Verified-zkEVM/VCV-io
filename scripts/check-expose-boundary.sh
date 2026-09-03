#!/usr/bin/env bash
# scripts/check-expose-boundary.sh
#
# Keep broad exposure from growing while VCVio moves to opaque public APIs. The baseline is a
# per-library ceiling on the number of Lean files that open a broad `@[expose] public section`
# (the compatibility-first migration default). A library absent from the baseline has a ceiling
# of zero, so a library that has been converted to selective exposure cannot silently regain a
# broadly exposed file.
#
# This is a syntactic ratchet, not a transparency analysis: per-declaration `@[expose]` is the
# intended replacement and is never counted, and `import all` in proof modules is unaffected.
# Lower counts are always accepted; a higher count needs an explicit, reviewable baseline change.
#
# Modes:
#   * ceiling (default) -- hard gate. No library may exceed its baseline count.
#   * report            -- advisory. Prints the per-library delta against a base ref.
#
# Usage:
#   scripts/check-expose-boundary.sh                 # ceiling check
#   scripts/check-expose-boundary.sh --report [REF]  # ceiling + advisory delta vs REF (default origin/main)
#   scripts/check-expose-boundary.sh --update-baseline
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

BASELINE="${EXPOSE_BOUNDARY_BASELINE:-scripts/expose_boundary_baseline.tsv}"
# Overridable so scripts/test-expose-boundary.sh can exercise this against fixtures.
if [[ -n "${EXPOSE_BOUNDARY_LIBS:-}" ]]; then
  read -r -a LIBS <<< "$EXPOSE_BOUNDARY_LIBS"
else
  LIBS=(VCVio ToMathlib LatticeCrypto HashSig Examples Extern VCVioWidgets VCVioTest
    LatticeCryptoTest HashSigTest)
fi

# Count, per library, the files that open a broad exposed public section.
count_tree() {
  local tree_root="$1"
  local output="$2"
  (
    cd "$tree_root"
    for lib in "${LIBS[@]}"; do
      [[ -d "$lib" ]] || continue
      # `grep -l` exits 1 on no matches, which is a legitimate count of zero under `pipefail`.
      count="$( (grep -rlE --include='*.lean' '^@\[expose\][[:space:]]+public[[:space:]]+section' "$lib" \
        || true) | wc -l | tr -d ' ')"
      printf '%s\t%s\n' "$lib" "$count"
    done
  ) | sort > "$output"
}

CURRENT="$(mktemp "${TMPDIR:-/tmp}/vcvio-expose-boundary.XXXXXX")"
BASE_COUNTS="$(mktemp "${TMPDIR:-/tmp}/vcvio-expose-basecounts.XXXXXX")"
BASE_TREE=""
cleanup() {
  rm -f "$CURRENT" "$BASE_COUNTS"
  if [[ -n "$BASE_TREE" && -d "$BASE_TREE" ]]; then
    rm -rf -- "$BASE_TREE"
  fi
}
trap cleanup EXIT

count_tree "$REPO_ROOT" "$CURRENT"

if [[ "${1:-}" == "--update-baseline" ]]; then
  cp "$CURRENT" "$BASELINE"
  echo "Expose boundary: updated $BASELINE."
  exit 0
fi

MODE="ceiling"
COMPARE_BASE="origin/main"
if [[ "${1:-}" == "--report" ]]; then
  MODE="report"
  if [[ -n "${2:-}" ]]; then
    COMPARE_BASE="$2"
    shift
  fi
  shift
fi

if (( $# > 0 )); then
  echo "Expose boundary: unknown argument '$1'." >&2
  exit 2
fi

if [[ ! -f "$BASELINE" ]]; then
  echo "Expose boundary: missing $BASELINE; run with --update-baseline." >&2
  exit 2
fi

if [[ "$MODE" == "report" ]]; then
  if git rev-parse --verify --quiet "$COMPARE_BASE" >/dev/null; then
    BASE_TREE="$(mktemp -d "${TMPDIR:-/tmp}/vcvio-expose-base-tree.XXXXXX")"
    if ! git archive "$COMPARE_BASE" -- "${LIBS[@]}" 2>/dev/null | tar -x -C "$BASE_TREE"; then
      echo "Expose boundary: could not materialize base ref '$COMPARE_BASE'; ceiling only." >&2
      MODE="ceiling"
    else
      count_tree "$BASE_TREE" "$BASE_COUNTS"
    fi
  else
    echo "Expose boundary: base ref '$COMPARE_BASE' not found; ceiling only." >&2
    MODE="ceiling"
  fi
fi

# awk for portability (macOS bash 3.2 has no associative arrays).
awk -F'\t' -v baseFile="$BASELINE" -v curFile="$CURRENT" -v baseCountsFile="$BASE_COUNTS" \
  -v mode="$MODE" -v compareBase="$COMPARE_BASE" '
function err(msg) { print msg > "/dev/stderr" }
FILENAME == baseFile { if ($1 != "") base[$1] = $2 + 0; next }
FILENAME == curFile { if ($1 != "") cur[$1] = $2 + 0; next }
FILENAME == baseCountsFile { if ($1 != "") were[$1] = $2 + 0; next }
END {
  violations = 0
  for (lib in cur) {
    limit = (lib in base) ? base[lib] : 0
    if (cur[lib] > limit) {
      err("ERROR: " lib " has " cur[lib] " broadly exposed file(s); baseline ceiling is " limit ".")
      violations++
    }
  }
  if (violations > 0) {
    err("Expose boundary: " violations " library(ies) gained a broad `@[expose] public section`.")
    err("Expose individual definitions instead, or update the baseline with explicit review.")
    exit 1
  }
  if (mode == "ceiling") { print "Expose boundary: OK."; exit 0 }
  print "Expose boundary: OK. Broadly exposed files vs " compareBase ":"
  for (lib in cur) {
    was = (lib in were) ? were[lib] : 0
    delta = cur[lib] - was
    printf "  %-20s %4d -> %4d  (%+d)\n", lib, was, cur[lib], delta
  }
  exit 0
}' "$BASELINE" "$CURRENT" "$BASE_COUNTS"
