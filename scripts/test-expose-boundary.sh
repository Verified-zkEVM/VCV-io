#!/usr/bin/env bash
# scripts/test-expose-boundary.sh
#
# Exercise check-expose-boundary.sh against fixtures: the per-library count of broadly exposed
# files, the zero ceiling for a library absent from the baseline, acceptance of decreases,
# rejection of increases, and the advisory report against a base ref.
#
# The checker resolves its repo root from its own location, so the fixtures live in a throwaway
# git repository with the script copied into it.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
CHECKER_SRC="$REPO_ROOT/scripts/check-expose-boundary.sh"
FIXTURE_REPO="$(mktemp -d)"
trap 'rm -rf "$FIXTURE_REPO"' EXIT

mkdir -p "$FIXTURE_REPO/scripts" "$FIXTURE_REPO/Lib" "$FIXTURE_REPO/Other"
cp "$CHECKER_SRC" "$FIXTURE_REPO/scripts/check-expose-boundary.sh"
CHECKER="$FIXTURE_REPO/scripts/check-expose-boundary.sh"

export EXPOSE_BOUNDARY_LIBS="Lib Other"

cd "$FIXTURE_REPO"
git init -q .
git config user.email fixture@example.com
git config user.name Fixture

# Counted: a file opening a broad exposed section. Not counted: plain `public section`,
# per-declaration `@[expose]`, or the phrase inside a comment.
printf '%s\n' 'module' '' '@[expose] public section' '' 'def a : Nat := 0' > Lib/Broad.lean
printf '%s\n' 'module' '' 'public section' '' '@[expose] def b : Nat := 0' > Lib/Selective.lean
printf '%s\n' 'module' '' '-- @[expose] public section is mentioned here only' 'public section' \
  'def c : Nat := 0' > Other/Comment.lean

"$CHECKER" --update-baseline >/dev/null
lib_count="$(awk -F'\t' '$1 == "Lib" { print $2 }' scripts/expose_boundary_baseline.tsv)"
other_count="$(awk -F'\t' '$1 == "Other" { print $2 }' scripts/expose_boundary_baseline.tsv)"
if [[ "$lib_count" != "1" || "$other_count" != "0" ]]; then
  echo "ERROR: expected Lib=1 Other=0 broadly exposed files, got Lib=${lib_count:-?} Other=${other_count:-?}." >&2
  exit 1
fi

git add -A
git commit -qm 'fixture: baseline'
BASE="$(git rev-parse HEAD)"

"$CHECKER" >/dev/null

# A second broadly exposed file in Lib exceeds the ceiling.
printf '%s\n' 'module' '' '@[expose] public section' '' 'def d : Nat := 0' > Lib/Broad2.lean
if "$CHECKER" >/dev/null 2>&1; then
  echo 'ERROR: a new broadly exposed file was not rejected by the ceiling.' >&2
  exit 1
fi
rm Lib/Broad2.lean

# A broadly exposed file in a library with a zero ceiling is rejected.
printf '%s\n' 'module' '' '@[expose] public section' '' 'def e : Nat := 0' > Other/Broad.lean
if "$CHECKER" >/dev/null 2>&1; then
  echo 'ERROR: a broadly exposed file in a zero-ceiling library was not rejected.' >&2
  exit 1
fi
rm Other/Broad.lean

# Converting the broad file to selective exposure is accepted, and the report shows the delta.
printf '%s\n' 'module' '' 'public section' '' '@[expose] def a : Nat := 0' > Lib/Broad.lean
"$CHECKER" >/dev/null
report="$("$CHECKER" --report "$BASE")"
if ! grep -q 'Lib.*1 ->.*0.*(-1)' <<<"$report"; then
  echo "ERROR: report did not show Lib decreasing from 1 to 0:" >&2
  echo "$report" >&2
  exit 1
fi

# An unknown argument is a usage error.
if "$CHECKER" --bogus >/dev/null 2>&1; then
  echo 'ERROR: an unknown argument was accepted.' >&2
  exit 1
fi

echo 'test-expose-boundary: OK.'
