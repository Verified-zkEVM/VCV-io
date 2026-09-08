#!/usr/bin/env bash
# scripts/check-imports.sh
#
# Verify that every generated umbrella module lists exactly the modules of its library:
# regenerate the umbrellas with scripts/update-lib.sh and fail if that changes any of them. The
# umbrellas are restored on exit, so a failing check leaves the working tree as it was.
#
# `lake exe mk_all --check` cannot be used bare here: it would iterate the curated
# `LatticeCryptoTest.lean`, the umbrella-less `HashSigTest`, and the axiom-sweep fixtures.
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

UMBRELLAS=(ToMathlib.lean VCVio.lean LatticeCrypto.lean Extern.lean HashSig.lean Examples.lean
  VCVioWidgets.lean VCVioTest.lean Interop.lean)

# A missing umbrella must fail before regeneration: otherwise it would be created without
# comparison or an original file to restore, silently turning this check into a repair.
for f in "${UMBRELLAS[@]}"; do
  if [[ ! -f "$f" ]]; then
    echo "ERROR: required umbrella $f is missing; run ./scripts/update-lib.sh." >&2
    exit 1
  fi
done

STASH="$(mktemp -d "${TMPDIR:-/tmp}/vcvio-umbrellas.XXXXXX")"
restore() {
  local f
  for f in "${UMBRELLAS[@]}"; do
    if [[ -f "$STASH/$f" ]]; then cp "$STASH/$f" "$f"; fi
  done
  rm -rf "$STASH"
}
trap restore EXIT

for f in "${UMBRELLAS[@]}"; do
  if [[ -f "$f" ]]; then cp "$f" "$STASH/$f"; fi
done

./scripts/update-lib.sh >/dev/null

stale=0
for f in "${UMBRELLAS[@]}"; do
  if [[ -f "$STASH/$f" ]] && ! cmp -s "$STASH/$f" "$f"; then
    echo "ERROR: $f is out of date:" >&2
    diff -u "$STASH/$f" "$f" >&2 || true
    stale=1
  fi
done

if (( stale )); then
  echo "Run ./scripts/update-lib.sh and commit the regenerated umbrella modules." >&2
  exit 1
fi
echo "Umbrella modules are up to date."
