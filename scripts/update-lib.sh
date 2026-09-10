#!/usr/bin/env bash

set -euo pipefail

regenerate() {
  local status
  if lake exe mk_all "$@"; then
    return 0
  else
    status=$?
  fi
  # Upstream returns the number of changed files: one for a successful --lib update.
  # Verify the result so a Lake/compiler failure with the same exit code is not swallowed.
  if (( status != 1 )); then return "$status"; fi
  lake exe mk_all "$@" --check
}

# Active root umbrellas are generated as module files with public imports.
for library in ToMathlib VCVio LatticeCrypto Extern HashSig Examples VCVioWidgets VCVioTest; do
  regenerate --lib "$library" --module
done

# Interop is dormant and has not yet adopted module scopes.
regenerate --lib Interop
