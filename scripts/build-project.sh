#!/usr/bin/env bash
# scripts/build-project.sh
#
# Thin alias kept for muscle memory: the routine local validation lives in scripts/validate.sh.
# `build-project.sh` runs the default checks plus the test driver; `build-project.sh --ffi` adds
# the native-backed ML-KEM / ML-DSA / Falcon executables (compiles the vendored C backends in
# third_party/, which is why it is opt-in; the same coverage runs nightly in CI).
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [[ "${1:-}" == "--ffi" ]]; then
  exec "$REPO_ROOT/scripts/validate.sh" --test --ffi
fi
exec "$REPO_ROOT/scripts/validate.sh" --test "$@"
