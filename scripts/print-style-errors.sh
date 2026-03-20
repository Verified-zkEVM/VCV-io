#!/usr/bin/env bash

set -euo pipefail
IFS=$'\n\t'

# Bridge the remaining Python-only style checks into `lake exe lint-style`.
touch scripts/style-exceptions.txt

find VCVio -name '*.lean' -print0 \
  | xargs -0 python3 ./scripts/lint-style.py "$@" \
  | LC_ALL=C sort || true
find Examples -name '*.lean' -print0 \
  | xargs -0 python3 ./scripts/lint-style.py "$@" \
  | LC_ALL=C sort || true
