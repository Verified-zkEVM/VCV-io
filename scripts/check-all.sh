#!/usr/bin/env bash
# Local strict-superset build check.
#
# Builds every Lean library in the repo, including the test libraries that the
# main CI workflow does not build. CI tracks ToMathlib, VCVio, FFI, LatticeCrypto,
# Examples, VCVioWidgets, and Interop (plus the VCVioTest/Smoke.lean smoke test);
# VCVioTest and LatticeCryptoTest are not built in CI but still exercise the
# public APIs, so they can drift silently after refactors. Run this before
# pushing to catch such drift locally.
#
# The three `LatticeCryptoTest/*/Main.lean` runners each define a top-level
# `def main` and cannot coexist in the umbrella `LatticeCryptoTest.lean`
# import file (Lean's pattern-match elaborator generates colliding
# `main.match_NN` names). They are built as individual modules here.
#
# Executable targets (smoke_test, mlkem_test, mldsa_test, falcon_test) are not
# built here: they require native submodules under third_party/ and a C
# toolchain. Use `git submodule update --init --recursive && lake build <exe>`
# for those.

set -euo pipefail

lake build \
  ToMathlib VCVio FFI LatticeCrypto Examples VCVioWidgets Interop \
  VCVioTest LatticeCryptoTest \
  LatticeCryptoTest.Falcon.Main \
  LatticeCryptoTest.MLDSA.Main \
  LatticeCryptoTest.MLKEM.Main

lake env lean VCVioTest/Smoke.lean
