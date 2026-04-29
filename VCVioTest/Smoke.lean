/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio

/-!
# VCVio Smoke Test

Minimal executable that imports the full VCVio library and runs a trivial computation.
Used by CI to measure build timing and verify the library typechecks end-to-end.
-/


def main : IO Unit := do
  IO.println "VCVio smoke test OK"
