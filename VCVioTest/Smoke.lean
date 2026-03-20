/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio

/-!
# VCVio Smoke Test

Minimal executable that imports the full VCVio library and runs a trivial computation.
Used by CI to measure build timing and verify the library typechecks end-to-end.
-/

set_option autoImplicit false

def main : IO Unit := do
  IO.println "VCVio smoke test OK"
