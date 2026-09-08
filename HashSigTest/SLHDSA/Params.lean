/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Params

/-!
# SLH-DSA parameter canaries

Executable checks for the twelve FIPS 205 parameter sets, their exact derived byte lengths, and
the boundary between raw and validated parameters. The expected values are written independently
of `FipsParameterSet.params` and `FipsParameterSet.expectedSizes` so a table mutation cannot make
both sides of a test change together.
-/

public section

namespace SLHDSA.ParamsTest

open FipsParameterSet

/-- Every standardized name is present exactly once and in the documented family-major order. -/
example : all.map name =
  ["SLH-DSA-SHA2-128s", "SLH-DSA-SHA2-128f", "SLH-DSA-SHA2-192s",
    "SLH-DSA-SHA2-192f", "SLH-DSA-SHA2-256s", "SLH-DSA-SHA2-256f",
    "SLH-DSA-SHAKE-128s", "SLH-DSA-SHAKE-128f", "SLH-DSA-SHAKE-192s",
    "SLH-DSA-SHAKE-192f", "SLH-DSA-SHAKE-256s", "SLH-DSA-SHAKE-256f"] := by
  decide

/-- The twelve names select the intended family independently of their shared numerical shapes. -/
example : all.map hashFamily =
  [.sha2, .sha2, .sha2, .sha2, .sha2, .sha2,
    .shake, .shake, .shake, .shake, .shake, .shake] := by
  decide

/-- Raw fields match the six FIPS 205 numerical shapes for both hash families. -/
example : all.map (fun ps =>
    let p := ps.params
    [p.n, p.h, p.d, p.hp, p.a, p.k, p.lgw]) =
  [[16, 63, 7, 9, 12, 14, 4], [16, 66, 22, 3, 6, 33, 4],
    [24, 63, 7, 9, 14, 17, 4], [24, 66, 22, 3, 8, 33, 4],
    [32, 64, 8, 8, 14, 22, 4], [32, 68, 17, 4, 9, 35, 4],
    [16, 63, 7, 9, 12, 14, 4], [16, 66, 22, 3, 6, 33, 4],
    [24, 63, 7, 9, 14, 17, 4], [24, 66, 22, 3, 8, 33, 4],
    [32, 64, 8, 8, 14, 22, 4], [32, 68, 17, 4, 9, 35, 4]] := by
  decide

/-- WOTS+ base, message digits, checksum digits, and total chains are derived independently. -/
example : all.map (fun ps =>
    let p := ps.params
    [p.w, p.len1, p.len2, p.len]) =
  [[16, 32, 3, 35], [16, 32, 3, 35],
    [16, 48, 3, 51], [16, 48, 3, 51],
    [16, 64, 3, 67], [16, 64, 3, 67],
    [16, 32, 3, 35], [16, 32, 3, 35],
    [16, 48, 3, 51], [16, 48, 3, 51],
    [16, 64, 3, 67], [16, 64, 3, 67]] := by
  decide

/-- The three independently rounded `H_msg` components match all six numerical shapes. -/
example : all.map (fun ps =>
    let p := ps.params
    [p.digestBytes, p.treeIdxBytes, p.leafIdxBytes]) =
  [[21, 7, 2], [25, 8, 1], [30, 7, 2], [33, 8, 1], [39, 7, 1], [40, 8, 1],
    [21, 7, 2], [25, 8, 1], [30, 7, 2], [33, 8, 1], [39, 7, 1], [40, 8, 1]] := by
  decide

/-- `H_msg`, public-key, secret-key, and signature lengths are derived from the raw formulas. -/
example : all.map (fun ps =>
    let p := ps.params
    [p.m, p.publicKeyBytes, p.secretKeyBytes, p.signatureBytes]) =
  [[30, 32, 64, 7856], [34, 32, 64, 17088],
    [39, 48, 96, 16224], [42, 48, 96, 35664],
    [47, 64, 128, 29792], [49, 64, 128, 49856],
    [30, 32, 64, 7856], [34, 32, 64, 17088],
    [39, 48, 96, 16224], [42, 48, 96, 35664],
    [47, 64, 128, 29792], [49, 64, 128, 49856]] := by
  decide

/-- Every approved set and the explicitly nonstandard reduced profile validates. -/
example : all.all (fun ps => ps.params.validate.isSome) = true := by decide
example : slhdsaSha2_128_24.validate.isSome = true := by decide

/-- Zero node length is rejected even when the layer equation still holds. -/
example : (Params.validate
    { n := 0, h := 63, d := 7, hp := 9, a := 12, k := 14, lgw := 4 }).isNone = true := by
  decide

/-- Zero layers are rejected. -/
example : (Params.validate
    { n := 16, h := 0, d := 0, hp := 9, a := 12, k := 14, lgw := 4 }).isNone = true := by
  decide

/-- Zero per-layer height is rejected. -/
example : (Params.validate
    { n := 16, h := 0, d := 7, hp := 0, a := 12, k := 14, lgw := 4 }).isNone = true := by
  decide

/-- Zero FORS tree height is rejected. -/
example : (Params.validate
    { n := 16, h := 2, d := 1, hp := 2, a := 0, k := 1, lgw := 4 }).isNone = true := by
  decide

/-- An empty FORS forest is rejected. -/
example : (Params.validate
    { n := 16, h := 2, d := 1, hp := 2, a := 1, k := 0, lgw := 4 }).isNone = true := by
  decide

/-- Zero Winternitz exponent is rejected. -/
example : (Params.validate
    { n := 16, h := 63, d := 7, hp := 9, a := 12, k := 14, lgw := 0 }).isNone = true := by
  decide

/-- An off-by-one total height is rejected despite all primary fields being positive. -/
example : (Params.validate
    { n := 16, h := 64, d := 7, hp := 9, a := 12, k := 14, lgw := 4 }).isNone = true := by
  decide

/-- WOTS+ parameters that require more than the available `n` input bytes are rejected. -/
example : (Params.validate
    { n := 1, h := 2, d := 1, hp := 2, a := 1, k := 1, lgw := 3 }).isNone = true := by
  decide

/-- Input alignment is general: a non-FIPS profile with `lgw = 3` validates when `3 ∣ 8n`. -/
example : (Params.validate
    { n := 3, h := 2, d := 1, hp := 2, a := 1, k := 1, lgw := 3 }).isSome = true := by
  decide

/-- The reduced profile remains distinct from every approved FIPS arithmetic shape. -/
example : slhdsaSha2_128_24.IsLimited := rfl

example : ¬slhdsaSha2_128_24.IsFipsShape := by
  intro h
  obtain ⟨ps, hps⟩ := h
  cases ps <;> simp [FipsParameterSet.params, slhdsaSha2_128_24,
    LimitedParameterSet.params] at hps

end SLHDSA.ParamsTest
