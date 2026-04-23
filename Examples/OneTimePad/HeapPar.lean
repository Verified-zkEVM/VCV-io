/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.OneTimePad.HeapBasic

/-!
# Two parallel OTP channels via `Package.par`

Pilot demonstration of HeapSSP's parallel-composition machinery on
the One-Time Pad. Take the single-channel `realPkg` / `idealPkg`
from `HeapBasic.lean` and form

* `pairRealPkg sp := (realPkg sp).par (realPkg sp)` with state
  `Heap (KeyIdent sp ⊕ KeyIdent sp)` (two independent key cells), and
* `pairIdealPkg sp := (idealPkg sp).par (idealPkg sp)` with state
  `Heap (PEmpty ⊕ PEmpty)` (still trivially stateless on each side).

The composite export `otpSpec sp + otpSpec sp` exposes two channels:
`Sum.inl (.enc m)` routes to the first OTP (under key `key_α`),
`Sum.inr (.enc m)` routes to the second (under key `key_β`).

## What this file builds

* `encOnceL sp m`, `encOnceR sp m` are single-call adversaries that
  hit the left or right channel.
* `encOncePair sp m₁ m₂` issues one query on each channel and pairs
  the ciphertexts.
* `evalDist_run_encOncePair_eq` is the headline two-channel
  indistinguishability. **Currently a `sorry`**, pending the HeapSSP
  `DistEquiv` / `IndistAt` infrastructure (mirror of `VCVio/SSP/`).
  The intended cut is "single-channel `realPkg ≡ᵈ idealPkg`, lifted
  through `par_left_congr` / `par_right_congr` plus transitivity".

## What `Package.par` buys here vs. a flat product state

In the SSP product-state model, building a two-channel OTP would
yield state type `(Option (BitVec sp)) × (Option (BitVec sp))` (or
similar), with an explicit "left handler reads `.1`, writes back
to `.1`, leaves `.2` alone" frame to discharge by hand each time.
HeapSSP gives this frame *structurally* via `Heap.split`: the two
channel handlers each touch only one half of the heap, with the
other half threaded as an opaque parameter, and frame reasoning
reduces to `Heap.split_apply_inl` / `Heap.split_apply_inr` plus the
right inverse `Heap.split.symm ∘ Heap.split = id` (definitional
after `cases`).
-/

open OracleSpec OracleComp ENNReal

namespace VCVio.HeapSSP.OneTimePad

/-! ## Parallel OTP packages -/

/-- The two-channel real OTP package: two independent OTP keys live
in the cells `KeyIdent sp ⊕ KeyIdent sp`.

The composite imports `unifSpec + unifSpec` (one uniform-sampling
oracle per child, threaded through `liftComp`) and exports
`otpSpec sp + otpSpec sp` (one encryption channel per child). -/
def pairRealPkg (sp : ℕ) :
    Package (unifSpec + unifSpec) (otpSpec sp + otpSpec sp)
      (KeyIdent sp ⊕ KeyIdent sp) :=
  (realPkg sp).par (realPkg sp)

/-- The two-channel ideal OTP package: both channels are
stateless (cells `PEmpty ⊕ PEmpty`); each query samples a fresh
uniform ciphertext. -/
def pairIdealPkg (sp : ℕ) :
    Package (unifSpec + unifSpec) (otpSpec sp + otpSpec sp)
      (PEmpty.{1} ⊕ PEmpty.{1}) :=
  (idealPkg sp).par (idealPkg sp)

/-! ## Single-channel adversaries -/

/-- Single-call adversary on the **left** channel: issues one
`enc m` query routed to the first OTP. -/
def encOnceL (sp : ℕ) (m : BitVec sp) :
    OracleComp (otpSpec sp + otpSpec sp) (BitVec sp) :=
  (otpSpec sp + otpSpec sp).query (Sum.inl (OTPOp.enc m))

/-- Single-call adversary on the **right** channel: issues one
`enc m` query routed to the second OTP. -/
def encOnceR (sp : ℕ) (m : BitVec sp) :
    OracleComp (otpSpec sp + otpSpec sp) (BitVec sp) :=
  (otpSpec sp + otpSpec sp).query (Sum.inr (OTPOp.enc m))

/-- Two-call adversary: encrypt `m₁` on the left channel, then
`m₂` on the right channel, and return both ciphertexts. -/
def encOncePair (sp : ℕ) (m₁ m₂ : BitVec sp) :
    OracleComp (otpSpec sp + otpSpec sp) (BitVec sp × BitVec sp) := do
  let c₁ ← encOnceL sp m₁
  let c₂ ← encOnceR sp m₂
  pure (c₁, c₂)

/-! ## Headline two-channel indistinguishability

The proof of this theorem is deferred until the HeapSSP `DistEquiv` /
`IndistAt` infrastructure is in place (mirror of `VCVio/SSP/`). The
intended cut is:

1. `realPkg sp ≡ᵈ idealPkg sp` at the single-channel level (via
   `HeapSSP.Package.DistEquiv.of_run_evalDist` reusing
   `evalDist_run_encOnce_eq` from `HeapBasic.lean`, **for single-call
   adversaries** -- OTP secrecy is single-query only).
2. Lift through `par_left_congr` / `par_right_congr` (to be added in
   `VCVio/HeapSSP/DistEquiv.lean` once basic API is in place) plus
   transitivity. -/

/-- **OTP two-channel indistinguishability (sorry, pending HeapSSP
dist-equiv layer).** The parallel real and ideal packages produce
the same output distribution on `encOncePair`. -/
theorem evalDist_run_encOncePair_eq (sp : ℕ) (m₁ m₂ : BitVec sp) :
    evalDist ((pairRealPkg sp).run (encOncePair sp m₁ m₂)) =
      evalDist ((pairIdealPkg sp).run (encOncePair sp m₁ m₂)) := by
  sorry

end VCVio.HeapSSP.OneTimePad
