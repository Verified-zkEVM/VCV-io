/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.OneTimePad.HeapBasic
import VCVio.StateSeparating.DistEquiv

/-!
# Two parallel OTP channels via `QueryImpl.Stateful.par`

Pilot demonstration of state-separating's parallel-composition machinery on
the One-Time Pad. Take the single-channel `realImpl` / `idealImpl`
from `HeapBasic.lean` and form

* `pairRealImpl sp := (realImpl sp).par (realImpl sp)` with state
  `Heap (UsedFlag ⊕ UsedFlag)` (one single-call gate per channel), and
* `pairIdealImpl sp := (idealImpl sp).par (idealImpl sp)` with the same
  state shape (each channel still single-call gated).

The composite export `otpSpec sp + otpSpec sp` exposes two channels:
`Sum.inl (.enc m)` routes to the first OTP, `Sum.inr (.enc m)`
routes to the second. The composite import `unifSpec + unifSpec`
threads each channel's uniform sampling through its own slot.

## What this file builds

* `encOnceL sp m`, `encOnceR sp m` are single-call adversaries that
  hit the left or right channel.
* `encOncePair sp m₁ m₂` issues one query on each channel and pairs
  the ciphertexts.
* `pairRealImpl_distEquiv_pairIdealImpl` is the headline two-channel
  *unconditional* distributional equivalence, proved by feeding the
  per-(query, heap) handler equality from
  `realImpl_impl_evalDist_idealImpl` (HeapBasic.lean) into
  `QueryImpl.Stateful.DistEquiv.par_congr` once per channel.
* `evalDist_run_encOncePair_eq` is the corollary on the canonical
  two-call adversary, a one-line specialisation via
  `QueryImpl.Stateful.DistEquiv.run_evalDist_eq`.

## Why no operational reduction here

The previous version of this file proved the two-channel statement
operationally, by walking `simulateQ` over `encOncePair`'s
query-bind chain and discharging each `liftComp` shell from
`QueryImpl.Stateful.par`'s sum-spec import by hand. That worked, but it
reproved the OTP cryptographic core (XOR with uniform is uniform)
inside the `par`-composite — which scales poorly to deeper
compositions and is unnecessary now that:

* `realImpl_impl_evalDist_idealImpl` (in `HeapBasic.lean`) handlers
  the OTP cryptographic core as a *per-(query, heap) handler
  equality* between the gated real and ideal single-channel
  handlers, and
* `QueryImpl.Stateful.DistEquiv.par_congr` (in `VCVio.state-separating.DistEquiv`)
  lifts a pair of such per-handler equalities to a `≡ᵈ`-hop on the
  parallel composite, without any operational `liftComp`
  bookkeeping.

The two combine to give `pairRealImpl ≡ᵈ pairIdealImpl` against
*every* two-channel adversary, not just `encOncePair`.

## What `QueryImpl.Stateful.par` buys here vs. a flat product state

In the SSP product-state model, a two-channel OTP would carry state
type `(Option (BitVec sp)) × (Option (BitVec sp))` (or similar),
with an explicit "left handler reads `.1`, writes back to `.1`,
leaves `.2` alone" frame to discharge by hand at every query.
state-separating gives this frame *structurally* via `Heap.split`: the two
channel handlers each touch only one half of the heap, with the
other half threaded through opaquely, and frame reasoning reduces
to `Heap.split.symm ∘ Heap.split = id` (definitional).
-/

open OracleSpec OracleComp ENNReal
open scoped QueryImpl.Stateful

namespace VCVio.StateSeparating.OneTimePad

/-! ## Parallel OTP handlers -/

/-- The two-channel real OTP handler: two independently-gated OTP
single-channel handlers composed in parallel.

The composite imports `unifSpec + unifSpec` (one uniform-sampling
oracle per child, threaded through `liftComp`) and exports
`otpSpec sp + otpSpec sp` (one encryption channel per child). The
identifier set is `UsedFlag ⊕ UsedFlag`: each channel carries its
own single-call gate, sampled and updated independently. -/
def pairRealImpl (sp : ℕ) :
    QueryImpl.Stateful (unifSpec + unifSpec) (otpSpec sp + otpSpec sp)
      (Heap UsedFlag × Heap UsedFlag) :=
  (realImpl sp).par (realImpl sp)

/-- The two-channel ideal OTP handler: two independently-gated OTP
ideal-channel handlers composed in parallel.

Same shape as `pairRealImpl`: two `UsedFlag` cells, one per channel.
Each channel samples a fresh uniform ciphertext on its first call
(then short-circuits to the dummy `0#sp` on subsequent calls). -/
def pairIdealImpl (sp : ℕ) :
    QueryImpl.Stateful (unifSpec + unifSpec) (otpSpec sp + otpSpec sp)
      (Heap UsedFlag × Heap UsedFlag) :=
  (idealImpl sp).par (idealImpl sp)

/-! ## Single-channel and two-channel adversaries -/

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

Both ingredients live one layer below:

* `realImpl_impl_evalDist_idealImpl` (HeapBasic.lean): per-(query,
  heap) handler `evalDist`-equality at the single-channel layer.
* `QueryImpl.Stateful.DistEquiv.par_congr` (VCVio.state-separating.DistEquiv): lift
  per-handler `evalDist`-equalities on each factor to a `≡ᵈ`-hop on
  the parallel composite.

Stitching them gives the two-channel statement against *every*
adversary, not just `encOncePair`. The one-call corollary is then
a `QueryImpl.Stateful.DistEquiv.run_evalDist_eq` specialisation. -/

/-- **OTP two-channel unconditional distributional equivalence.**
The parallel real and ideal handlers produce identical output
distributions against every two-channel adversary.

Proof: feed the per-(query, heap) handler equality from
`realImpl_impl_evalDist_idealImpl` into `par_congr` twice, once per
channel, from the default heap state on each side. -/
theorem pairRealImpl_distEquiv_pairIdealImpl (sp : ℕ) :
    pairRealImpl sp ≡ᵈ₀ pairIdealImpl sp :=
  QueryImpl.Stateful.DistEquiv.par_congr
    (h₁ := realImpl sp) (h₁' := idealImpl sp)
    (h₂ := realImpl sp) (h₂' := idealImpl sp)
    (s₁ := (default : Heap UsedFlag)) (s₂ := (default : Heap UsedFlag))
    (hh₁ := realImpl_impl_evalDist_idealImpl sp)
    (hh₂ := realImpl_impl_evalDist_idealImpl sp)

/-- **OTP two-channel indistinguishability on `encOncePair`.** The
parallel real and ideal handlers agree on output distribution for
the canonical two-call adversary, recovered from the universal
`pairRealImpl_distEquiv_pairIdealImpl` by specialisation via
`QueryImpl.Stateful.DistEquiv.run_evalDist_eq`. -/
theorem evalDist_run_encOncePair_eq (sp : ℕ) (m₁ m₂ : BitVec sp) :
    𝒟[(pairRealImpl sp).run₀ (encOncePair sp m₁ m₂)] =
      𝒟[(pairIdealImpl sp).run₀ (encOncePair sp m₁ m₂)] :=
  QueryImpl.Stateful.DistEquiv.run₀_evalDist_eq
    (pairRealImpl_distEquiv_pairIdealImpl sp) (encOncePair sp m₁ m₂)

end VCVio.StateSeparating.OneTimePad
