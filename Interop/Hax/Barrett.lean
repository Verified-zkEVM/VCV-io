/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Interop.Hax.Bridge
import Interop.Rust.Run
import Hax.rust_primitives.Cast
import Hax.rust_primitives.BVDecide
import Hax.Tactic
import Hax.MissingLean.Std.Do.Triple.Basic
import VCVio.ProgramLogic.Unary.StdDoBridge

/-!
# End-to-end hax example: signed Barrett reduction

Reproduces hax's `examples/lean_barrett` demo inside the `Interop`
bridge. `barrett_reduce` is the signed Barrett reduction routine used
by ML-KEM (aka Kyber) and ML-DSA for modular reduction by the field
prime `q = 3329`; it is the smallest genuinely lattice-cryptographic
primitive that fits on a single page of code.

## Provenance

The Rust source lives at `examples/lean_barrett/src/lib.rs` in hax's
repository:

```rust
pub(crate) type FieldElement = i32;

const BARRETT_R: i64 = 0x400000;
const BARRETT_SHIFT: i64 = 26;
const BARRETT_MULTIPLIER: i64 = 20159;
pub(crate) const FIELD_MODULUS: i32 = 3329;

pub fn barrett_reduce(value: FieldElement) -> FieldElement {
    let t = i64::from(value) * BARRETT_MULTIPLIER;
    let t = t + (BARRETT_R >> 1);
    let quotient = t >> BARRETT_SHIFT;
    let quotient = quotient as i32;
    let sub = quotient * FIELD_MODULUS;
    value - sub
}
```

Under the precondition `-BARRETT_R ≤ value ≤ BARRETT_R` (which holds
for every coefficient ML-KEM/ML-DSA ever passes through Barrett),
`barrett_reduce value` returns a value `r` with `|r| < FIELD_MODULUS`
and `r ≡ value (mod FIELD_MODULUS)`. The hax source embeds this
correctness theorem via `#[hax_lib::lean::replace(...)]` and closes it
with `hax_bv_decide (timeout := 90)`; we reproduce it verbatim here
and transport the result over the bridge.

## What this demonstrates

* Signed integer arithmetic (`*?`, `+?`, `-?`), signed shifts
  (`>>>?`), and integer-width casts (`rust_primitives.hax.cast_op`)
  all round-trip cleanly through the bridge.
* `hax_bv_decide` is the right tactic for Barrett-style proofs that
  need to reason about 64-bit intermediate arithmetic and 32-bit
  final results simultaneously. `hax_mvcgen + bv_decide` would also
  work (both compose the same bit-blasting backend) but Barrett's
  all-`pure` control flow makes the direct `hax_bv_decide` form more
  idiomatic.
* The oracle-lifted spec `barrett_reduce_Lifted_spec` is, as in
  `Computation.lean` / `Division.lean` / `Adc.lean`, one line over
  the hax-side spec via `triple_liftRustM`. This is the consistent
  story of the bridge: pay the bit-blasting cost once, on the hax
  side; oracle-awareness comes free.

## Relation to ML-KEM / ML-DSA

This exact routine (`FIELD_MODULUS = 3329`) is ML-KEM's `barrett_reduce`.
ML-DSA uses a sibling routine with `FIELD_MODULUS = 8380417` and a
correspondingly larger Barrett constant; the proof structure is
identical. A full ML-KEM or ML-DSA port remains a substantial
undertaking, but every coefficient-level modular reduction in those
schemes reduces to exactly this pattern.
-/

open Std.Do OracleSpec OracleComp
open scoped OracleSpec.PrimitiveQuery

namespace Interop.Hax.Examples.Barrett

variable {ι : Type} {spec : OracleSpec ι}

/-! ### Constants

The four Barrett constants, emitted as plain `def`s of the appropriate
machine-integer types. None of them are candidates for runtime panics
so hax does not wrap them in `RustM.of_isOk`. -/

/-- `BARRETT_R = 2^22`: the Barrett window, chosen so that the 64-bit
intermediate `t = value * BARRETT_MULTIPLIER` comfortably fits after
shifting by `BARRETT_SHIFT`. -/
def BARRETT_R : i64 := (0x400000 : i64)

/-- `BARRETT_SHIFT = 26`: the final right-shift that divides out the
Barrett scale. Chosen so that `2^BARRETT_SHIFT ≈ 2 * BARRETT_R *
FIELD_MODULUS` up to rounding. -/
def BARRETT_SHIFT : i64 := (26 : i64)

/-- `BARRETT_MULTIPLIER = ⌊2^BARRETT_SHIFT / FIELD_MODULUS⌉ = 20159`:
the precomputed multiplicative inverse of `FIELD_MODULUS` in the
Barrett window. -/
def BARRETT_MULTIPLIER : i64 := (20159 : i64)

/-- `FIELD_MODULUS = 3329`: the Kyber / ML-KEM field prime `q`. The
same Barrett reduction pattern is used by ML-DSA with
`FIELD_MODULUS = 8380417`. -/
def FIELD_MODULUS : i32 := (3329 : i32)

/-! ### Hax-style emission

Reproduces the `RustM` code hax emits for `barrett_reduce`. Five
panic-capable operations (`*?`, `+?`, `-?`, `>>>?`) are sequenced
through `do` and separated by casts via `rust_primitives.hax.cast_op`.
We compute the compile-time constant `(BARRETT_R >>> 1)` inside the
body so that the shape matches what hax emits at the AST level; the
bit-blasting proof below is indifferent to the difference. -/

/-- Signed Barrett reduction. Produces a representative `r ∈
(-FIELD_MODULUS, FIELD_MODULUS)` of `value` modulo `FIELD_MODULUS`
whenever `|value| ≤ BARRETT_R`; panics with `.integerOverflow` on the
rare paths where any intermediate overflows (none of which are
reachable under the precondition). -/
@[spec]
def barrett_reduce (value : i32) : RustM i32 := do
  let t : i64 ← (← (rust_primitives.hax.cast_op value : RustM i64)) *? BARRETT_MULTIPLIER
  let t : i64 ← t +? (← BARRETT_R >>>? (1 : i64))
  let quotient : i64 ← t >>>? BARRETT_SHIFT
  let quotient : i32 ← (rust_primitives.hax.cast_op quotient : RustM i32)
  let sub : i32 ← quotient *? FIELD_MODULUS
  value -? sub

/-! ### `RustM`-level Barrett correctness

The Hoare triple is stated directly in terms of `Int32` / `Int64`
signed comparisons and signed modular arithmetic: the precondition
is that `value`, widened to `i64`, lies in `[-BARRETT_R, BARRETT_R]`;
the postcondition is the standard Barrett window property `|r| <
FIELD_MODULUS ∧ r ≡ value (mod FIELD_MODULUS)`. Keeping the
specification on machine integers (rather than wrapping it in
`Bool`-valued helpers) is what allows `hax_bv_decide` to bit-blast
the whole thing; `.toInt`-style casts would turn the goal into a
mixed `Int`/`BitVec` problem that the decision procedure cannot
close.

Proof is `hax_bv_decide` with a bumped heartbeat limit, mirroring
hax's upstream `examples/lean_barrett` demo. Under the precondition
none of the `+?` / `*?` / `-?` operations in the body panic, so the
Triple collapses to the single BitVec assertion about the returned
value. -/

set_option mvcgen.warning false in
set_option maxHeartbeats 1_000_000 in
-- Bit-blasting a 64-bit intermediate with a 32-bit final result across
-- five checked arithmetic ops needs substantially more heartbeats than
-- the default; this matches hax's upstream `lean_barrett` demo. The
-- SAT timeout is bumped to 300 seconds (vs hax's upstream 90) because
-- CI runners are substantially slower than developer laptops on this
-- particular bit-blast; locally 90 suffices.
theorem barrett_reduce_spec (value : i32) :
    ⦃⌜value.toInt64 ≥ -(4194304 : Int64) ∧
       value.toInt64 ≤ (4194304 : Int64)⌝⦄
    (barrett_reduce value)
    ⦃⇓ r => ⌜r > -(3329 : Int32) ∧ r < (3329 : Int32) ∧
      (r = value % (3329 : Int32) ∨
       r = value % (3329 : Int32) + (3329 : Int32) ∨
       r = value % (3329 : Int32) - (3329 : Int32))⌝⦄ := by
  unfold barrett_reduce FIELD_MODULUS BARRETT_R BARRETT_MULTIPLIER BARRETT_SHIFT
  hax_bv_decide (timeout := 300)

/-! ### Oracle-lifted Barrett

The oracle-aware side of the bridge. `barrett_reduce_Lifted` is just
the lift, and `barrett_reduce_Lifted_spec` is the transport of the
`RustM`-side correctness theorem through `triple_liftRustM`. The
`errorOfHax` rebrand inside `triple_liftRustM` is invisible in the
post-condition because the precondition rules out the panic branch. -/

/-- Oracle-lifted Barrett reduction: wraps the hax-emitted
`barrett_reduce` in `RustOracleComp spec`. Equivalent to just
`liftRustM (barrett_reduce value)`. -/
def barrett_reduce_Lifted (value : i32) : Interop.Rust.RustOracleComp spec i32 :=
  liftRustM (barrett_reduce value)

/-- Transport of `barrett_reduce_spec` to `RustOracleComp`. This is the
end-to-end demonstration that a real lattice-crypto primitive, proved
on the hax side by the heavyweight `hax_bv_decide` stack, lands in
the oracle-aware target in a single line of proof. -/
theorem barrett_reduce_Lifted_spec [spec.Fintype] [spec.Inhabited]
    (value : i32) :
    ⦃⌜value.toInt64 ≥ -(4194304 : Int64) ∧
       value.toInt64 ≤ (4194304 : Int64)⌝⦄
    (barrett_reduce_Lifted (spec := spec) value)
    ⦃⇓ r => ⌜r > -(3329 : Int32) ∧ r < (3329 : Int32) ∧
      (r = value % (3329 : Int32) ∨
       r = value % (3329 : Int32) + (3329 : Int32) ∨
       r = value % (3329 : Int32) - (3329 : Int32))⌝⦄ := by
  unfold barrett_reduce_Lifted
  exact triple_liftRustM _ (barrett_reduce_spec value)

/-! ### Oracle-composed Barrett

The intended end-to-end usage of the bridge: sample a coefficient from
an oracle, cast it into the `i32` input type, and reduce it modulo
`FIELD_MODULUS` with the hax-emitted routine. Under a Barrett-window
bound on every oracle response, the composed program never panics and
its result always lies in `(-FIELD_MODULUS, FIELD_MODULUS)`.

This is the minimum sketch of an ML-KEM / ML-DSA inner loop: modular
reduction of a freshly-sampled coefficient. The `oracleThenBarrett`
shape is representative; real schemes iterate it `n` times over a
polynomial ring and eventually apply an NTT on top.

The postcondition here is deliberately weaker than
`barrett_reduce_Lifted_spec`'s: we drop the modular-equivalence
disjunction and keep only the window property, so that the
post-condition does not mention the oracle's output. Retaining the
modular-equivalence would force a postcondition that quantifies over
oracle outcomes, which is not expressible at the `Triple` level. -/

section OracleComposition

set_option mvcgen.warning false

variable [spec.Fintype] [spec.Inhabited]

/-- Query an oracle for a field coefficient (represented via `spec.Range t`
and a user-supplied cast), then reduce it modulo `FIELD_MODULUS`. -/
def oracleThenBarrett (t : ι) (coe : spec.Range t → i32) :
    Interop.Rust.RustOracleComp spec i32 := do
  let y ← (liftM (query t) : OracleComp spec _)
  barrett_reduce_Lifted (coe y)

/-- Under a universal Barrett-window bound on oracle responses, the
oracle-composed Barrett reduction always produces a coefficient inside
the representative window `(-FIELD_MODULUS, FIELD_MODULUS)`. -/
theorem oracleThenBarrett_triple
    (t : ι) (coe : spec.Range t → i32)
    (hbound : ∀ y : spec.Range t,
      (coe y).toInt64 ≥ -(4194304 : Int64) ∧
      (coe y).toInt64 ≤ (4194304 : Int64)) :
    ⦃⌜True⌝⦄
    (oracleThenBarrett (spec := spec) t coe)
    ⦃⇓ r => ⌜r > -(3329 : Int32) ∧ r < (3329 : Int32)⌝⦄ := by
  mvcgen [oracleThenBarrett]
  rw [OracleComp.ProgramLogic.StdDo.wpProp_iff_forall_support]
  intro y _
  -- On every oracle outcome, apply the full Barrett triple and drop
  -- the modular-equivalence conjunct to match the weaker post-condition.
  have hTriple : ⌜(coe y).toInt64 ≥ -(4194304 : Int64) ∧
      (coe y).toInt64 ≤ (4194304 : Int64)⌝ ⊢ₛ
        wp⟦barrett_reduce_Lifted (spec := spec) (coe y)⟧
          (PostCond.noThrow fun r => ⌜r > -(3329 : Int32) ∧ r < (3329 : Int32)⌝) :=
    Std.Do.Triple.entails_wp_of_post
      (barrett_reduce_Lifted_spec (spec := spec) (coe y))
      ⟨fun _ => SPred.pure_mono (fun hr => ⟨hr.1, hr.2.1⟩),
       ExceptConds.entails.refl _⟩
  exact hTriple (hbound y)

end OracleComposition

end Interop.Hax.Examples.Barrett
