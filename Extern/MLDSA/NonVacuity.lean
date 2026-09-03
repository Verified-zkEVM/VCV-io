/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module

public import Extern.MLDSA.Laws

/-!
# Hypothesis-consistency certificate for `MLDSA.Primitives.Laws` (issue #228)

The ML-DSA correctness and zero-knowledge theorems — `MLDSA.idsWithAbort_complete`
(`MLDSA/Security.lean`), `MLDSA.idsWithAbort_hvzk` (`MLDSA/SecurityHVZK.lean`),
`MLDSA.fipsSign_fipsVerify_correct` (`MLDSA/Signature.lean`), and the algebraic lemmas they run on
(`MLDSA.keyGenFromSeed_wApprox_eq`, `MLDSA.recoverT0_eq`) — are each gated on
`h_laws : Primitives.Laws prims nttOps`.  A conditional theorem asserts nothing if its hypothesis is
uninhabitable, and `#print axioms` cannot detect that.  This file rules that out with a
kernel-checked witness: `Primitives.Laws` is genuinely **inhabitable**.

This is a **logical consistency (inhabitance) witness only**: `seedRevealingPrims` publishes the
key-generation seed as the public `ρ`, so it is neither a faithful nor a secure ML-DSA
instantiation, and no security claim about concrete ML-DSA follows from it.

The witness `seedRevealingPrims` is `concretePrimitives` with the public `ρ`-component of
`expandSeed`
overridden to be the identity in the seed.  Every field consumed by the thirteen banked
`concrete_*` laws is definitionally unchanged, so those laws transfer verbatim; the only remaining
field, the determinacy assumption `keyVector_t0_determined`, holds trivially because the override
makes the published seed-component injective (matching `ρ` forces the same seed, hence the same
`t₀`).  Injectivity of the published seed-component is precisely the structural feature that makes
`keyVector_t0_determined` satisfiable by a deterministic bundle.

**Trust surface.**  `mldsa_laws_inhabited` depends on `propext`, `Classical.choice`, `Quot.sound`,
**and** the `native_decide` certificate for the concrete `256×256` NTT matrix inversion
(`MLDSA.Concrete.invNTTMatrix_nttMatrix_entry`, routed in through `concrete_transform`).  That
`native_decide` axiom is carried by every concrete ML-DSA fact (e.g. `concrete_transform` itself),
since `concreteNTTRingOps` is the only `NTTRingLaws` instance in the tree.  The *abstract*
`Laws`-gated theorems (quantified over `nttOps`) are themselves axiom-clean
`[propext, Classical.choice, Quot.sound]`; this certificate only witnesses that their `Laws`
hypothesis can be met by the concrete layer (whose NTT-correctness trust assumption it inherits).
-/

public section

open MLDSA

namespace MLDSA

/-- `concretePrimitives p` with the public `ρ`-component of `expandSeed` overridden to be the
identity in the seed.  Every other field — including all fields consumed by the thirteen
`concrete_*` laws — is definitionally equal to `concretePrimitives p`, so those laws transfer
unchanged.  The override makes the published seed-component injective, which is exactly what
`keyVector_t0_determined` needs.

A **logical consistency witness** for `Primitives.Laws`: publishing the seed as `ρ` discards
key secrecy, so this is not a faithful or secure ML-DSA instantiation — it exists to show the
`Laws` hypothesis type is inhabited. -/
def seedRevealingPrims (p : Params) : MLDSA.Primitives p :=
  { MLDSA.Concrete.concretePrimitives p with
      expandSeed := fun s => (s, ((MLDSA.Concrete.concretePrimitives p).expandSeed s).2) }

/-- `Primitives.Laws (seedRevealingPrims p) concreteNTTRingOps` for any approved `p`.  Thirteen
fields are
the banked `concrete_*` lemmas (they typecheck because every field consumed there is defeq between
`seedRevealingPrims p` and `concretePrimitives p`); `keyVector_t0_determined` needs only the
hypothesis
`((seedRevealingPrims p).expandSeed s).1 = ((seedRevealingPrims p).expandSeed s').1`, which
reduces to `s = s'`,
after which the two sides of the conclusion are syntactically identical. -/
theorem seedRevealingPrims_laws (p : Params) (hp : p.isApproved) :
    MLDSA.Primitives.Laws (seedRevealingPrims p) MLDSA.Concrete.concreteNTTRingOps where
  sampleInBall_norm        := MLDSA.Concrete.concrete_sampleInBall_norm p
  expandS_bound            := MLDSA.Concrete.concrete_expandS_bound p
  expandMask_bound         := MLDSA.Concrete.concrete_expandMask_bound p hp
  transform                := MLDSA.Concrete.concrete_transform
  high_low_decomp          := MLDSA.Concrete.concrete_high_low_decomp p
  lowBits_bound            := MLDSA.Concrete.concrete_lowBits_bound p hp
  hide_low                 := MLDSA.Concrete.concrete_hide_low p hp
  highBitsShift_injective  := MLDSA.Concrete.concrete_highBitsShift_injective p hp
  useHint_makeHint         := MLDSA.Concrete.concrete_useHint_makeHint p hp
  power2Round_decomp       := MLDSA.Concrete.concrete_power2Round_decomp p
  power2Round_bound        := MLDSA.Concrete.concrete_power2Round_bound p
  w1Encode_injective       := MLDSA.Concrete.concrete_w1Encode_injOn p hp
  sampleInBall_smul_bound  := MLDSA.Concrete.concrete_sampleInBall_smul_bound p
  keyVector_t0_determined  := by
    intro s s' hρ _
    -- `((seedRevealingPrims p).expandSeed s).1` reduces to `s`, so `hρ : s = s'`.
    simp only [seedRevealingPrims] at hρ
    subst hρ
    rfl

/-- **The #228 non-vacuity certificate.**  There is an approved parameter set and a primitive
bundle whose `Primitives.Laws` is inhabited — so the `Laws`-gated ML-DSA theorems
(`MLDSA.idsWithAbort_complete`, `MLDSA.idsWithAbort_hvzk`, `MLDSA.fipsSign_fipsVerify_correct`,
`MLDSA.keyGenFromSeed_wApprox_eq`, `MLDSA.recoverT0_eq`) are not true-but-vacuous.  (See the
trust-surface note in the module docstring on the inherited concrete NTT `native_decide` axiom.) -/
theorem mldsa_laws_inhabited :
    ∃ (p : Params) (prims : MLDSA.Primitives p),
      Nonempty (MLDSA.Primitives.Laws prims MLDSA.Concrete.concreteNTTRingOps) :=
  ⟨mldsa44, seedRevealingPrims mldsa44, ⟨seedRevealingPrims_laws mldsa44 (Or.inl rfl)⟩⟩

end MLDSA
