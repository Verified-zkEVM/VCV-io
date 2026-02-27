/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.EvalDist.Prod
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.OracleContext

/-!
# Symmetric Encryption Schemes.

This file defines a type `SymmEncAlg spec M K C` to represent a protocol
for symmetric encryption using oracles in `spec`, with message space `M`,
secret keys of type `K`, and ciphertext space `C`.
-/

universe u v w

open OracleSpec OracleComp ENNReal

structure SymmEncAlg (M K C : ℕ → Type)
    (Q : Type v) extends OracleContext Q ProbComp where
  keygen (sp : ℕ) : OracleComp spec (K sp)
  encrypt {sp : ℕ} (k : K sp) (msg : M sp) : OracleComp spec (C sp)
  decrypt {sp : ℕ} (k : K sp) (c : C sp) : OptionT (OracleComp spec) (M sp)

namespace SymmEncAlg

variable {M K C : ℕ → Type} {Q : Type v}

def CompleteExp (encAlg : SymmEncAlg M K C Q) {sp : ℕ} (m : M sp) :
    OptionT (OracleComp encAlg.spec) (M sp) := do
  let k ← liftM (encAlg.keygen sp)
  let σ ← liftM (encAlg.encrypt k m)
  encAlg.decrypt k σ

def Complete (encAlg : SymmEncAlg M K C Q) : Prop := ∀ sp, ∀ m : M sp,
  Pr[= m | simulateQ encAlg.impl (CompleteExp encAlg m).run] = 1

section perfectSecrecy

/-! ## Definitions and Equivalences

`perfectSecrecyAt` is the canonical notion (independence form).
We also provide equivalent formulations:
* `perfectSecrecyPosteriorEqPriorAt` (cross-multiplied posterior/prior form),
* `perfectSecrecyJointFactorizationAt` (same factorization with named marginals).

The `_iff_` lemmas below record equivalence between these forms. -/

/-- Joint message/ciphertext experiment used to express perfect secrecy. -/
def PerfectSecrecyExp (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    (mgen : OracleComp encAlg.spec (M sp)) : ProbComp (M sp × C sp) :=
  simulateQ encAlg.impl do
    let msg' ← mgen
    let k ← encAlg.keygen sp
    return (msg', ← encAlg.encrypt k msg')

/-- Ciphertext marginal induced by the perfect-secrecy experiment. -/
def PerfectSecrecyCipherExp (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    (mgen : OracleComp encAlg.spec (M sp)) : ProbComp (C sp) :=
  Prod.snd <$> encAlg.PerfectSecrecyExp sp mgen

/-- Message prior induced by the message generator. -/
def PerfectSecrecyPriorExp (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    (mgen : OracleComp encAlg.spec (M sp)) : ProbComp (M sp) :=
  simulateQ encAlg.impl mgen

/-- Standard perfect secrecy at one security parameter, expressed as independence:
`Pr[(M, C)] = Pr[M] * Pr[C]`. This is the canonical code-level definition. -/
def perfectSecrecyAt (encAlg : SymmEncAlg M K C Q) (sp : ℕ) : Prop :=
  ∀ mgen : OracleComp encAlg.spec (M sp), ∀ msg : M sp, ∀ σ : C sp,
    Pr[= (msg, σ) | encAlg.PerfectSecrecyExp sp mgen] =
      Pr[= msg | encAlg.PerfectSecrecyPriorExp sp mgen] *
      Pr[= σ | encAlg.PerfectSecrecyCipherExp sp mgen]

/-- Canonical asymptotic perfect secrecy notion. -/
def perfectSecrecy (encAlg : SymmEncAlg M K C Q) : Prop :=
  ∀ sp, encAlg.perfectSecrecyAt sp

/-- Posterior-equals-prior form, written in cross-multiplied form to avoid division.
This is equivalent to `perfectSecrecyAt`. -/
def perfectSecrecyPosteriorEqPriorAt (encAlg : SymmEncAlg M K C Q) (sp : ℕ) : Prop :=
  ∀ mgen : OracleComp encAlg.spec (M sp), ∀ msg : M sp, ∀ σ : C sp,
    Pr[= (msg, σ) | encAlg.PerfectSecrecyExp sp mgen] =
      Pr[= σ | encAlg.PerfectSecrecyCipherExp sp mgen] *
      Pr[= msg | encAlg.PerfectSecrecyPriorExp sp mgen]

/-- Joint-factorization form (same mathematical statement as independence, with explicit
named priors/marginals). This is equivalent to `perfectSecrecyAt`. -/
def perfectSecrecyJointFactorizationAt
    (encAlg : SymmEncAlg M K C Q) (sp : ℕ) : Prop :=
  ∀ mgen : OracleComp encAlg.spec (M sp), ∀ msg : M sp, ∀ σ : C sp,
    let jointExp := encAlg.PerfectSecrecyExp sp mgen
    let priorExp := encAlg.PerfectSecrecyPriorExp sp mgen
    let cipherExp := encAlg.PerfectSecrecyCipherExp sp mgen
    Pr[= (msg, σ) | jointExp] =
      Pr[= msg | priorExp] * Pr[= σ | cipherExp]

def perfectSecrecyPosteriorEqPrior (encAlg : SymmEncAlg M K C Q) : Prop :=
  ∀ sp, encAlg.perfectSecrecyPosteriorEqPriorAt sp

def perfectSecrecyJointFactorization (encAlg : SymmEncAlg M K C Q) : Prop :=
  ∀ sp, encAlg.perfectSecrecyJointFactorizationAt sp

lemma perfectSecrecyAt_iff_posteriorEqPriorAt (encAlg : SymmEncAlg M K C Q)
    (sp : ℕ) :
    encAlg.perfectSecrecyAt sp ↔ encAlg.perfectSecrecyPosteriorEqPriorAt sp := by
  constructor <;> intro h <;> intro mgen msg σ
  · simpa [perfectSecrecyAt, perfectSecrecyPosteriorEqPriorAt, mul_comm] using h mgen msg σ
  · simpa [perfectSecrecyAt, perfectSecrecyPosteriorEqPriorAt, mul_comm] using h mgen msg σ

lemma perfectSecrecyAt_iff_jointFactorizationAt (encAlg : SymmEncAlg M K C Q)
    (sp : ℕ) :
    encAlg.perfectSecrecyAt sp ↔ encAlg.perfectSecrecyJointFactorizationAt sp := by
  constructor
  · intro h
    simpa [perfectSecrecyAt, perfectSecrecyJointFactorizationAt]
      using h
  · intro h
    simpa [perfectSecrecyAt, perfectSecrecyJointFactorizationAt]
      using h

lemma perfectSecrecy_iff_posteriorEqPrior (encAlg : SymmEncAlg M K C Q) :
    encAlg.perfectSecrecy ↔ encAlg.perfectSecrecyPosteriorEqPrior := by
  constructor <;> intro h sp
  · exact (encAlg.perfectSecrecyAt_iff_posteriorEqPriorAt sp).1 (h sp)
  · exact (encAlg.perfectSecrecyAt_iff_posteriorEqPriorAt sp).2 (h sp)

lemma perfectSecrecy_iff_jointFactorization (encAlg : SymmEncAlg M K C Q) :
    encAlg.perfectSecrecy ↔ encAlg.perfectSecrecyJointFactorization := by
  constructor <;> intro h sp
  · exact (encAlg.perfectSecrecyAt_iff_jointFactorizationAt sp).1 (h sp)
  · exact (encAlg.perfectSecrecyAt_iff_jointFactorizationAt sp).2 (h sp)

/-- Shannon's theorem on perfect secrecy at a fixed security parameter: if the message space,
key space, and ciphertext space have the same cardinality, then perfect secrecy holds iff
keys are chosen uniformly and for each (message, ciphertext) pair there is a unique key
that encrypts the message to that ciphertext.

The old version used non-asymptotic `SymmEncAlg m M K C`; here we fix `sp : ℕ` and work
at that security parameter.

`deterministicEnc` asserts that encryption is deterministic (support is a singleton),
which is required for the classical statement. -/
private theorem perfectSecrecy_iff_of_card_eq_forward
    (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    [Fintype (M sp)] [Fintype (K sp)] [Fintype (C sp)]
    (hComplete : encAlg.Complete)
    (h1 : Fintype.card (M sp) = Fintype.card (K sp))
    (h2 : Fintype.card (K sp) = Fintype.card (C sp))
    (deterministicEnc : ∀ (k : K sp) (msg : M sp),
      ∃ c, support (simulateQ encAlg.impl (encAlg.encrypt k msg)) = {c}) :
    encAlg.perfectSecrecyAt sp →
    ((∀ k : K sp, Pr[= k | simulateQ encAlg.impl (encAlg.keygen sp)] =
        (Fintype.card (K sp) : ℝ≥0∞)⁻¹) ∧
    (∀ msg : M sp, ∀ c : C sp, ∃! k : K sp,
        k ∈ support (simulateQ encAlg.impl (encAlg.keygen sp)) ∧
        c ∈ support (simulateQ encAlg.impl (encAlg.encrypt k msg)))) := by
  sorry

private theorem perfectSecrecy_iff_of_card_eq_backward
    (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    [Fintype (M sp)] [Fintype (K sp)] [Fintype (C sp)]
    (hComplete : encAlg.Complete)
    (h1 : Fintype.card (M sp) = Fintype.card (K sp))
    (h2 : Fintype.card (K sp) = Fintype.card (C sp))
    (deterministicEnc : ∀ (k : K sp) (msg : M sp),
      ∃ c, support (simulateQ encAlg.impl (encAlg.encrypt k msg)) = {c}) :
    ((∀ k : K sp, Pr[= k | simulateQ encAlg.impl (encAlg.keygen sp)] =
        (Fintype.card (K sp) : ℝ≥0∞)⁻¹) ∧
    (∀ msg : M sp, ∀ c : C sp, ∃! k : K sp,
        k ∈ support (simulateQ encAlg.impl (encAlg.keygen sp)) ∧
        c ∈ support (simulateQ encAlg.impl (encAlg.encrypt k msg)))) →
    encAlg.perfectSecrecyAt sp := by
  sorry

theorem perfectSecrecy_iff_of_card_eq (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    [Fintype (M sp)] [Fintype (K sp)] [Fintype (C sp)]
    (hComplete : encAlg.Complete)
    (h1 : Fintype.card (M sp) = Fintype.card (K sp))
    (h2 : Fintype.card (K sp) = Fintype.card (C sp))
    (deterministicEnc : ∀ (k : K sp) (msg : M sp),
      ∃ c, support (simulateQ encAlg.impl (encAlg.encrypt k msg)) = {c}) :
    encAlg.perfectSecrecyAt sp ↔
    ((∀ k : K sp, Pr[= k | simulateQ encAlg.impl (encAlg.keygen sp)] =
        (Fintype.card (K sp) : ℝ≥0∞)⁻¹) ∧
    (∀ msg : M sp, ∀ c : C sp, ∃! k : K sp,
        k ∈ support (simulateQ encAlg.impl (encAlg.keygen sp)) ∧
        c ∈ support (simulateQ encAlg.impl (encAlg.encrypt k msg)))) :=
by
  constructor
  · exact perfectSecrecy_iff_of_card_eq_forward encAlg sp hComplete h1 h2 deterministicEnc
  · exact perfectSecrecy_iff_of_card_eq_backward encAlg sp hComplete h1 h2 deterministicEnc

end perfectSecrecy

end SymmEncAlg
