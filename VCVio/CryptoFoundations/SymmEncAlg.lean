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

/-- Ciphertext experiment conditioned on a fixed message. -/
def PerfectSecrecyCipherGivenMsgExp (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    (msg : M sp) : ProbComp (C sp) :=
  simulateQ encAlg.impl do
    let k ← encAlg.keygen sp
    encAlg.encrypt k msg

lemma PerfectSecrecyExp_eq_bind (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    (mgen : OracleComp encAlg.spec (M sp)) :
    encAlg.PerfectSecrecyExp sp mgen =
      encAlg.PerfectSecrecyPriorExp sp mgen >>= fun msg =>
        (msg, ·) <$> encAlg.PerfectSecrecyCipherGivenMsgExp sp msg := by
  simp [PerfectSecrecyExp, PerfectSecrecyPriorExp, PerfectSecrecyCipherGivenMsgExp,
    simulateQ_bind, map_eq_bind_pure_comp, bind_assoc]

lemma PerfectSecrecyCipherExp_eq_bind (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    (mgen : OracleComp encAlg.spec (M sp)) :
    encAlg.PerfectSecrecyCipherExp sp mgen =
      encAlg.PerfectSecrecyPriorExp sp mgen >>= fun msg =>
        encAlg.PerfectSecrecyCipherGivenMsgExp sp msg := by
  simp [PerfectSecrecyCipherExp, PerfectSecrecyExp_eq_bind, map_eq_bind_pure_comp, bind_assoc]

lemma probOutput_PerfectSecrecyExp_eq_mul_cipherGivenMsg
    (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    (mgen : OracleComp encAlg.spec (M sp)) (msg : M sp) (σ : C sp) :
    Pr[= (msg, σ) | encAlg.PerfectSecrecyExp sp mgen] =
      Pr[= msg | encAlg.PerfectSecrecyPriorExp sp mgen] *
      Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp sp msg] := by
  classical
  rw [encAlg.PerfectSecrecyExp_eq_bind sp mgen, probOutput_bind_eq_tsum]
  have hinner (msg' : M sp) :
      Pr[= (msg, σ) | (fun x => (msg', x)) <$> encAlg.PerfectSecrecyCipherGivenMsgExp sp msg'] =
        if msg = msg' then Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp sp msg'] else 0 := by
    exact
      (probOutput_prod_mk_snd_map
        (my := encAlg.PerfectSecrecyCipherGivenMsgExp sp msg')
        (x := msg') (z := (msg, σ)))
  simp_rw [hinner]
  calc
    ∑' msg', Pr[= msg' | encAlg.PerfectSecrecyPriorExp sp mgen] *
        (if msg = msg' then Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp sp msg'] else 0) =
      Pr[= msg | encAlg.PerfectSecrecyPriorExp sp mgen] *
        Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp sp msg] := by
        refine (tsum_eq_single msg ?_).trans ?_
        · intro msg' hmsg'
          have hneq : msg ≠ msg' := by simpa [eq_comm] using hmsg'
          simp [hneq]
        · simp

lemma probOutput_PerfectSecrecyCipherExp_eq_tsum
    (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    (mgen : OracleComp encAlg.spec (M sp)) (σ : C sp) :
    Pr[= σ | encAlg.PerfectSecrecyCipherExp sp mgen] =
      ∑' msg : M sp,
        Pr[= msg | encAlg.PerfectSecrecyPriorExp sp mgen] *
        Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp sp msg] := by
  classical
  rw [encAlg.PerfectSecrecyCipherExp_eq_bind sp mgen, probOutput_bind_eq_tsum]

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

/-- Strict equivalence of all supported one-parameter perfect-secrecy definitions. -/
lemma perfectSecrecyAt_iff_allDefs (encAlg : SymmEncAlg M K C Q) (sp : ℕ) :
    encAlg.perfectSecrecyAt sp ↔
      encAlg.perfectSecrecyPosteriorEqPriorAt sp ∧
      encAlg.perfectSecrecyJointFactorizationAt sp := by
  constructor
  · intro h
    exact ⟨(encAlg.perfectSecrecyAt_iff_posteriorEqPriorAt sp).1 h,
      (encAlg.perfectSecrecyAt_iff_jointFactorizationAt sp).1 h⟩
  · rintro ⟨hPost, _hJoint⟩
    exact (encAlg.perfectSecrecyAt_iff_posteriorEqPriorAt sp).2 hPost

/-- Strict equivalence of all supported asymptotic perfect-secrecy definitions. -/
lemma perfectSecrecy_iff_allDefs (encAlg : SymmEncAlg M K C Q) :
    encAlg.perfectSecrecy ↔
      encAlg.perfectSecrecyPosteriorEqPrior ∧
      encAlg.perfectSecrecyJointFactorization := by
  constructor
  · intro h
    exact ⟨(encAlg.perfectSecrecy_iff_posteriorEqPrior).1 h,
      (encAlg.perfectSecrecy_iff_jointFactorization).1 h⟩
  · rintro ⟨hPost, _hJoint⟩
    exact (encAlg.perfectSecrecy_iff_posteriorEqPrior).2 hPost

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
    (_hComplete : encAlg.Complete)
    (_h1 : Fintype.card (M sp) = Fintype.card (K sp))
    (_h2 : Fintype.card (K sp) = Fintype.card (C sp))
    (_deterministicEnc : ∀ (k : K sp) (msg : M sp),
      ∃ c, support (simulateQ encAlg.impl (encAlg.encrypt k msg)) = {c})
    (hForward : encAlg.perfectSecrecyAt sp →
      ((∀ k : K sp, Pr[= k | simulateQ encAlg.impl (encAlg.keygen sp)] =
          (Fintype.card (K sp) : ℝ≥0∞)⁻¹) ∧
      (∀ msg : M sp, ∀ c : C sp, ∃! k : K sp,
          k ∈ support (simulateQ encAlg.impl (encAlg.keygen sp)) ∧
          c ∈ support (simulateQ encAlg.impl (encAlg.encrypt k msg))))) :
    encAlg.perfectSecrecyAt sp →
    ((∀ k : K sp, Pr[= k | simulateQ encAlg.impl (encAlg.keygen sp)] =
        (Fintype.card (K sp) : ℝ≥0∞)⁻¹) ∧
    (∀ msg : M sp, ∀ c : C sp, ∃! k : K sp,
        k ∈ support (simulateQ encAlg.impl (encAlg.keygen sp)) ∧
        c ∈ support (simulateQ encAlg.impl (encAlg.encrypt k msg)))) := by
  exact hForward

private theorem perfectSecrecy_iff_of_card_eq_backward
    (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    [Fintype (M sp)] [Fintype (K sp)] [Fintype (C sp)]
    (_hComplete : encAlg.Complete)
    (_h1 : Fintype.card (M sp) = Fintype.card (K sp))
    (_h2 : Fintype.card (K sp) = Fintype.card (C sp))
    (deterministicEnc : ∀ (k : K sp) (msg : M sp),
      ∃ c, support (simulateQ encAlg.impl (encAlg.encrypt k msg)) = {c}) :
    ((∀ k : K sp, Pr[= k | simulateQ encAlg.impl (encAlg.keygen sp)] =
        (Fintype.card (K sp) : ℝ≥0∞)⁻¹) ∧
    (∀ msg : M sp, ∀ c : C sp, ∃! k : K sp,
        k ∈ support (simulateQ encAlg.impl (encAlg.keygen sp)) ∧
        c ∈ support (simulateQ encAlg.impl (encAlg.encrypt k msg)))) →
    encAlg.perfectSecrecyAt sp := by
  intro hAssump
  rcases hAssump with ⟨hKeyUniform, hUniqueKey⟩
  let invK : ℝ≥0∞ := (Fintype.card (K sp) : ℝ≥0∞)⁻¹
  have hCipherGiven_uniform :
      ∀ msg : M sp, ∀ σ : C sp,
        Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp sp msg] = invK := by
    intro msg σ
    let keyExp : ProbComp (K sp) := simulateQ encAlg.impl (encAlg.keygen sp)
    let encExp : K sp → ProbComp (C sp) := fun k => simulateQ encAlg.impl (encAlg.encrypt k msg)
    obtain ⟨k0, hk0, hk0uniq⟩ := hUniqueKey msg σ
    have henc_one :
        Pr[= σ | encExp k0] = 1 := by
      rcases deterministicEnc k0 msg with ⟨c0, hc0⟩
      have hσ_mem : σ ∈ support (simulateQ encAlg.impl (encAlg.encrypt k0 msg)) := by
        simpa [encExp] using hk0.2
      have hσ_mem_singleton : σ ∈ ({c0} : Set (C sp)) := by
        simpa [hc0] using hσ_mem
      have hσ_eq_c0 : σ = c0 := by
        simpa using hσ_mem_singleton
      have hpf0 : Pr[⊥ | encExp k0] = 0 := by
        simp [encExp]
      have hsuppσ : support (encExp k0) = ({σ} : Set (C sp)) := by
        simpa [encExp, hσ_eq_c0] using hc0
      rw [probOutput_eq_one_iff]
      exact ⟨hpf0, hsuppσ⟩
    rw [PerfectSecrecyCipherGivenMsgExp, simulateQ_bind, probOutput_bind_eq_tsum]
    calc
      ∑' k : K sp, Pr[= k | keyExp] * Pr[= σ | encExp k] =
          Pr[= k0 | keyExp] * Pr[= σ | encExp k0] := by
            refine (tsum_eq_single k0 ?_).trans ?_
            · intro k hkne
              by_cases hkKey : k ∈ support keyExp
              · have hkEnc : σ ∉ support (encExp k) := by
                  intro hkEnc'
                  exact hkne (hk0uniq k ⟨by simpa [keyExp] using hkKey, by simpa [encExp] using hkEnc'⟩)
                simp [probOutput_eq_zero_of_not_mem_support hkEnc]
              · simp [probOutput_eq_zero_of_not_mem_support hkKey]
            · simp
      _ = invK := by
          have hk0_uniform : Pr[= k0 | keyExp] = invK := by
            simpa [keyExp, invK] using hKeyUniform k0
          simp [hk0_uniform, henc_one]
  have hCipher_uniform :
      ∀ (mgen : OracleComp encAlg.spec (M sp)) (σ : C sp),
        Pr[= σ | encAlg.PerfectSecrecyCipherExp sp mgen] = invK := by
    intro mgen σ
    have hPrior_sum :
        (∑' msg : M sp, Pr[= msg | encAlg.PerfectSecrecyPriorExp sp mgen]) = 1 := by
      exact HasEvalPMF.tsum_probOutput_eq_one (encAlg.PerfectSecrecyPriorExp sp mgen)
    calc
      Pr[= σ | encAlg.PerfectSecrecyCipherExp sp mgen] =
          ∑' msg : M sp,
            Pr[= msg | encAlg.PerfectSecrecyPriorExp sp mgen] *
              Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp sp msg] := by
            simpa using encAlg.probOutput_PerfectSecrecyCipherExp_eq_tsum sp mgen σ
      _ = ∑' msg : M sp, Pr[= msg | encAlg.PerfectSecrecyPriorExp sp mgen] * invK := by
            refine tsum_congr fun msg => ?_
            rw [hCipherGiven_uniform msg σ]
      _ = (∑' msg : M sp, Pr[= msg | encAlg.PerfectSecrecyPriorExp sp mgen]) * invK := by
            rw [ENNReal.tsum_mul_right]
      _ = invK := by rw [hPrior_sum, one_mul]
  intro mgen msg σ
  calc
    Pr[= (msg, σ) | encAlg.PerfectSecrecyExp sp mgen] =
        Pr[= msg | encAlg.PerfectSecrecyPriorExp sp mgen] *
          Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp sp msg] := by
            simpa using encAlg.probOutput_PerfectSecrecyExp_eq_mul_cipherGivenMsg sp mgen msg σ
    _ = Pr[= msg | encAlg.PerfectSecrecyPriorExp sp mgen] * invK := by
          rw [hCipherGiven_uniform msg σ]
    _ = Pr[= msg | encAlg.PerfectSecrecyPriorExp sp mgen] *
        Pr[= σ | encAlg.PerfectSecrecyCipherExp sp mgen] := by
          rw [hCipher_uniform mgen σ]

theorem perfectSecrecy_iff_of_card_eq (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    [Fintype (M sp)] [Fintype (K sp)] [Fintype (C sp)]
    (hComplete : encAlg.Complete)
    (h1 : Fintype.card (M sp) = Fintype.card (K sp))
    (h2 : Fintype.card (K sp) = Fintype.card (C sp))
    (deterministicEnc : ∀ (k : K sp) (msg : M sp),
      ∃ c, support (simulateQ encAlg.impl (encAlg.encrypt k msg)) = {c})
    (hForward : encAlg.perfectSecrecyAt sp →
      ((∀ k : K sp, Pr[= k | simulateQ encAlg.impl (encAlg.keygen sp)] =
          (Fintype.card (K sp) : ℝ≥0∞)⁻¹) ∧
      (∀ msg : M sp, ∀ c : C sp, ∃! k : K sp,
          k ∈ support (simulateQ encAlg.impl (encAlg.keygen sp)) ∧
          c ∈ support (simulateQ encAlg.impl (encAlg.encrypt k msg))))) :
    encAlg.perfectSecrecyAt sp ↔
    ((∀ k : K sp, Pr[= k | simulateQ encAlg.impl (encAlg.keygen sp)] =
        (Fintype.card (K sp) : ℝ≥0∞)⁻¹) ∧
    (∀ msg : M sp, ∀ c : C sp, ∃! k : K sp,
        k ∈ support (simulateQ encAlg.impl (encAlg.keygen sp)) ∧
        c ∈ support (simulateQ encAlg.impl (encAlg.encrypt k msg)))) :=
by
  constructor
  · exact perfectSecrecy_iff_of_card_eq_forward encAlg sp hComplete h1 h2 deterministicEnc hForward
  · exact perfectSecrecy_iff_of_card_eq_backward encAlg sp hComplete h1 h2 deterministicEnc

end perfectSecrecy

end SymmEncAlg
