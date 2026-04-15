/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.EvalDist.Prod
import VCVio.OracleComp.ProbComp

/-!
# Symmetric Encryption Schemes

This file defines `SymmEncAlg m M K C`, a monad-generic symmetric encryption scheme with
message space `M`, key space `K`, and ciphertext space `C`.

The struct follows the same pattern as `AsymmEncAlg`, `KEMScheme`, `MacAlg`, etc.: it is
parameterized by an ambient monad `m` and uses plain `Type` parameters. Asymptotic security
statements are expressed externally by quantifying over a family
`(sp : ℕ) → SymmEncAlg m (M sp) (K sp) (C sp)`.
-/

universe u

open OracleComp ENNReal

structure SymmEncAlg (m : Type → Type u) [Monad m] (M K C : Type) where
  keygen : m K
  encrypt : K → M → m C
  decrypt : K → C → m (Option M)

namespace SymmEncAlg

variable {m : Type → Type u} [Monad m] {M K C : Type}

def CompleteExp (encAlg : SymmEncAlg m M K C) (msg : M) : m (Option M) := do
  let k ← encAlg.keygen
  let σ ← encAlg.encrypt k msg
  encAlg.decrypt k σ

def Complete [HasEvalPMF m] (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ msg : M, Pr[= msg | encAlg.CompleteExp msg] = 1

section perfectSecrecy

/-! ## Definitions and Equivalences

`perfectSecrecyAt` is the canonical notion (independence form).
We also provide equivalent formulations:
* `perfectSecrecyPosteriorEqPriorAt` (cross-multiplied posterior/prior form),
* `perfectSecrecyJointFactorizationAt` (same factorization with named marginals).

The `_iff_` lemmas below record equivalence between these forms. -/

/-- Joint message/ciphertext experiment used to express perfect secrecy. -/
def PerfectSecrecyExp (encAlg : SymmEncAlg m M K C)
    (mgen : m M) : m (M × C) := do
  let msg' ← mgen
  let k ← encAlg.keygen
  return (msg', ← encAlg.encrypt k msg')

/-- Ciphertext marginal induced by the perfect-secrecy experiment. -/
def PerfectSecrecyCipherExp (encAlg : SymmEncAlg m M K C)
    (mgen : m M) : m C :=
  Prod.snd <$> encAlg.PerfectSecrecyExp mgen

/-- Ciphertext experiment conditioned on a fixed message. -/
def PerfectSecrecyCipherGivenMsgExp (encAlg : SymmEncAlg m M K C)
    (msg : M) : m C := do
  let k ← encAlg.keygen
  encAlg.encrypt k msg

lemma PerfectSecrecyExp_eq_bind [LawfulMonad m] (encAlg : SymmEncAlg m M K C)
    (mgen : m M) :
    encAlg.PerfectSecrecyExp mgen =
      mgen >>= fun msg =>
        (msg, ·) <$> encAlg.PerfectSecrecyCipherGivenMsgExp msg := by
  simp [PerfectSecrecyExp, PerfectSecrecyCipherGivenMsgExp,
    map_eq_bind_pure_comp, bind_assoc]

lemma PerfectSecrecyCipherExp_eq_bind [LawfulMonad m] (encAlg : SymmEncAlg m M K C)
    (mgen : m M) :
    encAlg.PerfectSecrecyCipherExp mgen =
      mgen >>= fun msg =>
        encAlg.PerfectSecrecyCipherGivenMsgExp msg := by
  simp [PerfectSecrecyCipherExp, PerfectSecrecyExp_eq_bind, map_eq_bind_pure_comp, bind_assoc]

variable [HasEvalPMF m]

lemma probOutput_PerfectSecrecyExp_eq_mul_cipherGivenMsg [LawfulMonad m]
    (encAlg : SymmEncAlg m M K C) (mgen : m M) (msg : M) (σ : C) :
    Pr[= (msg, σ) | encAlg.PerfectSecrecyExp mgen] =
      Pr[= msg | mgen] *
      Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp msg] := by
  haveI : DecidableEq M := Classical.decEq M
  rw [encAlg.PerfectSecrecyExp_eq_bind mgen, probOutput_bind_eq_tsum]
  have hinner (msg' : M) :
      Pr[= (msg, σ) | (fun x => (msg', x)) <$> encAlg.PerfectSecrecyCipherGivenMsgExp msg'] =
        if msg = msg' then Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp msg'] else 0 := by
    exact
      (probOutput_prod_mk_snd_map
        (my := encAlg.PerfectSecrecyCipherGivenMsgExp msg')
        (x := msg') (z := (msg, σ)))
  simp_rw [hinner]
  calc
    ∑' msg', Pr[= msg' | mgen] *
        (if msg = msg' then Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp msg'] else 0) =
      Pr[= msg | mgen] *
        Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp msg] := by
        refine (tsum_eq_single msg ?_).trans ?_
        · intro msg' hmsg'
          have hneq : msg ≠ msg' := by simpa [eq_comm] using hmsg'
          simp [hneq]
        · simp

lemma probOutput_PerfectSecrecyCipherExp_eq_tsum [LawfulMonad m]
    (encAlg : SymmEncAlg m M K C) (mgen : m M) (σ : C) :
    Pr[= σ | encAlg.PerfectSecrecyCipherExp mgen] =
      ∑' msg : M,
        Pr[= msg | mgen] *
        Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp msg] := by
  haveI : DecidableEq M := Classical.decEq M
  rw [encAlg.PerfectSecrecyCipherExp_eq_bind mgen, probOutput_bind_eq_tsum]

private lemma eq_of_inv_mul_eq_inv_mul {a b n : ℝ≥0∞}
    (hn0 : n ≠ 0) (hnTop : n ≠ ⊤) (h : n⁻¹ * a = n⁻¹ * b) : a = b := by
  have h1 : n * (n⁻¹ * a) = a := by rw [← mul_assoc, ENNReal.mul_inv_cancel hn0 hnTop, one_mul]
  have h2 : n * (n⁻¹ * b) = b := by rw [← mul_assoc, ENNReal.mul_inv_cancel hn0 hnTop, one_mul]
  rw [← h1, ← h2, h]

/-- Strong perfect secrecy: ciphertexts are independent of messages
for every prior distribution on messages (PMF-level quantification). -/
def perfectSecrecyAtAllPriors (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ (μ : PMF M) (msg : M) (σ : C),
    let row := fun x : M => Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp x]
    μ msg * row msg = μ msg * (∑' x : M, μ x * row x)

/-- Equivalent channel-style formulation: every message induces the same ciphertext
distribution. -/
def ciphertextRowsEqualAt (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ (msg₀ msg₁ : M) (σ : C),
    Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp msg₀] =
      Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp msg₁]

theorem perfectSecrecyAtAllPriors_iff_ciphertextRowsEqualAt
    (encAlg : SymmEncAlg m M K C) [Finite M] :
    encAlg.perfectSecrecyAtAllPriors ↔ encAlg.ciphertextRowsEqualAt := by
  have : Fintype M := Fintype.ofFinite M
  constructor
  · intro hAll msg₀ msg₁ σ
    haveI : Nonempty M := ⟨msg₀⟩
    let μ : PMF M := PMF.uniformOfFintype M
    let row := fun x : M => Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp x]
    let s : ℝ≥0∞ := ∑' x : M, μ x * row x
    let c : ℝ≥0∞ := (Fintype.card M : ℝ≥0∞)⁻¹
    have hμ : ∀ x : M, μ x = c := by
      intro x
      simp [μ, c, PMF.uniformOfFintype_apply]
    have h0 : c * row msg₀ = c * s := by
      simpa [perfectSecrecyAtAllPriors, μ, row, s, c, hμ msg₀] using hAll μ msg₀ σ
    have h1 : c * row msg₁ = c * s := by
      simpa [perfectSecrecyAtAllPriors, μ, row, s, c, hμ msg₁] using hAll μ msg₁ σ
    have hn0 : (Fintype.card M : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hnTop : (Fintype.card M : ℝ≥0∞) ≠ ⊤ := by simp
    have h0' : row msg₀ = s := eq_of_inv_mul_eq_inv_mul hn0 hnTop (by simpa [c] using h0)
    have h1' : row msg₁ = s := eq_of_inv_mul_eq_inv_mul hn0 hnTop (by simpa [c] using h1)
    exact h0'.trans h1'.symm
  · intro hRows μ msg σ
    let row := fun x : M => Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp x]
    let q : ℝ≥0∞ := row msg
    have hrow : ∀ x : M, row x = q := fun x => (hRows x msg σ).trans rfl
    have hsum : ∑' x : M, μ x * row x = q := by
      calc
        ∑' x : M, μ x * row x = ∑' x : M, μ x * q := by
          refine tsum_congr fun x => ?_
          rw [hrow x]
        _ = (∑' x : M, μ x) * q := by rw [ENNReal.tsum_mul_right]
        _ = 1 * q := by rw [μ.tsum_coe]
        _ = q := by simp
    calc
      μ msg * Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp msg] = μ msg * q := rfl
      _ = μ msg * (∑' x : M, μ x * row x) := by rw [← hsum]
      _ = μ msg * (∑' x : M, μ x *
        Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp x]) := rfl

/-- Standard perfect secrecy expressed as independence:
`Pr[(M, C)] = Pr[M] * Pr[C]`. -/
def perfectSecrecyAt (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ mgen : m M, ∀ msg : M, ∀ σ : C,
    Pr[= (msg, σ) | encAlg.PerfectSecrecyExp mgen] =
      Pr[= msg | mgen] *
      Pr[= σ | encAlg.PerfectSecrecyCipherExp mgen]

/-- Posterior-equals-prior form, written in cross-multiplied form to avoid division. -/
def perfectSecrecyPosteriorEqPriorAt (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ mgen : m M, ∀ msg : M, ∀ σ : C,
    Pr[= (msg, σ) | encAlg.PerfectSecrecyExp mgen] =
      Pr[= σ | encAlg.PerfectSecrecyCipherExp mgen] *
      Pr[= msg | mgen]

/-- Joint-factorization form (same mathematical statement as independence, with explicit
named priors/marginals). -/
def perfectSecrecyJointFactorizationAt
    (encAlg : SymmEncAlg m M K C) : Prop :=
  ∀ mgen : m M, ∀ msg : M, ∀ σ : C,
    Pr[= (msg, σ) | encAlg.PerfectSecrecyExp mgen] =
      Pr[= msg | mgen] * Pr[= σ | encAlg.PerfectSecrecyCipherExp mgen]

lemma perfectSecrecyAt_iff_posteriorEqPriorAt (encAlg : SymmEncAlg m M K C) :
    encAlg.perfectSecrecyAt ↔ encAlg.perfectSecrecyPosteriorEqPriorAt := by
  constructor <;> intro h <;> intro mgen msg σ
  · simpa [perfectSecrecyAt, perfectSecrecyPosteriorEqPriorAt, mul_comm] using h mgen msg σ
  · simpa [perfectSecrecyAt, perfectSecrecyPosteriorEqPriorAt, mul_comm] using h mgen msg σ

lemma perfectSecrecyAt_iff_jointFactorizationAt (encAlg : SymmEncAlg m M K C) :
    encAlg.perfectSecrecyAt ↔ encAlg.perfectSecrecyJointFactorizationAt := by
  constructor
  · intro h
    simpa [perfectSecrecyAt, perfectSecrecyJointFactorizationAt]
      using h
  · intro h
    simpa [perfectSecrecyAt, perfectSecrecyJointFactorizationAt]
      using h

/-- Core uniformity lemma: uniform keygen plus unique key per (message, ciphertext) pair
implies every (message, ciphertext) conditional has probability `(card K)⁻¹`.
Both Shannon theorems follow from this. -/
theorem cipherGivenMsg_uniform_of_uniformKey_of_uniqueKey
    (encAlg : SymmEncAlg m M K C) [Fintype K]
    (deterministicEnc : ∀ (k : K) (msg : M),
      ∃ c, support (encAlg.encrypt k msg) = {c})
    (hKeyUniform : ∀ k : K, Pr[= k | encAlg.keygen] =
        (Fintype.card K : ℝ≥0∞)⁻¹)
    (hUniqueKey : ∀ msg : M, ∀ c : C, ∃! k : K,
        k ∈ support encAlg.keygen ∧
        c ∈ support (encAlg.encrypt k msg))
    (msg : M) (σ : C) :
    Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp msg] =
      (Fintype.card K : ℝ≥0∞)⁻¹ := by
  let invK : ℝ≥0∞ := (Fintype.card K : ℝ≥0∞)⁻¹
  let keyExp := encAlg.keygen
  let encExp := fun k => encAlg.encrypt k msg
  obtain ⟨k0, hk0, hk0uniq⟩ := hUniqueKey msg σ
  have henc_one :
      Pr[= σ | encExp k0] = 1 := by
    rcases deterministicEnc k0 msg with ⟨c0, hc0⟩
    have hσ_mem : σ ∈ support (encAlg.encrypt k0 msg) := hk0.2
    have hσ_mem_singleton : σ ∈ ({c0} : Set C) := by
      simpa [hc0] using hσ_mem
    have hσ_eq_c0 : σ = c0 := by
      simpa using hσ_mem_singleton
    have hsuppσ : support (encExp k0) = ({σ} : Set C) := by
      simpa [encExp, hσ_eq_c0] using hc0
    rw [probOutput_eq_one_iff]
    exact ⟨HasEvalPMF.probFailure_eq_zero _, hsuppσ⟩
  simp only [PerfectSecrecyCipherGivenMsgExp, probOutput_bind_eq_tsum]
  calc
    ∑' k : K, Pr[= k | keyExp] * Pr[= σ | encExp k] =
        Pr[= k0 | keyExp] * Pr[= σ | encExp k0] := by
          exact tsum_eq_single k0 fun k hkne => by
            by_cases hkKey : k ∈ support keyExp
            · have hkEnc : σ ∉ support (encExp k) := by
                intro hkEnc'
                exact hkne <| hk0uniq k ⟨hkKey, hkEnc'⟩
              simp [probOutput_eq_zero_of_not_mem_support hkEnc]
            · simp [probOutput_eq_zero_of_not_mem_support hkKey]
    _ = invK := by
        have hk0_uniform : Pr[= k0 | keyExp] = invK := hKeyUniform k0
        simp [hk0_uniform, henc_one]

theorem ciphertextRowsEqualAt_of_uniformKey_of_uniqueKey
    (encAlg : SymmEncAlg m M K C) [Fintype K]
    (deterministicEnc : ∀ (k : K) (msg : M),
      ∃ c, support (encAlg.encrypt k msg) = {c})
    (hKeyUniform : ∀ k : K, Pr[= k | encAlg.keygen] =
        (Fintype.card K : ℝ≥0∞)⁻¹)
    (hUniqueKey : ∀ msg : M, ∀ c : C, ∃! k : K,
        k ∈ support encAlg.keygen ∧
        c ∈ support (encAlg.encrypt k msg)) :
    encAlg.ciphertextRowsEqualAt := by
  intro msg₀ msg₁ σ
  rw [encAlg.cipherGivenMsg_uniform_of_uniformKey_of_uniqueKey
        deterministicEnc hKeyUniform hUniqueKey msg₀ σ,
      encAlg.cipherGivenMsg_uniform_of_uniformKey_of_uniqueKey
        deterministicEnc hKeyUniform hUniqueKey msg₁ σ]

/-- Constructive Shannon direction: if keygen is uniform and each `(message, ciphertext)`
pair is realized by a unique key in support, then perfect secrecy holds.

`deterministicEnc` asserts encryption is deterministic in distribution
(singleton support for each fixed `(key, message)`). -/
theorem perfectSecrecyAt_of_uniformKey_of_uniqueKey [LawfulMonad m]
    (encAlg : SymmEncAlg m M K C)
    [Fintype K]
    (deterministicEnc : ∀ (k : K) (msg : M),
      ∃ c, support (encAlg.encrypt k msg) = {c}) :
    ((∀ k : K, Pr[= k | encAlg.keygen] =
        (Fintype.card K : ℝ≥0∞)⁻¹) ∧
    (∀ msg : M, ∀ c : C, ∃! k : K,
        k ∈ support encAlg.keygen ∧
        c ∈ support (encAlg.encrypt k msg))) →
    encAlg.perfectSecrecyAt := by
  intro ⟨hKeyUniform, hUniqueKey⟩
  let invK : ℝ≥0∞ := (Fintype.card K : ℝ≥0∞)⁻¹
  have hCipherGiven_uniform := encAlg.cipherGivenMsg_uniform_of_uniformKey_of_uniqueKey
    deterministicEnc hKeyUniform hUniqueKey
  have hCipher_uniform :
      ∀ (mgen : m M) (σ : C),
        Pr[= σ | encAlg.PerfectSecrecyCipherExp mgen] = invK := by
    intro mgen σ
    calc
      Pr[= σ | encAlg.PerfectSecrecyCipherExp mgen] =
          ∑' msg : M,
            Pr[= msg | mgen] *
              Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp msg] := by
            simpa using encAlg.probOutput_PerfectSecrecyCipherExp_eq_tsum mgen σ
      _ = ∑' msg : M, Pr[= msg | mgen] * invK := by
            refine tsum_congr fun msg => ?_
            rw [hCipherGiven_uniform msg σ]
      _ = (∑' msg : M, Pr[= msg | mgen]) * invK := by
            rw [ENNReal.tsum_mul_right]
      _ = invK := by
            rw [HasEvalPMF.tsum_probOutput_eq_one mgen, one_mul]
  intro mgen msg σ
  calc
    Pr[= (msg, σ) | encAlg.PerfectSecrecyExp mgen] =
        Pr[= msg | mgen] *
          Pr[= σ | encAlg.PerfectSecrecyCipherGivenMsgExp msg] := by
            simpa using encAlg.probOutput_PerfectSecrecyExp_eq_mul_cipherGivenMsg mgen msg σ
    _ = Pr[= msg | mgen] * invK := by
          rw [hCipherGiven_uniform msg σ]
    _ = Pr[= msg | mgen] *
        Pr[= σ | encAlg.PerfectSecrecyCipherExp mgen] := by
          rw [hCipher_uniform mgen σ]

/-- Constructive Shannon direction for all priors: uniform keys plus uniqueness
imply perfect secrecy for all prior distributions on messages. -/
theorem perfectSecrecyAtAllPriors_of_uniformKey_of_uniqueKey
    (encAlg : SymmEncAlg m M K C)
    [Finite M] [Fintype K]
    (deterministicEnc : ∀ (k : K) (msg : M),
      ∃ c, support (encAlg.encrypt k msg) = {c}) :
    ((∀ k : K, Pr[= k | encAlg.keygen] =
        (Fintype.card K : ℝ≥0∞)⁻¹) ∧
    (∀ msg : M, ∀ c : C, ∃! k : K,
        k ∈ support encAlg.keygen ∧
        c ∈ support (encAlg.encrypt k msg))) →
    encAlg.perfectSecrecyAtAllPriors := by
  intro ⟨hKeyUniform, hUniqueKey⟩
  exact (encAlg.perfectSecrecyAtAllPriors_iff_ciphertextRowsEqualAt).2
    (encAlg.ciphertextRowsEqualAt_of_uniformKey_of_uniqueKey
      deterministicEnc hKeyUniform hUniqueKey)

end perfectSecrecy

end SymmEncAlg
