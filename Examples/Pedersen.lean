/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.CommitmentScheme
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.ProgramLogic.NotationCore

/-!
# Pedersen Commitment Scheme

This file defines the Pedersen commitment scheme and proves:
1. **Correctness**: honestly generated commitments verify.
2. **Perfect hiding**: the commitment distribution is independent of the message
   (via a bijection argument, same pattern as one-time pad).
3. **Computational binding**: a successful double-opener yields a DLog solver.

## Mathematical Setup

Uses the same additive `Module F G` notation as `DiffieHellman.lean`:
- `F` is the scalar field (exponents), `G` is the group
- `g : G` is a fixed generator with `Function.Bijective (· • g : F → G)`
- Public parameter: `h = x • g` for secret random `x : F`
- Commitment to message `m : F`: sample `d ← $ᵗ F`, output `(d • g + m • h, d)`
- Verification: check `c = d • g + m • h`
-/

open OracleComp OracleSpec ENNReal DiffieHellman CommitmentScheme

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]

/-! ## Definition -/

/-- The Pedersen commitment scheme over a cyclic group with generator `g`.

| Component | Definition |
|-----------|-----------|
| Setup | Sample `x ← $ᵗ F`, return `h = x • g` |
| Commit(h, m) | Sample `d ← $ᵗ F`, return `(d • g + m • h, d)` |
| Verify(h, m, c, d) | Check `d • g + m • h = c` |
-/
def pedersenCommit (g : G) : CommitmentScheme G F G F where
  setup := do let x ← $ᵗ F; return (x • g)
  commit pp m := do
    let d ← $ᵗ F
    return (d • g + m • pp, d)
  verify pp m c d := decide (d • g + m • pp = c)

namespace pedersenCommit

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
variable {g : G}

/-! ## Correctness -/

omit [Fintype F] [DecidableEq F] [SampleableType G] in
theorem correct : (pedersenCommit (F := F) g).PerfectlyCorrect := by
  intro pp _hpp m cd hmem
  have hmem' : cd ∈ support (do
      let d ← ($ᵗ F); pure ((d : F) • g + m • pp, d)) := hmem
  simp only [support_bind, support_pure, Set.mem_iUnion,
             Set.mem_singleton_iff] at hmem'
  obtain ⟨d', -, rfl, rfl⟩ := hmem'
  change decide ((d' : F) • g + m • pp = d' • g + m • pp) = true
  simp

/-! ## Perfect hiding -/

omit [Fintype F] [DecidableEq F] [SampleableType F]
  [SampleableType G] [DecidableEq G] in
private lemma commit_fst_bijective (hg : Function.Bijective (· • g : F → G))
    (pp : G) (m : F) : Function.Bijective (fun d : F => d • g + m • pp) := by
  change Function.Bijective ((· + m • pp) ∘ (· • g : F → G))
  exact Function.Bijective.comp
    ⟨fun a b h => add_right_cancel h,
     fun y => ⟨y - m • pp, sub_add_cancel y (m • pp)⟩⟩
    hg

omit [Fintype F] [DecidableEq F] [SampleableType G] in
/-- Rewrite the commitment distribution as a mapped uniform sample. -/
private lemma commit_fst_eq_map (pp : G) (m : F) :
    Prod.fst <$> (pedersenCommit (F := F) g).commit pp m =
    (fun d : F => d • g + m • pp) <$> ($ᵗ F) := by
  simp [pedersenCommit]

omit [Fintype F] [DecidableEq F] in
/-- The Pedersen commitment scheme is perfectly hiding: the commitment distribution
is independent of the committed message.

The proof uses the same bijection-coupling idea as the one-time pad: composing
the generator bijection `d ↦ d • g` with translation `· + c` gives a bijection
`F → G`, so the pushforward of uniform on `F` is uniform on `G` regardless of `c`. -/
theorem perfectlyHiding [Finite F] (hg : Function.Bijective (· • g : F → G)) :
    (pedersenCommit (F := F) g).PerfectlyHiding := by
  let _ : Fintype F := Fintype.ofFinite F
  intro pp _hpp m₁ m₂
  rw [commit_fst_eq_map, commit_fst_eq_map]
  have h₁ := evalDist_map_bijective_uniform_cross (α := F) (β := G)
    (fun d => d • g + m₁ • pp) (commit_fst_bijective hg pp m₁)
  have h₂ := evalDist_map_bijective_uniform_cross (α := F) (β := G)
    (fun d => d • g + m₂ • pp) (commit_fst_bijective hg pp m₂)
  exact h₁.trans h₂.symm

/-! ## Computational binding reduces to DLog -/

/-- Given a binding adversary for Pedersen, construct a DLog adversary.
If the binder produces two valid openings `(m₁, d₁)` and `(m₂, d₂)` to the same
commitment `c` with `m₁ ≠ m₂`, extract the discrete log as `(d₁ - d₂) / (m₂ - m₁)`. -/
def dlogReduction (binder : BindingAdv G F G F) : DLogAdversary F G :=
  fun gen h => do
    let (c, m₁, d₁, m₂, d₂) ← binder h
    return if decide (m₁ ≠ m₂ ∧ d₁ • gen + m₁ • h = c ∧ d₂ • gen + m₂ • h = c) then
      (d₁ - d₂) / (m₂ - m₁)
    else 0

omit [Fintype F] [DecidableEq F] [SampleableType F]
  [SampleableType G] [DecidableEq G] in
private lemma extractedLog_eq_dlog (hg : Function.Bijective (· • g : F → G))
    {x m₁ d₁ m₂ d₂ : F} {c : G}
    (hm : m₁ ≠ m₂)
    (h₁ : d₁ • g + m₁ • (x • g) = c)
    (h₂ : d₂ • g + m₂ • (x • g) = c) :
    (d₁ - d₂) / (m₂ - m₁) = x := by
  have hmul : d₁ - d₂ = (m₂ - m₁) * x := by
    have hcoeff : d₁ + m₁ * x = d₂ + m₂ * x := by
      apply hg.1
      calc
        (d₁ + m₁ * x) • g = d₁ • g + m₁ • (x • g) := by rw [add_smul, mul_smul]
        _ = c := h₁
        _ = d₂ • g + m₂ • (x • g) := h₂.symm
        _ = (d₂ + m₂ * x) • g := by rw [add_smul, mul_smul]
    have hcoeff' := congrArg (fun t : F => t - d₂ - m₁ * x) hcoeff
    ring_nf at hcoeff' ⊢
    exact hcoeff'
  have hneq : m₂ - m₁ ≠ 0 := sub_ne_zero.mpr hm.symm
  calc
    (d₁ - d₂) / (m₂ - m₁)
        = ((m₂ - m₁) * x) / (m₂ - m₁) := by rw [hmul]
    _ = x := by
      field_simp [hneq]

omit [Fintype F] [SampleableType F] [SampleableType G] in
private lemma bindingWin_implies_dlogWin (hg : Function.Bijective (· • g : F → G))
    {x m₁ d₁ m₂ d₂ : F} {c : G}
    (hwin : m₁ ≠ m₂ ∧ d₁ • g + m₁ • (x • g) = c ∧ d₂ • g + m₂ • (x • g) = c) :
    (if decide (m₁ ≠ m₂ ∧ d₁ • g + m₁ • (x • g) = c ∧ d₂ • g + m₂ • (x • g) = c) then
      (d₁ - d₂) / (m₂ - m₁)
    else 0) = x := by
  rcases hwin with ⟨hm, h₁, h₂⟩
  have hdec : decide (m₁ ≠ m₂ ∧ d₁ • g + m₁ • (x • g) = c ∧ d₂ • g + m₂ • (x • g) = c) = true := by
    simp [hm, h₁, h₂]
  simp [hdec, extractedLog_eq_dlog hg hm h₁ h₂]

omit [Fintype F] [SampleableType G] in
/-- Computational binding: a successful Pedersen binding adversary yields a
successful DLog solver. Specifically, `Pr[binding wins] ≤ Pr[DLog wins]`. -/
theorem binding_le_dlog (hg : Function.Bijective (· • g : F → G))
    (binder : BindingAdv G F G F) :
    Pr[= true | (pedersenCommit g).bindingExp binder] ≤
    Pr[= true | dlogExp g (dlogReduction binder)] := by
  let base : ProbComp (F × (G × F × F × F × F)) := do
    let x ← $ᵗ F
    let out ← binder (x • g)
    return (x, out)
  let bindingWin : F × (G × F × F × F × F) → Prop := fun
    | (x, (c, m₁, d₁, m₂, d₂)) =>
        m₁ ≠ m₂ ∧ d₁ • g + m₁ • (x • g) = c ∧ d₂ • g + m₂ • (x • g) = c
  let dlogWin : F × (G × F × F × F × F) → Prop := fun
    | (x, (c, m₁, d₁, m₂, d₂)) =>
        (if decide (m₁ ≠ m₂ ∧ d₁ • g + m₁ • (x • g) = c ∧ d₂ • g + m₂ • (x • g) = c) then
          (d₁ - d₂) / (m₂ - m₁)
        else 0) = x
  have hbinding :
      Pr[= true | (pedersenCommit g).bindingExp binder] = Pr[ bindingWin | base] := by
    rw [← probEvent_eq_eq_probOutput]
    rw [show (pedersenCommit g).bindingExp binder = (fun z => decide (bindingWin z)) <$> base by
      simp [CommitmentScheme.bindingExp, pedersenCommit, base, bindingWin, Bool.and_assoc]]
    rw [probEvent_map]
    refine probEvent_ext ?_
    intro z hz
    rcases z with ⟨x, ⟨c, m₁, d₁, m₂, d₂⟩⟩
    simp [bindingWin, Bool.and_eq_true, decide_eq_true_eq]
  have hdlog :
      Pr[= true | dlogExp g (dlogReduction binder)] = Pr[ dlogWin | base] := by
    rw [← probEvent_eq_eq_probOutput]
    rw [show dlogExp g (dlogReduction binder) = (fun z => decide (dlogWin z)) <$> base by
      simp [DiffieHellman.dlogExp, dlogReduction, base, dlogWin]]
    rw [probEvent_map]
    refine probEvent_ext ?_
    intro z hz
    rcases z with ⟨x, ⟨c, m₁, d₁, m₂, d₂⟩⟩
    simp [dlogWin, decide_eq_true_eq]
  rw [hbinding, hdlog]
  exact OracleComp.ProgramLogic.probEvent_mono base (fun z hwin => by
    rcases z with ⟨x, ⟨c, m₁, d₁, m₂, d₂⟩⟩
    simpa [bindingWin, dlogWin] using bindingWin_implies_dlogWin (g := g) hg hwin)

end pedersenCommit
