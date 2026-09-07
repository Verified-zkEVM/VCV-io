/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTOpenPREFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTDSPRFinalValidity
public import VCVio.CryptoFoundations.HardnessAssumptions.TweakableHash.SMDTTCRFinalValidity

/-!
# Reduction adversaries from SM-DT-OpenPRE to DSPR and TCR

This file formalizes the two concrete adversaries used by the EasyCrypt reduction
`OpenPRE_From_TCR_DSPR_THF.eca`. Both run the OpenPRE adversary's commitment phase, keep precisely
the bounded prefix of committed tweaks, sample the source problem's input distribution, and route
the resulting targets through the assumption game's challenge oracle.

The TCR reduction forwards the OpenPRE adversary's final index and candidate. The DSPR reduction
guesses that a second preimage exists exactly when that candidate differs from the sampled target
or when the selected target was opened. These are executable reductions, not just existential
adversary placeholders.

The finite-fiber algebra needed for the quantitative inequality

`OpenPRE ≤ (DSPR success - SPprob) + 3 · TCR`

is proved here. The remaining program-level probability decomposition and coupling obligations are
kept explicit in `CountingInterface`; the conditional theorem
`advantage_le_tcrDsprBound` derives the bound from precisely that interface. In particular, the
interface records `Problem.HasUniformInputs` and the exact OpenPRE game itself still permits any
input distribution.
-/

@[expose] public section

namespace TweakableHash

open OracleComp OracleSpec ENNReal

variable {ι PkSeed Tweak M Y : Type}

namespace SM_DT_OpenPRE_SourceFinalValidity

/-- Route commitment-phase randomness and collection queries into an assumption game's larger
selection interface, leaving its challenge oracle unavailable to the wrapped OpenPRE adversary. -/
def liftPick
    (prob : Problem ι PkSeed Tweak M Y) :
    QueryImpl (unifSpec + SourceFinalValidity.collectionSpec prob.thColl)
      (OracleComp (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
        SourceFinalValidity.collectionSpec prob.thColl)))
  | .inl q => liftM ((unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
      SourceFinalValidity.collectionSpec prob.thColl)).query (.inl q))
  | .inr q => liftM ((unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
      SourceFinalValidity.collectionSpec prob.thColl)).query (.inr (.inr q)))

/-! ## Assumption problems induced by an OpenPRE problem -/

/-- The TCR problem attacked by the OpenPRE-to-TCR reduction. -/
def Problem.toTCR (prob : Problem ι PkSeed Tweak M Y) :
    SM_DT_TCR_SourceFinalValidity.Problem ι PkSeed Tweak M Y where
  th := prob.th
  thColl := prob.thColl
  numTargets := prob.numTargets

/-- The DSPR problem attacked by the OpenPRE-to-DSPR reduction. -/
def Problem.toDSPR (prob : Problem ι PkSeed Tweak M Y) :
    SM_DT_DSPR_SourceFinalValidity.Problem ι PkSeed Tweak M Y where
  th := prob.th
  thColl := prob.thColl
  numTargets := prob.numTargets

/-! ## Shared target setup -/

/-- In an assumption game's selection phase, sample OpenPRE target inputs and submit them to that
game's challenge oracle. The input list is already the bounded prefix. Returned data contains the
sampled `(tweak, input)` targets needed to implement `open`, and the images shown to OpenPRE. -/
noncomputable def reductionInitialize
    (prob : Problem ι PkSeed Tweak M Y) :
    List Tweak → OracleComp
      (unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
        SourceFinalValidity.collectionSpec prob.thColl)) (List (Tweak × M) × List Y)
  | [] => pure ([], [])
  | t :: ts => do
      let x ← liftM prob.inputGen
      let y ← liftM ((unifSpec + (SM_DT_TCR_SourceFinalValidity.challengeSpec Tweak M Y +
        SourceFinalValidity.collectionSpec prob.thColl)).query (.inr (.inl (t, x))))
      let (targets, ys) ← reductionInitialize prob ts
      return ((t, x) :: targets, y :: ys)

/-! ## Concrete TCR reduction -/

/-- Concrete reduction from an OpenPRE adversary to a TCR adversary. Opening queries are simulated
from the sampled target inputs; the reduction then forwards the selected index and candidate. -/
noncomputable def toTCR [Inhabited M]
    {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) : SM_DT_TCR_SourceFinalValidity.Adversary prob.toTCR where
  State := adv.State × List (Tweak × M) × List Y
  choose := do
    let (privateState, tweaks) ← simulateQ (liftPick prob) adv.pick
    let (targets, ys) ←
      reductionInitialize prob (tweaks.take prob.numTargets)
    return (privateState, targets, ys)
  forge state pk := do
    let (privateState, targets, ys) := state
    let ((j, m), _) ←
      (simulateQ (findOracles targets) (adv.find privateState pk ys)).run []
    return (j, m)

/-! ## Concrete DSPR reduction -/

/-- Concrete reduction from an OpenPRE adversary to a DSPR adversary. It predicts that the selected
target has a second preimage iff the candidate differs from the sampled input or the selected target
was opened. An invalid index uses the fixed witness, matching the source oracle's `nth witness`. -/
noncomputable def toDSPR [Inhabited M] [DecidableEq M]
    {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) : SM_DT_DSPR_SourceFinalValidity.Adversary prob.toDSPR where
  State := adv.State × List (Tweak × M) × List Y
  choose := do
    let (privateState, tweaks) ← simulateQ (liftPick prob) adv.pick
    let (targets, ys) ←
      reductionInitialize prob (tweaks.take prob.numTargets)
    return (privateState, targets, ys)
  guess state pk := do
    let (privateState, targets, ys) := state
    let ((j, m), opened) ←
      (simulateQ (findOracles targets) (adv.find privateState pk ys)).run []
    let sampled := (targets[j]?.map Prod.snd).getD default
    return (j, decide (sampled ≠ m ∨ j ∈ opened))

/-! ## Finite preimage counting -/

/-- Cardinality of the fiber of `y` under the hash fixed at `pk` and `t`. -/
def PreimageCount [Fintype M] [DecidableEq Y] (th : TweakableHash PkSeed Tweak M Y)
    (pk : PkSeed) (t : Tweak) (y : Y) : ℕ :=
  (Finset.univ.filter fun m => th.eval pk t m = y).card

/-- Every actual hash image has a nonempty fiber. -/
theorem one_le_preimageCount_image [Fintype M] [DecidableEq Y]
    (th : TweakableHash PkSeed Tweak M Y) (pk : PkSeed) (t : Tweak) (m : M) :
    1 ≤ PreimageCount th pk t (th.eval pk t m) := by
  change 0 < (Finset.univ.filter fun m' => th.eval pk t m' = th.eval pk t m).card
  rw [Finset.card_pos]
  exact ⟨m, by simp⟩

/-- No fiber is larger than the finite message space. -/
theorem preimageCount_le_card [Fintype M] [DecidableEq Y]
    (th : TweakableHash PkSeed Tweak M Y) (pk : PkSeed) (t : Tweak) (y : Y) :
    PreimageCount th pk t y ≤ Fintype.card M := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The DSPR predicate is exactly the statement that the selected image's fiber has cardinality at
least two. This is the finite-preimage lemma called `eqv_spex_szprefl` in the EasyCrypt proof. -/
theorem secondPreimageExists_iff_two_le_preimageCount [Fintype M] [DecidableEq Y]
    (th : TweakableHash PkSeed Tweak M Y) (pk : PkSeed) (t : Tweak) (m : M) :
    SecondPreimageExists th pk t m ↔ 2 ≤ PreimageCount th pk t (th.eval pk t m) := by
  classical
  let s : Finset M := Finset.univ.filter fun m' => th.eval pk t m' = th.eval pk t m
  have hm : m ∈ s := by simp [s]
  change SecondPreimageExists th pk t m ↔ 2 ≤ s.card
  rw [show 2 ≤ s.card ↔ 1 < s.card by omega, Finset.one_lt_card]
  constructor
  · rintro ⟨m', hne, heq⟩
    exact ⟨m, hm, m', by simp [s, heq], hne⟩
  · rintro ⟨a, ha, b, hb, hab⟩
    by_cases ham : a = m
    · refine ⟨b, ?_, ?_⟩
      · intro hmb
        exact hab (ham.trans hmb)
      · have hbEq : th.eval pk t b = th.eval pk t m := by simpa [s] using hb
        exact hbEq.symm
    · refine ⟨a, (fun hma => ham hma.symm), ?_⟩
      have haEq : th.eval pk t a = th.eval pk t m := by simpa [s] using ha
      exact haEq.symm

/-! ## Algebra of the fiber-cardinality strata -/

/-- Reciprocal mass subtracted by the DSPR/SPprob gap on fibers of size at least two. -/
noncomputable def reciprocalMass {α : Type} [Fintype α]
    (fiberSize : α → ℕ) (mass : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ a, 1 / (fiberSize a : ℝ≥0∞) * mass a

/-- Collision mass gained by TCR on fibers of size at least two. -/
noncomputable def collisionMass {α : Type} [Fintype α]
    (fiberSize : α → ℕ) (mass : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ a, ((fiberSize a - 1 : ℕ) : ℝ≥0∞) / fiberSize a * mass a

/-- For a fiber of size `n ≥ 2`, the source proof's coefficient inequality is
`1 + 1/n ≤ 3(n-1)/n`. -/
theorem openPRE_fiber_coefficient_le (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ≥0∞) + 1 / n ≤ 3 * ((n - 1 : ℕ) / n : ℝ≥0∞) := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  have hnInf : (n : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  rw [show (1 : ℝ≥0∞) + 1 / n = (n + 1) / n by
    calc
      (1 : ℝ≥0∞) + 1 / n = n / n + 1 / n := by rw [ENNReal.div_self hn0 hnInf]
      _ = (n + 1) / n := by exact ENNReal.div_add_div_same]
  rw [ENNReal.div_le_iff hn0 hnInf, mul_assoc]
  rw [ENNReal.div_mul_cancel hn0 hnInf]
  norm_num
  exact_mod_cast (by omega : n + 1 ≤ 3 * (n - 1))

/-- Summing the pointwise coefficient inequality over arbitrary fiber-cardinality strata. -/
theorem openPRE_multipleMass_add_reciprocal_le_three_collision {α : Type} [Fintype α]
    (fiberSize : α → ℕ) (mass : α → ℝ≥0∞) (hsize : ∀ a, 2 ≤ fiberSize a) :
    (∑ a, mass a) + reciprocalMass fiberSize mass ≤
      3 * collisionMass fiberSize mass := by
  rw [reciprocalMass, collisionMass,
    ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  let n := fiberSize a
  have hn : 2 ≤ n := hsize a
  have hcoeff := openPRE_fiber_coefficient_le n hn
  calc
    mass a + 1 / (fiberSize a : ℝ≥0∞) * mass a =
        ((1 : ℝ≥0∞) + 1 / n) * mass a := by simp [n, add_mul]
    _ ≤ (3 * ((n - 1 : ℕ) / n : ℝ≥0∞)) * mass a := by gcongr
    _ = 3 * (((fiberSize a - 1 : ℕ) : ℝ≥0∞) /
        fiberSize a * mass a) := by
      simp only [n]
      ac_rfl

/-! ## Quantitative reduction target -/

/-- The exact right-hand side of the source reduction, instantiated with the concrete adversaries
above. `SM_DT_DSPR_SourceFinalValidity.Advantage` already contains the truncated
`DSPR success - SPprob` subtraction. -/
noncomputable def TCRDSPRBound [Fintype M] [Inhabited M] [DecidableEq Tweak]
    [DecidableEq M] [DecidableEq Y] {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) : ℝ≥0∞ :=
  SM_DT_DSPR_SourceFinalValidity.Advantage (toDSPR adv) +
    3 * SM_DT_TCR_SourceFinalValidity.Advantage (toTCR adv)

/-- Evidence interface for the program-level probability decomposition by the selected image's
fiber cardinality. `singleMass` is the successful OpenPRE mass on fibers of size one.
`multipleMass k` is the mass on fibers of size `k + 2`, aggregating over all selected target
indices.

This structure is deliberately a proof obligation, not a theorem supplied by this file. Its two
equations and one inequality are the substantive probabilistic coupling still to be constructed
from the executable games; none assumes the desired final reduction bound. -/
structure CountingInterface [Fintype M] [Inhabited M] [SampleableType M]
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) where
  /-- The source counting argument uses full uniform sampling of the finite input space. -/
  uniformInputs : prob.HasUniformInputs
  /-- Successful mass whose selected image has exactly one preimage. -/
  singleMass : ℝ≥0∞
  /-- Successful masses for fiber cardinalities `2, …, Fintype.card M`. -/
  multipleMass : Fin (Fintype.card M - 1) → ℝ≥0∞
  /-- Decomposition of OpenPRE success by fiber cardinality. -/
  openPRE_decomposition :
    Advantage adv = singleMass + ∑ k, multipleMass k
  /-- Exact DSPR/SPprob truncated gap: singleton mass minus the reciprocal mass of larger
  fibers. -/
  dspr_decomposition :
    SM_DT_DSPR_SourceFinalValidity.Advantage (toDSPR adv) =
      singleMass - reciprocalMass (fun k => k.val + 2) multipleMass
  /-- TCR success lower-bounds the collision-weighted mass of fibers of size at least two. -/
  tcr_strata_le :
    collisionMass (fun k => k.val + 2) multipleMass ≤
      SM_DT_TCR_SourceFinalValidity.Advantage (toTCR adv)

/-- Once the named fiber-counting/coupling lemma is supplied, the full quantitative reduction is
pure ENNReal algebra. This is the exact `OpenPRE ≤ DSPR + 3·TCR` theorem interface. -/
theorem advantage_le_tcrDsprBound [Fintype M] [Inhabited M] [SampleableType M]
    [DecidableEq Tweak] [DecidableEq M] [DecidableEq Y]
    {prob : Problem ι PkSeed Tweak M Y}
    (adv : Adversary prob) (hcount : CountingInterface adv) :
    Advantage adv ≤ TCRDSPRBound adv := by
  let reciprocal := reciprocalMass
    (fun k : Fin (Fintype.card M - 1) => k.val + 2) hcount.multipleMass
  let collision := collisionMass
    (fun k : Fin (Fintype.card M - 1) => k.val + 2) hcount.multipleMass
  have hsingle : hcount.singleMass ≤
      SM_DT_DSPR_SourceFinalValidity.Advantage (toDSPR adv) + reciprocal := by
    rw [hcount.dspr_decomposition]
    exact le_tsub_add
  have hmultiple : (∑ k, hcount.multipleMass k) + reciprocal ≤ 3 * collision := by
    exact openPRE_multipleMass_add_reciprocal_le_three_collision _ _ (fun _ => by omega)
  have hcollision : 3 * collision ≤
      3 * SM_DT_TCR_SourceFinalValidity.Advantage (toTCR adv) := by
    gcongr
    exact hcount.tcr_strata_le
  rw [hcount.openPRE_decomposition]
  calc
    hcount.singleMass + ∑ k, hcount.multipleMass k ≤
        (SM_DT_DSPR_SourceFinalValidity.Advantage (toDSPR adv) + reciprocal) +
          ∑ k, hcount.multipleMass k := by gcongr
    _ = SM_DT_DSPR_SourceFinalValidity.Advantage (toDSPR adv) +
        ((∑ k, hcount.multipleMass k) + reciprocal) := by ac_rfl
    _ ≤ SM_DT_DSPR_SourceFinalValidity.Advantage (toDSPR adv) + 3 * collision := by gcongr
    _ ≤ SM_DT_DSPR_SourceFinalValidity.Advantage (toDSPR adv) +
        3 * SM_DT_TCR_SourceFinalValidity.Advantage (toTCR adv) := by gcongr

end SM_DT_OpenPRE_SourceFinalValidity

end TweakableHash
