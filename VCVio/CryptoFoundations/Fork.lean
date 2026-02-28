/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.QueryTracking.SeededOracle
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.Coercions.Add
import ToMathlib.Data.ENNReal.SumSquares

/-!
# Forking Lemma

The forking lemma is a key tool in provable security. Given an adversary that succeeds with
some probability, the "fork" runs it twice with shared randomness up to a chosen query index,
then re-samples one oracle response, bounding the probability that both runs succeed.

## API changes from old version

- `OracleComp` no longer has `Alternative`, so `guard`/`getM` are unavailable.
  `fork` now returns `OracleComp spec (Option (α × α))` with explicit matching.
- `seededOracle` uses `StateT` (not `ReaderT`), so `.run' seed` discards the final state.
- Old probability notation `[= x | ...]` → `Pr[= x | ...]`, `[⊥ | ...]` → `Pr[= none | ...]`.
- `generateSeed` returns `ProbComp`, lifted via `liftComp`.
-/

open OracleSpec OracleComp ENNReal Function Finset

namespace OracleComp

variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
  [∀ i, SampleableType (spec.Range i)] [spec.DecidableEq] [unifSpec ⊂ₒ spec]
  {α β γ : Type}

/-- Bundles the inputs to the forking lemma. -/
structure forkInput (spec : OracleSpec ι) (α : Type) where
  main : OracleComp spec α
  queryBound : ι → ℕ
  js : List ι

/-- The forking operation: run `main` with a random seed, then re-run it with the seed modified
at the `s`-th query to oracle `i` (where `s = cf x₁`), checking that both runs agree on `cf`.

Returns `none` (failure) when:
- `cf x₁ = none` (adversary did not choose a fork point)
- the re-sampled oracle response equals the original (no useful fork)
- `cf x₂ ≠ cf x₁` (the second run chose a different fork point) -/
def fork (main : OracleComp spec α)
    (qb : ι → ℕ) (js : List ι) (i : ι)
    (cf : α → Option (Fin (qb i + 1))) :
    OracleComp spec (Option (α × α)) := do
  let seed ← liftComp (generateSeed spec qb js) spec
  let x₁ ← (simulateQ seededOracle main).run' seed
  match cf x₁ with
  | none => return none
  | some s =>
    let u ← liftComp ($ᵗ spec.Range i) spec
    -- `seed' := take s ++ [u]` replaces the value at index `s` (0-based) when present.
    -- The collision guard must compare against that same index.
    if (seed i)[↑s]? = some u then
      return none
    else
      let seed' := (seed.takeAtIndex i ↑s).addValue i u
      let x₂ ← (simulateQ seededOracle main).run' seed'
      if cf x₂ = some s then
        return some (x₁, x₂)
      else
        return none

variable (main : OracleComp spec α) (qb : ι → ℕ)
    (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1)))
    [spec.Fintype] [spec.Inhabited] [OracleSpec.LawfulSubSpec unifSpec spec]

omit [spec.Fintype] [spec.Inhabited] [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- If `fork` succeeds (returns `some`), both runs agree on the fork index. -/
theorem cf_eq_of_mem_support_fork (x₁ x₂ : α)
    (h : some (x₁, x₂) ∈ support (fork main qb js i cf)) :
      ∃ s, cf x₁ = some s ∧ cf x₂ = some s := by
  simp only [fork] at h
  rw [mem_support_bind_iff] at h; obtain ⟨seed, -, h⟩ := h
  rw [mem_support_bind_iff] at h; obtain ⟨y₁, -, h⟩ := h
  rcases hcf : cf y₁ with _ | s
  · simp_all
  · simp only [hcf] at h
    rw [mem_support_bind_iff] at h; obtain ⟨u, -, h⟩ := h
    split_ifs at h with heq
    · simp_all
    · rw [mem_support_bind_iff] at h; obtain ⟨y₂, -, h⟩ := h
      split_ifs at h with hcf₂
      · rw [mem_support_pure_iff] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨s, hcf, hcf₂⟩
      · simp_all

omit [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- On `fork` support, first-projection success equals old pair-style success event. -/
private lemma probEvent_fork_fst_eq_probEvent_pair (s : Fin (qb i + 1)) :
    Pr[fun r => r.map (cf ∘ Prod.fst) = some (some s) | fork main qb js i cf] =
      Pr[fun r => r.map (Prod.map cf cf) = some (some s, some s) | fork main qb js i cf] := by
  refine probEvent_ext ?_
  intro r hr
  rcases r with _ | ⟨x₁, x₂⟩
  · simp
  · have hmem : some (x₁, x₂) ∈ support (fork main qb js i cf) := by
      simpa using hr
    rcases cf_eq_of_mem_support_fork (main := main) (qb := qb) (js := js) (i := i) (cf := cf)
      x₁ x₂ hmem with ⟨t, h₁, h₂⟩
    simp [h₁, h₂]

omit [spec.DecidableEq] in
private lemma probEvent_uniform_eq_seedSlot_le_inv (s : Fin (qb i + 1))
    (seed : QuerySeed spec) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[fun u : spec.Range i => (seed i)[↑s]? = some u | liftComp ($ᵗ spec.Range i) spec] ≤ h⁻¹ := by
  simp only
  by_cases hnone : (seed i)[↑s]? = none
  · simp [hnone]
  · rcases Option.ne_none_iff_exists'.mp hnone with ⟨u₀, hu₀⟩
    rw [hu₀]
    have : Pr[fun u : spec.Range i => (some u₀ : Option (spec.Range i)) = some u |
          liftComp ($ᵗ spec.Range i) spec] =
        Pr[fun u : spec.Range i => u₀ = u | liftComp ($ᵗ spec.Range i) spec] := by
      congr 1; ext; simp
    rw [this]
    exact le_of_eq (seededOracle.probEvent_liftComp_uniformSample_eq_of_eq u₀)

omit [spec.DecidableEq] in
private lemma probEvent_uniform_eq_seedSlot_eq_inv_of_get (s : Fin (qb i + 1))
    (seed : QuerySeed spec) {u₀ : spec.Range i}
    (hu₀ : (seed i)[↑s]? = some u₀) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[fun u : spec.Range i => (seed i)[↑s]? = some u | liftComp ($ᵗ spec.Range i) spec] = h⁻¹ := by
  simp only
  rw [hu₀]
  have : Pr[fun u : spec.Range i => (some u₀ : Option (spec.Range i)) = some u |
        liftComp ($ᵗ spec.Range i) spec] =
      Pr[fun u : spec.Range i => u₀ = u | liftComp ($ᵗ spec.Range i) spec] := by
    congr 1; ext; simp
  rw [this]
  exact seededOracle.probEvent_liftComp_uniformSample_eq_of_eq u₀

private lemma probOutput_collision_given_seed_le (s : Fin (qb i + 1))
    (seed : QuerySeed spec) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[= (some s : Option (Fin (qb i + 1))) | do
      let x₁ ← (simulateQ seededOracle main).run' seed
      let u ← liftComp ($ᵗ spec.Range i) spec
      if (seed i)[↑s]? = some u then return cf x₁ else return none] ≤
    Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> (simulateQ seededOracle main).run' seed] / h := by
  simp only
  rw [probOutput_bind_eq_tsum, probOutput_map_eq_tsum]
  simp_rw [div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right]
  refine ENNReal.tsum_le_tsum fun x₁ => ?_
  have hterm :
      Pr[= (some s : Option (Fin (qb i + 1))) | do
        let u ← liftComp ($ᵗ spec.Range i) spec
        if (seed i)[↑s]? = some u then return cf x₁ else return none] ≤
      Pr[= (some s : Option (Fin (qb i + 1))) |
        (pure (cf x₁) : OracleComp spec (Option (Fin (qb i + 1))))] *
        (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹ := by
    by_cases hcf : cf x₁ = some s
    · have hslot :=
        probEvent_uniform_eq_seedSlot_le_inv (s := s) (seed := seed)
      calc
        Pr[= (some s : Option (Fin (qb i + 1))) | do
            let u ← liftComp ($ᵗ spec.Range i) spec
            if (seed i)[↑s]? = some u then return cf x₁ else return none]
          = Pr[fun u : spec.Range i => (seed i)[↑s]? = some u | liftComp ($ᵗ spec.Range i) spec] := by
              rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite]
              refine tsum_congr fun u => ?_
              by_cases hu : (seed i)[↑s]? = some u <;> simp [hcf, hu]
        _ ≤ (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹ := by
              simpa using hslot
        _ = Pr[= (some s : Option (Fin (qb i + 1))) |
              (pure (cf x₁) : OracleComp spec (Option (Fin (qb i + 1))))] *
              (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹ := by
              simp [hcf]
        _ ≤ Pr[= (some s : Option (Fin (qb i + 1))) |
              (pure (cf x₁) : OracleComp spec (Option (Fin (qb i + 1))))] *
              (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹ := le_rfl
    · have hcf' : (some s : Option (Fin (qb i + 1))) ≠ cf x₁ := by
        simpa [eq_comm] using hcf
      calc
        Pr[= (some s : Option (Fin (qb i + 1))) | do
            let u ← liftComp ($ᵗ spec.Range i) spec
            if (seed i)[↑s]? = some u then return cf x₁ else return none] = 0 := by
              rw [probOutput_bind_eq_tsum]
              refine ENNReal.tsum_eq_zero.mpr fun u => ?_
              by_cases hu : (seed i)[↑s]? = some u <;> simp [hu, hcf']
        _ = Pr[= (some s : Option (Fin (qb i + 1))) |
              (pure (cf x₁) : OracleComp spec (Option (Fin (qb i + 1))))] *
              (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹ := by
              simp [hcf']
        _ ≤ Pr[= (some s : Option (Fin (qb i + 1))) |
              (pure (cf x₁) : OracleComp spec (Option (Fin (qb i + 1))))] *
              (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹ := le_rfl
  calc
    Pr[= x₁ | (simulateQ seededOracle main).run' seed] *
      Pr[= (some s : Option (Fin (qb i + 1))) | do
        let u ← liftComp ($ᵗ spec.Range i) spec
        if (seed i)[↑s]? = some u then return cf x₁ else return none]
      ≤ Pr[= x₁ | (simulateQ seededOracle main).run' seed] *
          (Pr[= (some s : Option (Fin (qb i + 1))) |
            (pure (cf x₁) : OracleComp spec (Option (Fin (qb i + 1))))] *
            (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹) := by
          exact mul_le_mul' le_rfl hterm
    _ = Pr[= x₁ | (simulateQ seededOracle main).run' seed] *
          Pr[= (some s : Option (Fin (qb i + 1))) |
            (pure (cf x₁) : OracleComp spec (Option (Fin (qb i + 1))))] *
          (↑(Fintype.card (spec.Range i)) : ℝ≥0∞)⁻¹ := by
          rw [mul_assoc]

set_option maxHeartbeats 300000 in
private lemma probOutput_collision_le_main_div (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[= (some s : Option (Fin (qb i + 1))) | do
      let seed ← liftComp (generateSeed spec qb js) spec
      let x₁ ← (simulateQ seededOracle main).run' seed
      let u ← liftComp ($ᵗ spec.Range i) spec
      if (seed i)[↑s]? = some u then return cf x₁ else return none] ≤
    Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] / h := by
  simp only
  rw [probOutput_bind_eq_tsum]
  calc
    ∑' seed : QuerySeed spec,
      Pr[= seed | liftComp (generateSeed spec qb js) spec] *
        Pr[= (some s : Option (Fin (qb i + 1))) | do
          let x₁ ← (simulateQ seededOracle main).run' seed
          let u ← liftComp ($ᵗ spec.Range i) spec
          if (seed i)[↑s]? = some u then return cf x₁ else return none]
      ≤ ∑' seed : QuerySeed spec,
          Pr[= seed | liftComp (generateSeed spec qb js) spec] *
            (Pr[= (some s : Option (Fin (qb i + 1))) |
              cf <$> (simulateQ seededOracle main).run' seed] /
            ↑(Fintype.card (spec.Range i))) := by
          refine ENNReal.tsum_le_tsum fun seed => ?_
          exact mul_le_mul' le_rfl
            (probOutput_collision_given_seed_le
              (main := main) (qb := qb) (i := i) (cf := cf) (s := s) (seed := seed))
    _ = (∑' seed : QuerySeed spec,
          Pr[= seed | liftComp (generateSeed spec qb js) spec] *
            Pr[= (some s : Option (Fin (qb i + 1))) |
              cf <$> (simulateQ seededOracle main).run' seed]) /
            ↑(Fintype.card (spec.Range i)) := by
          simp_rw [div_eq_mul_inv]
          rw [← ENNReal.tsum_mul_right]
          refine tsum_congr fun seed => ?_
          rw [mul_assoc]
    _ = Pr[= (some s : Option (Fin (qb i + 1))) | do
          let seed ← liftComp (generateSeed spec qb js) spec
          cf <$> (simulateQ seededOracle main).run' seed] /
            ↑(Fintype.card (spec.Range i)) := by
          rw [probOutput_bind_eq_tsum]
    _ = Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] /
            ↑(Fintype.card (spec.Range i)) := by
          simpa using congrArg
            (fun p => p / (↑(Fintype.card (spec.Range i)) : ℝ≥0∞))
            (seededOracle.probOutput_generateSeed_bind_map_simulateQ
              (qc := qb) (js := js) (oa := main) (f := cf)
              (y := (some s : Option (Fin (qb i + 1)))))

set_option maxHeartbeats 800000 in
/-- Key bound of the forking lemma: the probability that both runs succeed with fork point `s`
is at least `Pr[cf(main) = s]² - Pr[cf(main) = s] / |Range i|`. -/
theorem le_probOutput_fork (s : Fin (qb i + 1)) :
    let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
    Pr[= s | cf <$> main] ^ 2 - Pr[= s | cf <$> main] / h
      ≤ Pr[fun r => r.map (cf ∘ Prod.fst) = some (some s) |
            fork main qb js i cf] := by
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  -- Reduce to the old pair-style success event on `fork` outputs.
  rw [probEvent_fork_fst_eq_probEvent_pair (main := main) (qb := qb) (js := js) (i := i) (cf := cf)]
  let f : Option (α × α) → Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) :=
    fun r => r.map (Prod.map cf cf)
  let z : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) := some (some s, some s)
  have hRhsEq :
      Pr[fun r => r.map (Prod.map cf cf) = some (some s, some s) | fork main qb js i cf] =
      Pr[= z | f <$> fork main qb js i cf] := by
    calc
      Pr[fun r => r.map (Prod.map cf cf) = some (some s, some s) | fork main qb js i cf]
        = Pr[fun r => f r = z | fork main qb js i cf] := by
            simp [f, z]
      _ = Pr[fun x => x = z | f <$> fork main qb js i cf] := by
            simpa [Function.comp] using
              (probEvent_map
                (mx := fork main qb js i cf)
                (f := f)
                (q := fun x : Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1))) => x = z)).symm
      _ = Pr[= z | f <$> fork main qb js i cf] := by
            simp [probEvent_eq_eq_probOutput (mx := f <$> fork main qb js i cf) (x := z)]
  rw [hRhsEq]
  -- Guard-collision branch contributes at most `Pr[cf(main)=s] / h`.
  have hCollision :
      Pr[= (some s : Option (Fin (qb i + 1))) | do
        let seed ← liftComp (generateSeed spec qb js) spec
        let x₁ ← (simulateQ seededOracle main).run' seed
        let u ← liftComp ($ᵗ spec.Range i) spec
        if (seed i)[↑s]? = some u then return cf x₁ else return none]
      ≤ Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] / h := by
    simpa [h] using
      (probOutput_collision_le_main_div
        (main := main) (qb := qb) (js := js) (i := i) (cf := cf) s)
  have hLhsCollision :
      Pr[= s | cf <$> main] ^ 2 - Pr[= s | cf <$> main] / h ≤
      Pr[= s | cf <$> main] ^ 2 -
        Pr[= (some s : Option (Fin (qb i + 1))) | do
          let seed ← liftComp (generateSeed spec qb js) spec
          let x₁ ← (simulateQ seededOracle main).run' seed
          let u ← liftComp ($ᵗ spec.Range i) spec
          if (seed i)[↑s]? = some u then return cf x₁ else return none] := by
    have hCollision' :
        Pr[= (some s : Option (Fin (qb i + 1))) | do
          let seed ← liftComp (generateSeed spec qb js) spec
          let x₁ ← (simulateQ seededOracle main).run' seed
          let u ← liftComp ($ᵗ spec.Range i) spec
          if (seed i)[↑s]? = some u then return cf x₁ else return none]
        ≤ Pr[= s | cf <$> main] / h := by
      simpa using hCollision
    exact tsub_le_tsub_left hCollision' (Pr[= s | cf <$> main] ^ 2)
  refine le_trans hLhsCollision ?_
  let collisionComp : OracleComp spec (Option (Fin (qb i + 1))) := do
    let seed ← liftComp (generateSeed spec qb js) spec
    let x₁ ← (simulateQ seededOracle main).run' seed
    let u ← liftComp ($ᵗ spec.Range i) spec
    if (seed i)[↑s]? = some u then return cf x₁ else return none
  let noGuardComp :
      OracleComp spec (Option (Option (Fin (qb i + 1)) × Option (Fin (qb i + 1)))) := do
    let seed ← liftComp (generateSeed spec qb js) spec
    let x₁ ← (simulateQ seededOracle main).run' seed
    let u ← liftComp ($ᵗ spec.Range i) spec
    let seed' := (seed.takeAtIndex i ↑s).addValue i u
    let x₂ ← (simulateQ seededOracle main).run' seed'
    return some (cf x₁, cf x₂)
  change Pr[= s | cf <$> main] ^ 2 - Pr[= (some s : Option (Fin (qb i + 1))) | collisionComp] ≤
      Pr[= z | f <$> fork main qb js i cf]
  have hNoGuardLeAdd :
      Pr[= z | noGuardComp] ≤
        Pr[= z | f <$> fork main qb js i cf] +
          Pr[= (some s : Option (Fin (qb i + 1))) | collisionComp] := by
    simp only [noGuardComp, collisionComp]
    simp [fork, f, z]
    refine (probOutput_bind_congr_le_add
      (mx := (liftComp (generateSeed spec qb js) spec : OracleComp spec (QuerySeed spec)))
      (y := z) (z₁ := z) (z₂ := (some s : Option (Fin (qb i + 1))))) ?_
    intro seed hseed
    stop
    refine (probOutput_bind_congr_le_add
      (mx := (simulateQ seededOracle main).run' seed)
      (y := z) (z₁ := z) (z₂ := (some s : Option (Fin (qb i + 1))))) ?_
    intro x₁ hx₁
    by_cases hcfx₁ : cf x₁ = some s
    · simp [hcfx₁]
      refine (probOutput_bind_congr_le_add
        (mx := (liftComp ($ᵗ spec.Range i) spec : OracleComp spec (spec.Range i)))
        (y := z) (z₁ := z) (z₂ := (some s : Option (Fin (qb i + 1))))) ?_
      intro u hu
      by_cases hu' : (seed i)[↑s]? = some u
      · simp [hu']
        exact probOutput_le_one
      · simp [hu']
    · have hcfx₁' : (some s : Option (Fin (qb i + 1))) ≠ cf x₁ := by
        simpa [eq_comm] using hcfx₁
      simp [hcfx₁, hcfx₁']
  have hNoGuardMinusLeRhs :
      Pr[= z | noGuardComp] - Pr[= (some s : Option (Fin (qb i + 1))) | collisionComp] ≤
        Pr[= z | f <$> fork main qb js i cf] := by
    exact (tsub_le_iff_right).2 hNoGuardLeAdd
  have hNoGuardGeSquare :
      Pr[= s | cf <$> main] ^ 2 ≤ Pr[= z | noGuardComp] := by
    -- Remaining core: seed-factorization and weighted-square lower bound.
    sorry
  exact le_trans
    (tsub_le_tsub_right hNoGuardGeSquare (Pr[= (some s : Option (Fin (qb i + 1))) | collisionComp]))
    hNoGuardMinusLeRhs

omit [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- Sum of disjoint fork-success events is at most the total `some` probability. -/
private lemma sum_probEvent_fork_le_tsum_some :
    ∑ s : Fin (qb i + 1),
      Pr[fun r => r.map (cf ∘ Prod.fst) = some (some s) | fork main qb js i cf]
    ≤ ∑' (p : α × α), Pr[= some p | fork main qb js i cf] := by
  classical
  simp_rw [probEvent_eq_tsum_ite]
  have hsplit : ∀ s : Fin (qb i + 1),
      (∑' (r : Option (α × α)),
        if r.map (cf ∘ Prod.fst) = some (some s) then Pr[= r | fork main qb js i cf] else 0)
      = ∑' (p : α × α), if cf p.1 = some s then
          Pr[= some p | fork main qb js i cf] else 0 := by
    intro s
    have h := tsum_option (fun r : Option (α × α) =>
      if r.map (cf ∘ Prod.fst) = some (some s) then
        Pr[= r | fork main qb js i cf] else 0) ENNReal.summable
    simp only [Option.map, comp_apply, reduceCtorEq, ite_false, zero_add,
      Option.some.injEq] at h
    exact h
  simp_rw [hsplit]
  rw [← tsum_fintype (L := .unconditional _), ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum fun p => ?_
  rw [tsum_fintype (L := .unconditional _)]
  rcases hcf : cf p.1 with _ | s₀
  · simp
  · rw [Finset.sum_eq_single s₀ (by intro b _ hb; simp [Ne.symm hb]) (by simp)]
    simp

omit [DecidableEq ι] [(i : ι) → SampleableType (spec.Range i)]
  [spec.DecidableEq] [unifSpec ⊂ₒ spec] [OracleSpec.LawfulSubSpec unifSpec spec] in
/-- The acceptance probability `∑ Pr[cf(main) = some s]` is at most 1. -/
private lemma sum_probOutput_cf_le_one :
    ∑ s : Fin (qb i + 1), Pr[= (some s : Option (Fin (qb i + 1))) | cf <$> main] ≤ 1 := by
  calc ∑ s, Pr[= (some s : Option _) | cf <$> main]
    _ ≤ ∑' (x : Option (Fin (qb i + 1))), Pr[= x | cf <$> main] := by
        rw [← tsum_fintype (L := .unconditional _)]
        have h := tsum_option (fun x : Option (Fin (qb i + 1)) =>
          Pr[= x | cf <$> main]) ENNReal.summable
        rw [h]; exact le_add_self
    _ ≤ 1 := tsum_probOutput_le_one

/-- Main forking lemma: the failure probability is bounded by `1 - acc * (acc / q - 1/h)`. -/
theorem probOutput_none_fork_le :
    let acc : ℝ≥0∞ := ∑ s, Pr[= some s | cf <$> main]
    let h : ℝ≥0∞ := Fintype.card (spec.Range i)
    let q := qb i + 1
    Pr[= none | fork main qb js i cf] ≤ 1 - acc * (acc / q - h⁻¹) := by
  simp only
  set ps : Fin (qb i + 1) → ℝ≥0∞ := fun s => Pr[= (some s : Option _) | cf <$> main]
  set acc := ∑ s, ps s
  set h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
  have hacc_ne_top : acc ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (sum_probOutput_cf_le_one main qb i cf)
  have htotal := probOutput_none_add_tsum_some (mx := fork main qb js i cf)
  rw [HasEvalPMF.probFailure_eq_zero, tsub_zero] at htotal
  have hne_top : (∑' p, Pr[= some p | fork main qb js i cf]) ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (htotal ▸ le_add_self)
  have hPr_eq : Pr[= none | fork main qb js i cf] =
      1 - ∑' p, Pr[= some p | fork main qb js i cf] :=
    ENNReal.eq_sub_of_add_eq hne_top htotal
  calc Pr[= none | fork main qb js i cf]
    _ = 1 - ∑' p, Pr[= some p | fork main qb js i cf] := hPr_eq
    _ ≤ 1 - ∑ s, Pr[fun r => r.map (cf ∘ Prod.fst) = some (some s) |
            fork main qb js i cf] :=
        tsub_le_tsub_left (sum_probEvent_fork_le_tsum_some main qb js i cf) 1
    _ ≤ 1 - ∑ s, (ps s ^ 2 - ps s / h) :=
        tsub_le_tsub_left (Finset.sum_le_sum fun s _ =>
          le_probOutput_fork main qb js i cf s) 1
    _ ≤ 1 - acc * (acc / ↑(qb i + 1) - h⁻¹) := by
        apply tsub_le_tsub_left _ 1
        have hcs := ENNReal.sq_sum_le_card_mul_sum_sq
          (Finset.univ : Finset (Fin (qb i + 1))) ps
        simp only [Finset.card_univ, Fintype.card_fin] at hcs
        calc acc * (acc / ↑(qb i + 1) - h⁻¹)
          _ = acc * (acc / ↑(qb i + 1)) - acc * h⁻¹ :=
              ENNReal.mul_sub (fun _ _ => hacc_ne_top)
          _ = acc ^ 2 / ↑(qb i + 1) - acc / h := by
              rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, sq, div_eq_mul_inv]
          _ ≤ (∑ s, ps s ^ 2) - acc / h := by
              gcongr; rw [div_eq_mul_inv]
              have hn : ((qb i + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
              calc acc ^ 2 * (↑(qb i + 1))⁻¹
                  _ ≤ (↑(qb i + 1) * ∑ s, ps s ^ 2) * (↑(qb i + 1))⁻¹ := by gcongr
                  _ = ∑ s, ps s ^ 2 := by
                      rw [mul_assoc, mul_comm (∑ s, ps s ^ 2) _, ← mul_assoc,
                        ENNReal.mul_inv_cancel hn (by simp), one_mul]
          _ ≤ (∑ s, ps s ^ 2) - ∑ s, ps s / h := by
              gcongr; simp_rw [div_eq_mul_inv]; rw [← Finset.sum_mul]
          _ ≤ ∑ s, (ps s ^ 2 - ps s / h) := by
              rw [tsub_le_iff_right]
              calc ∑ s, ps s ^ 2
                ≤ ∑ s, ((ps s ^ 2 - ps s / h) + ps s / h) :=
                    Finset.sum_le_sum fun s _ => le_tsub_add
                _ = ∑ s, (ps s ^ 2 - ps s / h) + ∑ s, ps s / h :=
                    Finset.sum_add_distrib

end OracleComp

/-! ## Old commented code (for reference)

-- open OracleSpec OracleComp Option ENNReal Function

-- section scratch

-- universe u v w

-- variable {ι : Type u} {spec : OracleSpec ι} {α β γ δ : Type v}

-- lemma probOutput_prod_mk_seq_map_eq_mul [spec.FiniteRange] (oa : OracleComp spec α)
--     (ob : OracleComp spec β) (z : α × β) :
--     [= z | ((·, ·) <$> oa <*> ob : OracleComp spec (α × β))] = [= z.1 | oa] * [= z.2 | ob] := by
--     obtain ⟨fst, snd⟩ := z
--     simp_all only [probOutput_seq_map_prod_mk_eq_mul]

-- lemma probOutput_prod_mk_seq_map_eq_mul' [spec.FiniteRange] (oa : OracleComp spec α)
--     (ob : OracleComp spec β) (x : α) (y : β) :
--     [= (x, y) | ((·, ·) <$> oa <*> ob : OracleComp spec (α × β))] = [= x | oa] * [= y | ob] := by
--     simp_all only [probOutput_seq_map_prod_mk_eq_mul]

-- lemma probOutput_prod_mk_apply_seq_map_eq_mul [spec.FiniteRange] (oa : OracleComp spec α)
--     (ob : OracleComp spec β)
--     (f : α → γ) (g : β → δ) (z : γ × δ) :
--     [= z | (f ·, g ·) <$> oa <*> ob] = [= z.1 | f <$> oa] * [= z.2 | g <$> ob] := by
--   sorry

-- lemma probOutput_prod_mk_apply_seq_map_eq_mul' [spec.FiniteRange] (oa : OracleComp spec α)
--     (ob : OracleComp spec β)
--     (f : α → γ) (g : β → δ) (x : γ) (y : δ) :
--     [= (x, y) | (f ·, g ·) <$> oa <*> ob] = [= x | f <$> oa] * [= y | g <$> ob] := by
--     rw [@probOutput_prod_mk_apply_seq_map_eq_mul]

-- lemma probOutput_bind_bind_prod_mk_eq_mul [spec.FiniteRange] (oa : OracleComp spec α)
--     (ob : OracleComp spec β) (f : α → γ) (g : β → δ) (z : γ × δ) :
--     [= z | do let x ← oa; let y ← ob; return (f x, g y)] =
--       [= z.1 | f <$> oa] * [= z.2 | g <$> ob] := by
--   sorry

-- @[simp]
-- lemma probOutput_bind_bind_prod_mk_eq_mul' [spec.FiniteRange] (oa : OracleComp spec α)
--     (ob : OracleComp spec β) (f : α → γ) (g : β → δ) (x : γ) (y : δ) :
--     [= (x, y) | do let x ← oa; let y ← ob; return (f x, g y)] =
--       [= x | f <$> oa] * [= y | g <$> ob] := by
--       rw [@probOutput_bind_bind_prod_mk_eq_mul]

-- lemma map_ite (oa₁ oa₂ : OracleComp spec α) (f : α → β) (p : Prop) [Decidable p] :
--     f <$> (if p then oa₁ else oa₂) = if p then (f <$> oa₁) else (f <$> oa₂) := by
--     rw [← @apply_ite]

-- lemma probFailure_bind_eq_sum_probFailure [spec.FiniteRange] (oa : OracleComp spec α)
--     {ob : α → OracleComp spec β} {σ : Type u} {s : Finset σ}
--     {oc : σ → α → OracleComp spec γ} :
--     [⊥ | oa >>= ob] = ∑ x ∈ s, [⊥ | oa >>= oc x] := by
--   sorry

-- lemma probOutput_map_eq_probEvent [spec.FiniteRange]
--     (oa : OracleComp spec α) (f : α → β) (y : β) :
--     [= y | f <$> oa] = [fun x => f x = y | oa] := by
--   rw [← probEvent_eq_eq_probOutput, probEvent_map, Function.comp_def]

-- @[simp]
-- lemma probOutput_prod_mk_fst_map [spec.FiniteRange] (oa : OracleComp spec α) (y : β) (z : α × β) :
--     [= z | (·, y) <$> oa] = [= z.1 | oa] * [= z.2 | (pure y : OracleComp spec β)] := by
--   sorry

-- @[simp]
-- lemma probOutput_prod_mk_snd_map [spec.FiniteRange] (ob : OracleComp spec β) (x : α) (z : α × β) :
--     [= z | (x, ·) <$> ob] = [= z.1 | (pure x : OracleComp spec α)] * [= z.2 | ob] := by
--   sorry

-- @[simp]
-- lemma probOutput_prod_mk_fst_map' [spec.FiniteRange] (oa : OracleComp spec α)
--     (f : α → γ) (y : β) (z : γ × β) :
--     [= z | (f ·, y) <$> oa] = [= z.1 | f <$> oa] * [= z.2 | (pure y : OracleComp spec β)] := by
--   sorry

-- @[simp]
-- lemma probOutput_prod_mk_snd_map' [spec.FiniteRange] (ob : OracleComp spec β)
--     (f : β → γ) (x : α) (z : α × γ) :
--     [= z | (x, f ·) <$> ob] = [= z.1 | (pure x : OracleComp spec α)] * [= z.2 | f <$> ob] := by
--   sorry

-- lemma probOutput_bind_ite_failure_eq_tsum [spec.FiniteRange] [DecidableEq β]
--     (oa : OracleComp spec α) (f : α → β) (p : α → Prop) [DecidablePred p] (y : β) :
--     [= y | oa >>= fun x => if p x then pure (f x) else failure] =
--       ∑' x : α, if p x ∧ y = f x then [= x | oa] else 0 := by
--   rw [probOutput_bind_eq_tsum]
--   simp [probEvent_eq_tsum_ite, ite_and]

-- -- lemma probOutput_eq

-- end scratch

-- namespace OracleComp

-- variable {ι : Type} [DecidableEq ι] {spec : OracleSpec ι}
--   [∀ i, SampleableType (spec.Range i)] [spec.DecidableEq] [unifSpec ⊂ₒ spec]
--   {α β γ : Type}

-- structure forkInput (spec : OracleSpec ι) (α : Type) where
--   /-- The main program to fork execution of -/
--   main : OracleComp spec α
--   /-- A bound on the number of queries the adversary makes-/
--   queryBound : ι → ℕ
--   /-- List of oracles that are queried during computation (used to order seed generation). -/
--   js : List ι

-- /-- Version of `fork` that doesn't choose `s` ahead of time.
-- Should give better concrete bounds. -/
-- def fork (main : OracleComp spec α)
--     (qb : ι → ℕ) (js : List ι) (i : ι)
--     (cf : α → Option (Fin (qb i + 1))) :
--     OracleComp spec (α × α) := do
--   let seed ← generateSeed spec qb js
--   let x₁ ← (simulateQ seededOracle main).run seed
--   let s : Fin (qb i + 1) ← (cf x₁).getM
--   let u ←$ᵗ spec.Range i -- Choose new output for query
--   guard ((seed i)[s + 1]? ≠ some u) -- Didn't pick the same output
--   let seed' := (seed.takeAtIndex i s).addValue i u
--   let x₂ ← (simulateQ seededOracle main).run seed'
--   guard (cf x₂ = some s) -- Choose the same index on this run
--   return (x₁, x₂)

-- variable (main : OracleComp spec α) (qb : ι → ℕ)
--     (js : List ι) (i : ι) (cf : α → Option (Fin (qb i + 1))) [spec.FiniteRange]

-- @[simp] lemma support_map_prod_map_fork : (Prod.map cf cf <$> main.fork qb js i cf).support =
--     (fun s => (s, s)) '' (cf <$> main).support := by
--   sorry

-- @[simp] lemma finSupport_map_prod_map_fork : (Prod.map cf cf <$> main.fork qb js i cf).finSupport =
--     (cf <$> main).finSupport.image fun s => (s, s) := by
--   sorry

-- lemma apply_eq_apply_of_mem_support_fork (x₁ x₂ : α)
--     (h : (x₁, x₂) ∈ (fork main qb js i cf).support) : cf x₁ = cf x₂ := by
--   sorry

-- @[simp] lemma probOutput_none_map_fork_left (s : Option (Fin (qb i + 1))) :
--     [= (none, s) | Prod.map cf cf <$> main.fork qb js i cf] = 0 := by
--   sorry

-- @[simp] lemma probOutput_none_map_fork_right (s : Option (Fin (qb i + 1))) :
--     [= (s, none) | Prod.map cf cf <$> main.fork qb js i cf] = 0 := by
--   sorry

-- theorem exists_log_of_mem_support_fork (x₁ x₂ : α)
--     (h : (x₁, x₂) ∈ (fork main qb js i cf).support) :
--       ∃ s, cf x₁ = some s ∧ cf x₂ = some s ∧
--       ∃ log₁ : QueryLog spec, ∃ hcf₁ : ↑s < log₁.countQ i,
--       ∃ log₂ : QueryLog spec, ∃ hcf₁ : ↑s < log₂.countQ i,
--       (log₁.getQ i)[s].1 = (log₂.getQ i)[s].1 ∧
--       (log₁.getQ i)[s].2 ≠ (log₂.getQ i)[s].2 ∧
--       (x₁, log₁) ∈ (simulateQ loggingOracle main).run.support ∧
--       (x₂, log₂) ∈ (simulateQ loggingOracle main).run.support := by
--   sorry

-- lemma le_probOutput_fork (s : Fin (qb i + 1)) :
--     let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
--     [= s | cf <$> main] ^ 2 - [= s | cf <$> main] / h
--       ≤ [= (s, s) | Prod.map cf cf <$> fork main qb js i cf] :=
--   let h : ℝ≥0∞ := ↑(Fintype.card (spec.Range i))
--   have : DecidableEq α := Classical.decEq α -- :(
--   have : DecidableEq spec.QuerySeed := Classical.decEq _
--   calc [= (s, s) | Prod.map cf cf <$> fork main qb js i cf]
--     _ = [fun (x₁, x₂) => cf x₁ = s ∧ cf x₂ = s | fork main qb js i cf] := by {
--       simp [probOutput_map_eq_tsum_ite, probEvent_eq_tsum_ite,
--         Prod.eq_iff_fst_eq_snd_eq, @eq_comm _ (some s)]
--     }
--     _ = [= (s, s) | Prod.map cf cf <$> fork main qb js i cf] := by {
--         simp [probOutput_map_eq_probEvent, Prod.eq_iff_fst_eq_snd_eq]
--       }
--     _ = [= (s, s) | do
--           let seed ← liftM (generateSeed spec qb js)
--           let x₁ ← (simulateQ seededOracle main).run seed
--           let u ←$ᵗ spec.Range i
--           guard ((seed i)[s + 1]? ≠ u)
--           let seed' := (seed.takeAtIndex i s).addValue i u
--           let x₂ ← (simulateQ seededOracle main).run seed'
--           return (cf x₁, cf x₂)] := by {
--         simp [fork]
--         refine probOutput_bind_congr fun _ _ => ?_
--         refine probOutput_bind_congr fun x₁ hx₁ => ?_
--         by_cases hcfx₁ : cf x₁ = s
--         · simp [hcfx₁]
--           refine probOutput_bind_congr fun _ _ => ?_
--           refine probOutput_bind_congr fun () _ => ?_
--           simp [apply_ite]
--           rw [probOutput_bind_ite_failure_eq_tsum, probOutput_map_eq_tsum]
--           simp
--           refine tsum_congr fun x₂ => ?_
--           by_cases hcfx₂ : cf x₂ = s
--           · simp [hcfx₂]
--           · simp [hcfx₂, Ne.symm hcfx₂]
--         · refine (?_ : _ = (0 : ℝ≥0∞)).trans (?_ : (0 : ℝ≥0∞) = _)
--           · simp [hcfx₁]
--           · simp [hcfx₁]
--       }
--     _ ≥ [= (s, s) | do
--           let seed ← liftM (generateSeed spec qb js)
--           let x₁ ← (simulateQ seededOracle main).run seed
--           let u ←$ᵗ spec.Range i
--           let seed' := (seed.takeAtIndex i s).addValue i u
--           let x₂ ← (simulateQ seededOracle main).run seed'
--           return (cf x₁, cf x₂)] -
--         [= (s, s) | do
--           let seed ← liftM (generateSeed spec qb js)
--           let x₁ ← (simulateQ seededOracle main).run seed
--           let u ←$ᵗ spec.Range i
--           guard ((seed i)[s + 1]? = u)
--           let seed' := (seed.takeAtIndex i s).addValue i u
--           let x₂ ← (simulateQ seededOracle main).run seed'
--           return (cf x₁, cf x₂)] := by {
--         rw [ge_iff_le]
--         refine probOutput_bind_congr_sub_le fun seed hseed => ?_
--         refine probOutput_bind_congr_sub_le fun x₁ hx₁ => ?_
--         by_cases hcfx₁ : cf x₁ = s
--         · simp [hcfx₁]
--           refine probOutput_bind_congr_le_add fun u hu => ?_
--           by_cases hu' : (seed i)[(↑(s + 1) : ℕ)]? = some u
--           · simp [hu']
--           · simp [hu']
--         · refine le_of_eq_of_le ?_ zero_le'
--           refine tsub_eq_zero_of_le (le_of_eq_of_le ?_ zero_le')
--           simp [hcfx₁]
--       }
--     _ ≥ [= (s, s) | do
--           let seed ← liftM (generateSeed spec qb js)
--           let x₁ ← (simulateQ seededOracle main).run seed
--           let u ←$ᵗ spec.Range i
--           let seed' := (seed.takeAtIndex i s).addValue i u
--           let x₂ ← (simulateQ seededOracle main).run seed'
--           return (cf x₁, cf x₂)] -
--         [= s | do
--           let seed ← liftM (generateSeed spec qb js)
--           let x₁ ← (simulateQ seededOracle main).run seed
--           let u ←$ᵗ spec.Range i
--           guard ((seed i)[s + 1]? = u)
--           return (cf x₁)] := by {
--         refine tsub_le_tsub le_rfl ?_
--         refine probOutput_bind_mono fun seed hseed => ?_
--         refine probOutput_bind_mono fun x₁ hx₁ => ?_
--         refine probOutput_bind_mono fun u hu => ?_
--         refine probOutput_bind_mono fun () _ => ?_
--         by_cases hcfx₁ : some s = cf x₁
--         · simp [hcfx₁]
--         · simp [hcfx₁]
--       }
--     _ = [= (s, s) | do
--           let shared_seed ← liftM (generateSeed spec (Function.update qb i s) js)
--           let x₁ ← (simulateQ seededOracle main).run shared_seed
--           let x₂ ← (simulateQ seededOracle main).run shared_seed
--           return (cf x₁, cf x₂)] -
--         [= s | do
--           let seed ← liftM (generateSeed spec qb js)
--           let x₁ ← (simulateQ seededOracle main).run seed
--           return (cf x₁)] / h := by {
--         congr 1
--         · sorry
--         · refine probOutput_bind_congr_div_const fun seed hseed => ?_
--           have : (↑(s + 1) : ℕ) < (seed i).length := by sorry
--           let u : spec.Range i := ((seed i)[↑(s + 1)])
--           simp [probOutput_bind_eq_tsum, probOutput_map_eq_tsum, div_eq_mul_inv,
--             ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
--           refine tsum_congr fun x => ?_
--           refine (tsum_eq_single ((seed i)[(↑(s + 1) : ℕ)]) ?_).trans ?_
--           · intro u' hu'
--             rw [List.getElem?_eq_getElem this]
--             simp [hu'.symm]
--           · simp [h]
--       }
--     _ = ∑ seed ∈ (generateSeed spec (Function.update qb i s) js).finSupport,
--           ((generateSeed spec (Function.update qb i s) js).finSupport.card : ℝ≥0∞)⁻¹ * [= (s, s) | do
--             let x₁ ← (simulateQ seededOracle main).run seed
--             let x₂ ← (simulateQ seededOracle main).run seed
--             return (cf x₁, cf x₂)] - [= s | cf <$> main] / h := by {
--         congr 1
--         · rw [probOutput_bind_eq_sum_finSupport]
--           simp only [liftM_eq_liftComp, finSupport_liftComp, probOutput_liftComp, bind_pure_comp, h]
--           refine Finset.sum_congr rfl fun seed hseed => ?_
--           congr 1
--           apply probOutput_generateSeed'
--           refine mem_support_of_mem_finSupport _ hseed
--         · rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
--           refine (ENNReal.mul_right_inj (by simp [h]) (by simp [h])).2 ?_
--           simp
--       }
--     _ = ((generateSeed spec (Function.update qb i s) js).finSupport.card : ℝ≥0∞)⁻¹ *
--           ∑ seed ∈ (generateSeed spec (Function.update qb i s) js).finSupport,
--             [= s | cf <$> (simulateQ seededOracle main).run seed] ^ 2 - [= s | cf <$> main] / h := by {
--         rw [Finset.mul_sum]
--         congr 2
--         simp only [probOutput_bind_bind_prod_mk_eq_mul', pow_two]
--       }
--     _ ≥ ((generateSeed spec (Function.update qb i s) js).finSupport.card : ℝ≥0∞)⁻¹ ^ 2 *
--           (∑ seed ∈ (generateSeed spec (Function.update qb i s) js).finSupport,
--             [= s | cf <$> (simulateQ seededOracle main).run seed]) ^ 2 - [= s | cf <$> main] / h := by {
--         refine tsub_le_tsub ?_ le_rfl
--         have := ENNReal.rpow_sum_le_const_mul_sum_rpow
--           ((generateSeed spec (Function.update qb i s) js).finSupport)
--           (fun seed => [= s | cf <$> (simulateQ seededOracle main).run seed])
--           (one_le_two)
--         simp only [] at this
--         have hc : ((finSupport (generateSeed spec (update qb i ↑s) js)).card : ℝ≥0∞)⁻¹ ^ 2 ≠ 0 := by {
--           simp
--         }
--         have := ((ENNReal.mul_le_mul_left hc (by simp)).2 this)
--         simp only [rpow_two] at this
--         refine le_trans this ?_
--         rw [← mul_assoc]
--         refine le_of_eq ?_
--         refine congr_arg (· * _) ?_
--         norm_num
--         rw [pow_two, mul_assoc, ENNReal.inv_mul_cancel, mul_one]
--         · simp
--         · simp
--       }
--     _ = [= s | do
--           let seed ← liftM (generateSeed spec ((Function.update qb i s)) js)
--           cf <$> (simulateQ seededOracle main).run seed] ^ 2 - [= s | cf <$> main] / h := by {
--         rw [probOutput_bind_eq_sum_finSupport]
--         congr 1
--         rw [← mul_pow, Finset.mul_sum]
--         refine congr_arg (· ^ 2) ?_
--         refine Finset.sum_congr (finSupport_liftComp _ _).symm fun seed hseed => ?_
--         rw [liftM_eq_liftComp, probOutput_liftComp, probOutput_generateSeed']
--         refine mem_support_of_mem_finSupport _ ?_
--         simpa using hseed
--       }
--     _ = [= s | cf <$> main] ^ 2 - [= s | cf <$> main] / h := by {
--         simp only [liftM_eq_liftComp, seededOracle.probOutput_generateSeed_bind_map_simulateQ, h]
--       }

-- theorem probFailure_fork_le :
--     let acc : ℝ≥0∞ := ∑ s, [= some s | cf <$> main]
--     let h : ℝ≥0∞ := Fintype.card (spec.Range i)
--     let q := qb i + 1
--     [⊥ | fork main qb js i cf] ≤ 1 - acc * (acc / q - h⁻¹) := by
--   let acc : ℝ≥0∞ := ∑ s, [= some s | cf <$> main]
--   let h : ℝ≥0∞ := Fintype.card (spec.Range i)
--   let q := qb i + 1
--   calc [⊥ | fork main qb js i cf]
--     _ = 1 - ∑ s, [= (some s, some s) | Prod.map cf cf <$> fork main qb js i cf] := by
--       have := (probFailure_eq_sub_sum_probOutput_map (fork main qb js i cf) (Prod.map cf cf))
--       rw [this]
--       refine congr_arg (_ - ·) ?_ --
--       rw [Fintype.sum_prod_type]
--       rw [Fintype.sum_option]
--       simp
--       refine (Finset.sum_congr rfl fun s hs => ?_)
--       refine Finset.sum_eq_single _ ?_ (by simp)
--       simp
--       tauto
--     _ ≤ 1 - ∑ s, ([= some s | cf <$> main] ^ 2 - [= some s | cf <$> main] / h) := by
--       refine tsub_le_tsub le_rfl ?_
--       refine Finset.sum_le_sum fun s _ => ?_
--       have := le_probOutput_fork main qb js i cf s
--       exact this
--     _ ≤ 1 - ((∑ s, [= some s | cf <$> main] ^ 2) - (∑ s, [= some s | cf <$> main] / h)) := by
--       refine tsub_le_tsub le_rfl ?_
--       sorry -- Hypothesis that `h` is sufficiently large
--     _ = 1 - (∑ s, [= some s | cf <$> main] ^ 2) + (∑ s, [= some s | cf <$> main] / h) := by
--       sorry -- Hypothesis that `h` is sufficiently large
--     _ ≤ 1 - (∑ s, [= some s | cf <$> main]) ^ 2 / q + (∑ s, [= some s | cf <$> main]) / h := by
--       simp only [div_eq_mul_inv]
--       refine add_le_add ?_ (by simp [Finset.sum_mul])
--       refine tsub_le_tsub le_rfl ?_
--       have := ENNReal.rpow_sum_le_const_mul_sum_rpow
--           (Finset.univ : Finset (Fin (qb i + 1)))
--           (fun s => [= s | cf <$> main])
--           (one_le_two)
--       norm_num at this
--       rw [mul_comm, ENNReal.inv_mul_le_iff]
--       · refine le_trans this ?_
--         simp [q]
--       · simp [q]
--       · simp [q]
--     _ = 1 - acc ^ 2 / q + acc / h := rfl
--     _ = 1 - acc * (acc / q - h⁻¹) := by
--       rw [ENNReal.mul_sub]
--       · simp [div_eq_mul_inv]
--         ring_nf
--         sorry -- Hypothesis that `h` is sufficiently large
--       · simp [acc]


-- end OracleComp
-/
