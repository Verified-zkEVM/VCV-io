/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

/-!
# Random-Function Random-Permutation Switching Lemma
-/

open OracleSpec OracleComp ENNReal

-- /-- Security adversary for RF-RP distinguisher experiments. -/
-- def RF_RP_Adv' (α : ℕ → Type) [∀ n, Fintype (α n)]
--     [∀ n, Inhabited (α n)] [∀ n, DecidableEq (α n)] :=
--   SecAdv (λ n ↦ (α n →ₒ α n)) (λ _ ↦ Unit) (λ _ ↦ Bool)

-- /-- Security adversary for RF-RP distinguisher experiments.
-- Note: We don't give the adversary a `unifSpec` oracle, it only has distinguisher pieces. -/
-- def RF_RP_Adv (α : ℕ → Type) [∀ n, Fintype (α n)]
--     [∀ n, Inhabited (α n)] [∀ n, DecidableEq (α n)] :=
--   SecAdv (λ n ↦ (α n →ₒ α n)) (λ _ ↦ Unit) (λ _ ↦ Bool)

-- def distinguisher {ι : Type} [DecidableEq ι] (spec : ℕ → OracleSpec ι) :=
--   SecAdv spec (λ _ ↦ Unit) (λ _ ↦ Bool)

-- variable {α : ℕ → Type} [∀ n, Fintype (α n)]
--     [∀ n, Inhabited (α n)] [∀ n, DecidableEq (α n)]
--     [∀ n, SampleableType (α n)]

-- /-- Run a `RF_RP_Adv` using a random function to answer queries,
-- implemented as a simulation with a random oracle. -/
-- def RF_Exp (adv : RF_RP_Adv α) : SecExp (λ n ↦ (α n →ₒ α n)) where
--   main n := (· = true) <$> adv.run n ()
--   baseState n := QueryCache (α n →ₒ α n)
--   init_state _ := ∅
--   baseSimOracle _ := randOracle



-- def distinguisher_exp {ι : Type} [DecidableEq ι] (spec : ℕ → OracleSpec ι)
--     {ι' : Type} (spec' : ℕ → OracleSpec ι')
--     (adv : distinguisher spec) {σ₁ σ₂ : Type}
--     (so : (n : ℕ) → spec n →[σ₁]ₛₒ unifSpec)
--     (so' : (n : ℕ) → spec n →[σ₂]ₛₒ unifSpec)
--     (s₁ : ℕ → σ₁) (s₂ : ℕ → σ₂) : SecExp spec where
--   baseState := _
--   init_state := s₁
--   baseSimOracle := so
--   main n := sorry

-- /-- Run a `RF_RP_Adv` using a random permutation to answer queries.
-- The simulation uses an additional finset to avoid choosing duplicate query outputs.

-- Note: We could implement a `randUniqOracle` rather than do this ad hoc.
-- unsure other use cases. -/
-- noncomputable def RP_Exp (adv : RF_RP_Adv α) : SecExp (λ n ↦ (α n →ₒ α n)) where
--   main n := (· = false) <$> adv.run n ()
--   baseState n := QueryCache (α n →ₒ α n) × Finset (α n)
--   init_state _ := (∅, ∅)
--   baseSimOracle _ := λ () t (cache, used) ↦ do
--     let (u, cache') ← cache.lookup_or_else () t ($ usedᶜ)
--     return (u, cache', insert u used)

-- noncomputable def RF_RP_distinguisher_advantage (adv : RF_RP_Adv α) (n : ℕ) : ℝ≥0∞ :=
--   ((RF_Exp adv).advantage n + (RP_Exp adv).advantage n) / 2

-- lemma state_thing {α ι₁ ι₂: Type} {spec : OracleSpec ι₁} {spec' : OracleSpec ι₂}
--     (oa : OracleComp spec Bool)
--     {σ₁ σ₂ : Type} (so : spec →[σ₁]ₛₒ spec') (so' : spec →[σ₂]ₛₒ spec')
--     (good_step₁ : σ₁ → Prop) (good_step₂ : σ₂ → Prop)
--     (s₁ : σ₁) (s₂ : σ₂) (ε₁ ε₂ : ℝ≥0∞) :
--     [= true | simulate' so s₁ oa] + [= false | simulate' so' s₂ oa] ≤ ε₁ + ε₂ :=
--   sorry

-- lemma strong_interpolation_theorem {α ι₁ ι₂: Type} [DecidableEq ι₁] [DecidableEq ι₂]
--     {spec : OracleSpec ι₁} {spec' : OracleSpec ι₂}
--     (oa : OracleComp spec Bool)
--     {σ₁ σ₂ : Type} (so₁ : spec →[σ₁]ₛₒ spec') (so₂ : spec →[σ₂]ₛₒ spec')
--     (good_view : QueryLog spec' → Prop)
--     (ε ε' : ℝ≥0∞) (s₁ : σ₁) (s₂ : σ₂)
--     -- Simulation with
--     (h₂ : ∀ view : QueryLog spec', good_view view →
--       [= view | (λ z ↦ z.2.2) <$> simulate (loggingOracle ∘ₛₒ so₂) (s₂, ∅) oa] ≥
--         (1 - ε') * [= view | (λ z ↦ z.2.2) <$> simulate (loggingOracle ∘ₛₒ so₁) (s₁, ∅) oa])
--     (h₁ : [good_view | (λ z ↦ z.2.2) <$> simulate (loggingOracle ∘ₛₒ so₁) (s₁, ∅) oa] ≥ 1 - ε) :
--     [= true | simulate' so₁ s₁ oa] + [= false | simulate' so₂ s₂ oa] ≤ ε + ε' := by
--   sorry

-- theorem RF_RP_switching_lemma (adv : RF_RP_Adv α) (n : ℕ) :
--     let q : ℕ := (adv.qb ()).eval n
--     let k : ℕ := Fintype.card (α n)
--     (RF_RP_distinguisher_advantage adv n) ≤ (1 + q * (q + 1) / k ^ n) / 2 := by
--   unfold RF_RP_distinguisher_advantage
--   refine ENNReal.div_le_div ?_ le_rfl
--   sorry
