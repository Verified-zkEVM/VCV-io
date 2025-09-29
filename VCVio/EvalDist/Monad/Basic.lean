/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Basic

/-!
# Evaluation Distributions of Computations with `Bind`

File for lemmas about `evalDist` and `support` involving the monadic `pure` and `bind`.
-/
universe u v w

variable {α β γ : Type u} {m : Type u → Type v} [Monad m]

open ENNReal

section pure

@[simp] lemma support_pure [HasEvalSet m] (x : α) :
    support (pure x : m α) = {x} := by aesop

lemma mem_support_pure_iff [HasEvalSet m] (x y : α) :
    x ∈ support (pure y : m α) ↔ x = y := by aesop
lemma mem_support_pure_iff' [HasEvalSet m] (x y : α) :
    x ∈ support (pure y : m α) ↔ y = x := by aesop

@[simp] lemma finSupport_pure [HasEvalSet m] [HasEvalFinset m] (x : α) :
    finSupport (pure x : m α) = {x} := by aesop

lemma mem_finSupport_pure_iff [HasEvalSet m] [HasEvalFinset m] (x y : α) :
    x ∈ finSupport (pure y : m α) ↔ x = y := by aesop
lemma mem_finSupport_pure_iff' [HasEvalSet m] [HasEvalFinset m] (x y : α) :
    x ∈ finSupport (pure y : m α) ↔ y = x := by aesop

lemma evalDist_pure [HasEvalSPMF m] {α : Type u} (x : α) :
    evalDist (pure x : m α) = pure x := by aesop

@[simp] lemma evalDist_comp_pure [HasEvalSPMF m] :
    evalDist ∘ (pure : α → m α) = pure := by aesop

@[simp] lemma evalDist_comp_pure' [HasEvalSPMF m] (f : α → β) :
    evalDist ∘ (pure : β → m β) ∘ f = pure ∘ f := by aesop

@[simp] lemma probOutput_pure [HasEvalSPMF m] [DecidableEq α] (x y : α) :
    Pr[= x | (pure y : m α)] = if x = y then 1 else 0 := by aesop

@[simp] lemma probOutput_pure_self [HasEvalSPMF m] (x : α) :
    Pr[= x | (pure x : m α)] = 1 := by aesop

@[simp] lemma probFailure_pure [HasEvalSPMF m] (x : α) :
    Pr[⊥ | (pure x : m α)] = 0 := by aesop

/-- Fallback when we don't have decidable equality. -/
lemma probOutput_pure_eq_indicator [HasEvalSPMF m] (x y : α) :
    Pr[= x | (pure y : m α)] = Set.indicator {y} (Function.const α 1) x := by aesop

@[simp] lemma probEvent_pure [HasEvalSPMF m] (x : α) (p : α → Prop) [DecidablePred p] :
    Pr[p | (pure x : m α)] = if p x then 1 else 0 := by aesop

/-- Fallback when we don't have decidable equality. -/
lemma probEvent_pure_eq_indicator [HasEvalSPMF m] (x : α) (p : α → Prop) :
    Pr[p | (pure x : m α)] = Set.indicator {x | p x} (Function.const α 1) x := by aesop


end pure

section bind

@[simp] lemma support_bind [HasEvalSet m] (mx : m α) (my : α → m β) :
    support (mx >>= my) = ⋃ x ∈ support mx, support (my x) := by aesop

lemma mem_support_bind_iff [HasEvalSet m] (mx : m α) (my : α → m β) (y : β) :
    y ∈ support (mx >>= my) ↔ ∃ x ∈ support mx, y ∈ support (my x) := by simp

-- dtumad: do we need global assumptions about `decidable_eq` for the `finSupport` definition?
@[simp] lemma finSupport_bind [HasEvalSet m] [HasEvalFinset m]
    [DecidableEq β] (mx : m α) (my : α → m β) :
    finSupport (mx >>= my) = Finset.biUnion (finSupport mx) fun x => finSupport (my x) := by aesop

lemma mem_finSupport_bind_iff [HasEvalSet m] [HasEvalFinset m]
    [DecidableEq β] (mx : m α) (my : α → m β) (y : β) :
    y ∈ finSupport (mx >>= my) ↔ ∃ x ∈ finSupport mx, y ∈ finSupport (my x) := by aesop

@[simp] lemma evalDist_bind [HasEvalSPMF m] (mx : m α) (my : α → m β) :
    evalDist (mx >>= my) = evalDist mx >>= fun x => evalDist (my x) :=
  MonadHom.toFun_bind' _ mx my

lemma probOutput_bind_eq_tsum [HasEvalSPMF m] (mx : m α) (my : α → m β) (y : β) :
    Pr[= y | mx >>= my] = ∑' x : α, Pr[= x | mx] * Pr[= y | my x] := by
  simp [probOutput, tsum_option _ ENNReal.summable, Option.elimM]



end bind

section map

-- @[simp] lemma support_map [LawfulMonad m] (f : α → β) (mx : m α) :
--     support (f <$> mx) = f '' support mx := by
--   rw [map_eq_bind_pure_comp]
--   aesop


-- @[simp] lemma evalDist_map [LawfulMonad m] (mx : m α) (f : α → β) :
--     evalDist (f <$> mx) = f <$> (evalDist mx) := by
--   simp [map_eq_bind_pure_comp]

-- @[simp] lemma evalDist_comp_map [LawfulMonad m] (mx : m α) : evalDist ∘ (fun f => f <$> mx) =
--     fun f : (α → β) => f <$> evalDist mx := by simp [funext_iff]


end map



-- @[simp] lemma support_seq [LawfulMonad m] (mf : m (α → β)) (mx : m α) :
--     support (mf <*> mx) = ⋃ f ∈ support mf, f '' support mx := by
--   simp [seq_eq_bind_map]


-- @[simp] lemma evalDist_seq [LawfulMonad m] (mf : m (α → β)) (mx : m α) :
--     evalDist (mf <*> mx) = evalDist mf <*> evalDist mx := by simp [seq_eq_bind_map]


-- open Classical in
-- @[simp] lemma support_seqLeft [LawfulMonad m] (mx : m α) (my : m β) :
--     support (mx <* my) = if support my = ∅ then ∅ else support mx := by
--   simp [seqLeft_eq, Set.ext_iff]

-- open Classical in
-- @[simp] lemma support_seqRight [LawfulMonad m] (mx : m α) (my : m β) :
--     support (mx *> my) = if support mx = ∅ then ∅ else support my := by
--   simp [seqRight_eq, Set.ext_iff]


lemma probOutput_true_eq_probEvent {α} {m : Type → Type u} [Monad m] [HasEvalSPMF m]
    (mx : m α) (p : α → Prop) : Pr{let x ← mx}[p x] = Pr[p | mx] := by
  stop
  rw [probEvent_eq_tsum_indicator]
  rw [probOutput_bind_eq_tsum]
  refine tsum_congr fun α => ?_
  simp [Set.indicator]
  congr
  rw [eq_true_eq_id]
  rfl

-- section bind_congr -- TODO: we should have tactics for this kind of thing

-- variable {ι : Type v} {spec : OracleSpec ι} {α β γ δ : Type u} [spec.Fintype]

-- lemma probFailure_bind_congr (oa : OracleComp spec α)
--     {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ}
--     (h : ∀ x ∈ oa.support, [⊥ | ob x] = [⊥ | oc x]) : [⊥ | oa >>= ob] = [⊥ | oa >>= oc] := by
--   sorry

-- lemma probFailure_bind_congr' (oa : OracleComp spec α)
--     {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ}
--     (h : ∀ x, [⊥ | ob x] = [⊥ | oc x]) : [⊥ | oa >>= ob] = [⊥ | oa >>= oc] := by
--   sorry

-- lemma probOutput_bind_congr {oa : OracleComp spec α} {ob₁ ob₂ : α → OracleComp spec β} {y : β}
--     (h : ∀ x ∈ oa.support, [= y | ob₁ x] = [= y | ob₂ x]) :
--     [= y | oa >>= ob₁] = [= y | oa >>= ob₂] := by
--   sorry

-- lemma probOutput_bind_congr' (oa : OracleComp spec α) {ob₁ ob₂ : α → OracleComp spec β} (y : β)
--     (h : ∀ x, [= y | ob₁ x] = [= y | ob₂ x]) :
--     [= y | oa >>= ob₁] = [= y | oa >>= ob₂] := by
--   sorry

-- lemma probOutput_bind_mono {oa : OracleComp spec α}
--     {ob : α → OracleComp spec β} {oc : α → OracleComp spec γ} {y : β} {z : γ}
--     (h : ∀ x ∈ oa.support, [= y | ob x] ≤ [= z | oc x]) :
--     [= y | oa >>= ob] ≤ [= z | oa >>= oc] := by
--   sorry

-- lemma probOutput_bind_congr_div_const {oa : OracleComp spec α}
--     {ob₁ ob₂ : α → OracleComp spec β} {y : β} {r : ℝ≥0∞}
--     (h : ∀ x ∈ oa.support, [= y | ob₁ x] = [= y | ob₂ x] / r) :
--     [= y | oa >>= ob₁] = [= y | oa >>= ob₂] / r := by
--   sorry

-- lemma probOutput_bind_congr_eq_add {γ₁ γ₂ : Type u}
--     {oa : OracleComp spec α} {ob : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ oa.support, [= y | ob x] = [= z₁ | oc₁ x] + [= z₂ | oc₂ x]) :
--     [= y | oa >>= ob] = [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] := by
--   simp [probOutput_bind_eq_tsum, ← ENNReal.tsum_add]
--   refine tsum_congr fun x => ?_
--   by_cases hx : x ∈ oa.support
--   · simp [h x hx, left_distrib]
--   · simp [probOutput_eq_zero _ _ hx]

-- lemma probOutput_bind_congr_le_add {γ₁ γ₂ : Type u}
--     {oa : OracleComp spec α} {ob : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ oa.support, [= y | ob x] ≤ [= z₁ | oc₁ x] + [= z₂ | oc₂ x]) :
--     [= y | oa >>= ob] ≤ [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] := by
--   sorry

-- lemma probOutput_bind_congr_add_le {γ₁ γ₂ : Type u}
--     {oa : OracleComp spec α} {ob : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ oa.support, [= z₁ | oc₁ x] + [= z₂ | oc₂ x] ≤ [= y | ob x]) :
--     [= z₁ | oa >>= oc₁] + [= z₂ | oa >>= oc₂] ≤ [= y | oa >>= ob] := by
--   sorry

-- lemma probOutput_bind_congr_le_sub {γ₁ γ₂ : Type u}
--     {oa : OracleComp spec α} {ob : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ oa.support, [= y | ob x] ≤ [= z₁ | oc₁ x] - [= z₂ | oc₂ x]) :
--     [= y | oa >>= ob] ≤ [= z₁ | oa >>= oc₁] - [= z₂ | oa >>= oc₂] := by
--   sorry

-- lemma probOutput_bind_congr_sub_le {γ₁ γ₂ : Type u}
--     {oa : OracleComp spec α} {ob : α → OracleComp spec β}
--       {oc₁ : α → OracleComp spec γ₁} {oc₂ : α → OracleComp spec γ₂}
--     {y : β} {z₁ : γ₁} {z₂ : γ₂}
--     (h : ∀ x ∈ oa.support, [= z₁ | oc₁ x] - [= z₂ | oc₂ x] ≤ [= y | ob x]) :
--     [= z₁ | oa >>= oc₁] - [= z₂ | oa >>= oc₂] ≤ [= y | oa >>= ob] := by
--   sorry

-- end bind_congr
