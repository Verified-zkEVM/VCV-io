/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import ToMathlib.Control.OptionT
import VCVio.EvalDist.Option
import VCVio.EvalDist.Defs.AlternativeMonad

/-!
# Probability Distributions on Potentially Failing Computations

This file lifts `MonadLiftT _ SetM` and `MonadLiftT _ SPMF` semantics through the
`OptionT` monad transformer.

dt: should add more instances and connecting lemmas
-/

universe u v w

variable {m : Type u → Type v} [Monad m] {α β γ : Type u}

namespace OptionT

section EvalSet

/-- Standalone `MonadLiftT (OptionT m) SetM` instance under the weaker `[MonadLiftT m SetM]`
assumption. Keeping this standalone means `support` on `OptionT m` works without requiring a
full `MonadLiftT m SPMF` lift — only `MonadLiftT m SetM` is needed.

We declare a `MonadLiftT` (rather than `MonadLift`) so the instance has no `semiOutParam`
arguments to synthesize — `OptionT m`'s `m` cannot be recovered from the `SetM` codomain. -/
noncomputable instance instMonadLiftTSetM {m : Type u → Type v} [Monad m]
    [MonadLiftT m SetM] : MonadLiftT (OptionT m) SetM where
  monadLift mx := some ⁻¹' (support (OptionT.run mx))

noncomputable instance instLawfulMonadLiftTSetM {m : Type u → Type v} [Monad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] :
    LawfulMonadLiftT (OptionT m) SetM where
  monadLift_pure mx := by
    change some ⁻¹' (support (OptionT.run (pure mx : OptionT m _))) = pure mx
    ext x; simp
  monadLift_bind mx my := by
    change (some ⁻¹' (support (OptionT.run (mx >>= my))) : SetM _) =
      ((some ⁻¹' (support mx.run)) >>= fun a => some ⁻¹' (support (my a).run) : SetM _)
    ext x
    rw [Set.mem_preimage]
    calc
      some x ∈ support (OptionT.run (mx >>= my)) ↔
          ∃ a ∈ support mx.run, some x ∈ support (a.elim (pure none) fun x => (my x).run) := by
            rw [OptionT.run_bind, Option.elimM, mem_support_bind_iff]
      _ ↔ ∃ a, some a ∈ support mx.run ∧ some x ∈ support (my a).run := by
            constructor
            · rintro ⟨a, ha, hx⟩
              cases a with
              | none =>
                  simp at hx
              | some a =>
                  exact ⟨a, ha, by simpa using hx⟩
            · rintro ⟨a, ha, hx⟩
              exact ⟨some a, ha, by simpa using hx⟩
      _ ↔ x ∈ ⋃ a ∈ some ⁻¹' support mx.run, some ⁻¹' support (my a).run := by
            simp only [Set.mem_iUnion, Set.mem_preimage, exists_prop]

variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]

omit [LawfulMonadLiftT m SetM] in
@[aesop unsafe norm, grind =]
lemma support_def (mx : OptionT m α) :
    support mx = some ⁻¹' (support mx.run) := rfl

omit [LawfulMonadLiftT m SetM] in
@[simp low]
lemma mem_support_iff (mx : OptionT m α) (x : α) :
    x ∈ support mx ↔ some x ∈ support mx.run := by grind

@[simp]
lemma support_liftM (mx : m α) :
    support (liftM mx : OptionT m α) = support mx := by grind

@[simp]
lemma support_lift (mx : m α) :
    support (OptionT.lift mx) = support mx := by grind

end EvalSet

section HasEvalFinset

/-- Lift a `HasEvalFinset` instance to `OptionT`. by just taking preimage under `some`. -/
noncomputable instance (m : Type u → Type v) [Monad m] [MonadLiftT m SetM] [HasEvalFinset m] :
    HasEvalFinset (OptionT m) where
  finSupport mx := (finSupport mx.run).preimage some (by simp)
  coe_finSupport := by aesop

variable [MonadLiftT m SetM] [HasEvalFinset m]

@[aesop unsafe norm, grind =]
lemma finSupport_def [DecidableEq α] (mx : OptionT m α) :
    finSupport mx = (finSupport mx.run).preimage some (by simp) := rfl

@[simp low]
lemma mem_finSupport_iff [DecidableEq α] (mx : OptionT m α) (x : α) :
    x ∈ finSupport mx ↔ some x ∈ finSupport mx.run := by
  simp [finSupport_def, Finset.mem_preimage]

@[simp]
lemma finSupport_liftM [LawfulMonadLiftT m SetM] [LawfulMonad m] [DecidableEq α] (mx : m α) :
    finSupport (liftM mx : OptionT m α) = finSupport mx := by
  ext x; simp [mem_finSupport_iff, mem_finSupport_iff_mem_support]

@[simp]
lemma finSupport_lift [LawfulMonadLiftT m SetM] [LawfulMonad m] [DecidableEq α] (mx : m α) :
    finSupport (OptionT.lift mx) = finSupport mx := by
  ext x; simp [mem_finSupport_iff, mem_finSupport_iff_mem_support]

end HasEvalFinset

section EvalSPMF

/-- Lift a `MonadLiftT m SPMF` instance to `MonadLiftT (OptionT m) SPMF`. Failure in `OptionT`
contributes to the failure mass of the resulting `SPMF`. -/
noncomputable instance instMonadLiftTSPMF (m : Type u → Type v) [Monad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] :
    MonadLiftT (OptionT m) SPMF where
  monadLift x := OptionT.mapM' (MonadHom.ofLift m SPMF) x

noncomputable instance instLawfulMonadLiftTSPMF (m : Type u → Type v) [Monad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] :
    LawfulMonadLiftT (OptionT m) SPMF where
  monadLift_pure x := by
    change OptionT.mapM' (MonadHom.ofLift m SPMF) (pure x : OptionT m _) = pure x
    simp
  monadLift_bind mx my := by
    change OptionT.mapM' (MonadHom.ofLift m SPMF) (mx >>= my) =
      OptionT.mapM' (MonadHom.ofLift m SPMF) mx >>=
        fun a => OptionT.mapM' (MonadHom.ofLift m SPMF) (my a)
    simp

instance instLawfulFailure (m : Type u → Type v) [Monad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF] :
    HasEvalSet.LawfulFailure (OptionT m) where
  support_failure' := by aesop

/-- The SetM-lift of `OptionT m` (preimage of `support mx.run` under `some`) agrees with the
SPMF-lift (the `OptionT.mapM'` bind into `SPMF`) on outputs, given `EvalDistCompatible m`. -/
instance instEvalDistCompatible (m : Type u → Type v) [Monad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [EvalDistCompatible m] :
    EvalDistCompatible (OptionT m) where
  support_eq_SPMF_support {α} mx := by
    change some ⁻¹' (SetM.run (liftM mx.run : SetM (Option α))) =
      SPMF.support ((MonadHom.ofLift m SPMF) mx.run >>=
        fun y => match y with | some a => pure a | none => failure : SPMF α)
    rw [SPMF.support_bind]
    have hbridge : SetM.run (liftM mx.run : SetM (Option α)) =
        SPMF.support ((MonadHom.ofLift m SPMF) mx.run) :=
      EvalDistCompatible.support_eq_SPMF_support mx.run
    rw [hbridge]
    ext a
    simp only [Set.mem_preimage, Set.mem_iUnion, exists_prop]
    refine ⟨fun h => ⟨some a, h, by simp [SPMF.support_pure]⟩, ?_⟩
    rintro ⟨y, hy, ha⟩
    cases y with
    | none => simp only [SPMF.mem_support_iff, SPMF.failure_apply, ne_eq, not_true_eq_false] at ha
    | some b => rw [SPMF.support_pure, Set.mem_singleton_iff] at ha; exact ha ▸ hy


variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

lemma evalDist_eq (mx : OptionT m α) :
    𝒟[mx] = OptionT.mapM' (MonadHom.ofLift m SPMF) mx := rfl

@[grind =]
lemma probOutput_eq (mx : OptionT m α) (x : α) :
    Pr[= x | mx] = Pr[= some x | mx.run] := by
  simp only [probOutput_def]
  change (OptionT.mapM' (MonadHom.ofLift m SPMF) mx) x = (MonadHom.ofLift m SPMF) mx.run (some x)
  rw [show (OptionT.mapM' (MonadHom.ofLift m SPMF) mx : SPMF α) =
    (MonadHom.ofLift m SPMF) mx.run >>= fun y =>
      match y with | some a => pure a | none => failure from rfl]
  rw [SPMF.bind_apply_eq_tsum]
  refine (tsum_eq_single (some x) fun y hy => ?_).trans (by simp)
  cases y with
  | none => simp
  | some a =>
      have : x ≠ a := by intro h; subst h; exact hy rfl
      simp [this]

@[grind =]
lemma probEvent_eq (mx : OptionT m α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | mx] + Pr[= none | mx.run] = Pr[ fun x => x.all p | mx.run] := by
  simp only [probEvent_eq_tsum_indicator, probOutput_eq]
  rw [add_comm, tsum_option _ ENNReal.summable]
  congr 1
  · simp
  · congr 1; ext a; simp [Set.indicator_apply, decide_eq_true_eq]

@[grind =]
lemma probFailure_eq (mx : OptionT m α) :
    Pr[⊥ | mx] = Pr[⊥ | mx.run] + Pr[= none | mx.run] := by
  simp only [probFailure_def, probOutput_def]
  rw [show 𝒟[mx] = ((MonadHom.ofLift m SPMF) mx.run >>= fun y =>
      match y with | some a => pure a | none => failure : SPMF α) from rfl]
  simp [SPMF.toPMF_bind, Option.elimM, PMF.bind_apply, tsum_option,
    SPMF.toPMF_failure, SPMF.toPMF_pure, SPMF.apply_eq_toPMF_some, evalDist_def]

@[simp, grind =]
lemma probOutput_liftM [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | liftM (n := OptionT m) mx] = Pr[= x | mx] := by
  rw [probOutput_eq]
  show Pr[= some x | (liftM mx : OptionT m _).run] = Pr[= x | mx]
  rw [show (liftM mx : OptionT m _).run = some <$> mx from by
    simp [monad_norm]]
  exact probOutput_map_injective (f := (some : α → Option α)) mx (Option.some_injective _) x

@[simp, grind =]
lemma probOutput_lift [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | OptionT.lift mx] = Pr[= x | mx] :=
  probOutput_liftM mx x

@[simp, grind =]
lemma probEvent_liftM [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[ p | liftM (n := OptionT m) mx] = Pr[ p | mx] := by
  grind only [= probEvent_eq_tsum_indicator, = probOutput_liftM]

@[simp, grind =]
lemma probEvent_lift [LawfulMonad m] (mx : m α) (p : α → Prop) :
    Pr[ p | OptionT.lift mx] = Pr[ p | mx] := by
  grind only [= probEvent_eq_tsum_indicator, = probOutput_lift]

@[simp, grind =]
lemma probFailure_liftM [LawfulMonad m] (mx : m α) :
    Pr[⊥ | liftM (n := OptionT m) mx] = Pr[⊥ | mx] := by
  simp [probFailure_eq]

@[simp, grind =]
lemma probFailure_lift [LawfulMonad m] (mx : m α) :
    Pr[⊥ | OptionT.lift mx] = Pr[⊥ | mx] := by
  simp [probFailure_eq]

end EvalSPMF

end OptionT
