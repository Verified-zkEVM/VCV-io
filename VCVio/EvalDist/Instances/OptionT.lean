/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import ToMathlib.Control.OptionT
import VCVio.EvalDist.Defs.AlternativeMonad
import VCVio.EvalDist.Option

/-!
# Probability Distributions on Potentially Failing Computations

This file lifts `MonadLiftT _ SetM` and `MonadLiftT _ SPMF` semantics through the
`OptionT` monad transformer, providing `support`, `finSupport`, and `evalDist`-based
probability lemmas for `OptionT m α` in terms of the underlying `m (Option α)`.
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
    simp [Set.ext_iff]
  monadLift_bind mx my := by
    change (some ⁻¹' (support (OptionT.run (mx >>= my))) : SetM _) =
      ((some ⁻¹' (support mx.run)) >>= fun a => some ⁻¹' (support (my a).run) : SetM _)
    ext x
    simp only [Set.mem_preimage]
    rw [OptionT.run_bind, Option.elimM, mem_support_bind_iff]
    constructor
    · rintro ⟨(_ | a), ha, hx⟩
      · simp at hx
      · exact Set.mem_iUnion₂.mpr ⟨a, ha, by simpa using hx⟩
    · intro h
      obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.mp h
      exact ⟨some a, ha, by simpa using hx⟩

variable [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]

omit [LawfulMonadLiftT m SetM] in
@[aesop unsafe norm, grind =]
lemma support_def (mx : OptionT m α) : support mx = some ⁻¹' (support mx.run) := rfl

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

/-- Peel the leading sample off the support of an `OptionT.mk`'d bind: any element of the
support of `OptionT.mk (sample >>= body)` factors through a sample `a` in the support of
`sample`, with the element in the support of `OptionT.mk (body a)`. -/
lemma mem_support_bind_mk (sample : m α) (body : α → m (Option β)) {x : β}
    (hx : x ∈ support (OptionT.mk (do
      let a ← sample
      body a))) :
    ∃ a, a ∈ support sample ∧ x ∈ support (OptionT.mk (body a)) := by
  rw [OptionT.mem_support_iff] at hx
  simp only [OptionT.run_mk] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨a, _, hx⟩ := hx
  exact ⟨a, ‹a ∈ support sample›, by simpa [OptionT.mem_support_iff] using hx⟩

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
    refine ⟨fun h => ⟨some a, h, by simp⟩, ?_⟩
    rintro ⟨(_ | y), hy, ha⟩ <;> simp_all

variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]

lemma evalDist_eq (mx : OptionT m α) :
    𝒟[mx] = OptionT.mapM' (MonadHom.ofLift m SPMF) mx := rfl

@[grind =]
lemma probOutput_eq (mx : OptionT m α) (x : α) :
    Pr[= x | mx] = Pr[= some x | mx.run] := by
  simp only [probOutput_def, evalDist_eq, OptionT.mapM', SPMF.bind_apply_eq_tsum]
  refine (tsum_eq_single (some x) fun y hy => ?_).trans (by simp)
  cases y with
  | none => simp
  | some a => simp [show ¬x = a from fun h => hy (h ▸ rfl)]

@[grind =]
lemma probEvent_eq (mx : OptionT m α) (p : α → Prop) [DecidablePred p] :
    Pr[ p | mx] + Pr[= none | mx.run] = Pr[ fun x => x.all p | mx.run] := by
  simp [probEvent_eq_tsum_indicator, probOutput_eq, tsum_option _ ENNReal.summable,
    Set.indicator_apply, add_comm]

@[grind =]
lemma probFailure_eq (mx : OptionT m α) :
    Pr[⊥ | mx] = Pr[⊥ | mx.run] + Pr[= none | mx.run] := by
  simp [probFailure_def, probOutput_def, evalDist_eq, OptionT.mapM', SPMF.toPMF_bind,
    Option.elimM, PMF.bind_apply, tsum_option, SPMF.toPMF_failure, SPMF.toPMF_pure,
    SPMF.apply_eq_toPMF_some, evalDist_def]

@[simp, grind =]
lemma probOutput_liftM [LawfulMonad m] (mx : m α) (x : α) :
    Pr[= x | liftM (n := OptionT m) mx] = Pr[= x | mx] := by
  simp [probOutput_eq]

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
    Pr[ p | OptionT.lift mx] = Pr[ p | mx] :=
  probEvent_liftM mx p

@[simp, grind =]
lemma probFailure_liftM [LawfulMonad m] (mx : m α) :
    Pr[⊥ | liftM (n := OptionT m) mx] = Pr[⊥ | mx] := by
  simp [probFailure_eq]

@[simp, grind =]
lemma probFailure_lift [LawfulMonad m] (mx : m α) :
    Pr[⊥ | OptionT.lift mx] = Pr[⊥ | mx] :=
  probFailure_liftM mx

/-- Bridge lemma: when two `OptionT` computations have underlying `run`s related by an
`Option.map` of a function `f`, their probabilities for the events `P` and `P ∘ f` agree. -/
lemma probEvent_eq_of_run_map_eq [LawfulMonad m]
    (mx : OptionT m α) (my : OptionT m β) (f : β → α) (P : α → Prop)
    (h : mx.run = (Option.map f) <$> my.run) :
    Pr[P | mx] = Pr[P ∘ f | my] := by
  have hmx : mx = f <$> my := by
    change mx.run = (f <$> my).run
    rw [OptionT.run_map]; exact h
  rw [hmx, probEvent_map]

end EvalSPMF

end OptionT
