/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.QueryTracking.ObservationOracle
import VCVio.ProgramLogic.Relational.Quantitative
import VCVio.EvalDist.TVDist

/-!
# Leakage Judgments for Side-Channel Reasoning

This file defines three leakage judgments of increasing strength, enabling formal
side-channel reasoning within the VCVio framework. All three operate on observed
computations (outputs of `runObs`) that produce a result paired with an accumulated trace.

## Main Definitions

* `TraceNoninterference`: exact trace equality in every coupling (pRHL indicator).
  Two observed computations satisfy this when their trace components always match,
  regardless of the result. This is the VCVio analogue of constant-time execution.
* `ProbLeakFree`: distributional trace independence.
  The trace distribution does not depend on secrets.
* `LeakageBound`: approximate trace independence via total variation distance.
  The trace distributions differ by at most `ε`.

## Main Results

* `traceNoninterference_implies_probLeakFree`: exact trace equality implies distributional
  independence.
* `probLeakFree_iff_leakageBound_zero`: `ProbLeakFree` is the `ε = 0` case of `LeakageBound`.
* `leakageBound_triangle`: transitivity for game-hopping arguments.
-/

open OracleSpec OracleComp ENNReal

universe u

namespace OracleComp.Leakage

variable {ι₁ : Type u} {ι₂ : Type u} {ι₃ : Type u}
variable {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂} {spec₃ : OracleSpec ι₃}
variable {α β γ : Type} {ω : Type}

/-! ### TraceNoninterference -/

/-- Exact trace noninterference: two observed computations produce equal trace components
in every coupled output. This is the strongest leakage judgment, corresponding to
constant-time execution for deterministic channels.

Defined via `RelTriple'` (the pRHL indicator pattern from `QuantitativeDefs.lean`). -/
def TraceNoninterference [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    (oa₁ : OracleComp spec₁ (α × ω))
    (oa₂ : OracleComp spec₂ (β × ω)) : Prop :=
  ProgramLogic.Relational.RelTriple' oa₁ oa₂ (fun z₁ z₂ => z₁.2 = z₂.2)

/-! ### ProbLeakFree -/

/-- Distributional trace independence: the trace distributions are identical regardless
of which computation produced them. This captures the property that an adversary observing
only the trace cannot distinguish between the two computations.

The comparison is made at the `SPMF` level via `evalDist`, allowing computations over
different oracle specs to be compared. -/
def ProbLeakFree [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    (oa₁ : OracleComp spec₁ (α × ω))
    (oa₂ : OracleComp spec₂ (β × ω)) : Prop :=
  evalDist (Prod.snd <$> oa₁) = evalDist (Prod.snd <$> oa₂)

/-! ### LeakageBound -/

/-- Approximate trace independence: the trace distributions differ by at most `ε` in total
variation distance. This enables game-hopping arguments where each hop introduces a small
leakage discrepancy. -/
def LeakageBound [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    (ε : ℝ) (oa₁ : OracleComp spec₁ (α × ω))
    (oa₂ : OracleComp spec₂ (β × ω)) : Prop :=
  SPMF.tvDist (evalDist (Prod.snd <$> oa₁)) (evalDist (Prod.snd <$> oa₂)) ≤ ε

/-! ### Bridge Lemmas -/

/-- Exact trace noninterference implies distributional trace independence:
if traces always match in every coupling, their distributions must be equal. -/
theorem traceNoninterference_implies_probLeakFree
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : TraceNoninterference oa₁ oa₂) :
    ProbLeakFree oa₁ oa₂ :=
  ProgramLogic.Relational.evalDist_map_eq_of_relTriple' h

/-- `ProbLeakFree` is equivalent to `LeakageBound 0`. -/
theorem probLeakFree_iff_leakageBound_zero
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)} :
    ProbLeakFree oa₁ oa₂ ↔ LeakageBound 0 oa₁ oa₂ := by
  simp only [ProbLeakFree, LeakageBound]
  constructor
  · intro h; rw [h]; simp [SPMF.tvDist_self]
  · intro h
    have h0 := SPMF.tvDist_nonneg (evalDist (Prod.snd <$> oa₁)) (evalDist (Prod.snd <$> oa₂))
    have := le_antisymm h h0
    rwa [SPMF.tvDist_eq_zero_iff, SPMF.toPMF_inj] at this

/-- Transitivity of `LeakageBound` for game-hopping: if the first pair of computations
has leakage at most `ε₁` and the second pair at most `ε₂`, then the outer pair has
leakage at most `ε₁ + ε₂`. -/
theorem leakageBound_triangle
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    [spec₃.Fintype] [spec₃.Inhabited]
    {ε₁ ε₂ : ℝ}
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    {oa₃ : OracleComp spec₃ (γ × ω)}
    (h₁₂ : LeakageBound ε₁ oa₁ oa₂) (h₂₃ : LeakageBound ε₂ oa₂ oa₃) :
    LeakageBound (ε₁ + ε₂) oa₁ oa₃ := by
  unfold LeakageBound at *
  calc SPMF.tvDist (evalDist (Prod.snd <$> oa₁)) (evalDist (Prod.snd <$> oa₃))
      ≤ SPMF.tvDist (evalDist (Prod.snd <$> oa₁)) (evalDist (Prod.snd <$> oa₂)) +
        SPMF.tvDist (evalDist (Prod.snd <$> oa₂)) (evalDist (Prod.snd <$> oa₃)) :=
          SPMF.tvDist_triangle _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add h₁₂ h₂₃

/-- `ProbLeakFree` is reflexive. -/
@[simp]
theorem probLeakFree_refl [spec₁.Fintype] [spec₁.Inhabited]
    (oa : OracleComp spec₁ (α × ω)) :
    ProbLeakFree oa oa := rfl

/-- `ProbLeakFree` is symmetric. -/
theorem probLeakFree_symm
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : ProbLeakFree oa₁ oa₂) :
    ProbLeakFree oa₂ oa₁ := h.symm

/-- `LeakageBound` with `ε = 0` implies `ProbLeakFree`. -/
theorem probLeakFree_of_leakageBound_zero
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound 0 oa₁ oa₂) :
    ProbLeakFree oa₁ oa₂ :=
  probLeakFree_iff_leakageBound_zero.mpr h

/-- `LeakageBound` is reflexive with bound `0`. -/
@[simp]
theorem leakageBound_refl [spec₁.Fintype] [spec₁.Inhabited]
    (oa : OracleComp spec₁ (α × ω)) :
    LeakageBound 0 oa oa := by
  unfold LeakageBound; simp

/-- `LeakageBound` is symmetric. -/
theorem leakageBound_symm
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {ε : ℝ} {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε oa₁ oa₂) :
    LeakageBound ε oa₂ oa₁ := by
  unfold LeakageBound at *
  rwa [SPMF.tvDist_comm]

/-- Monotonicity: a smaller leakage bound implies a larger one. -/
theorem leakageBound_mono
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {ε₁ ε₂ : ℝ} (hε : ε₁ ≤ ε₂)
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε₁ oa₁ oa₂) :
    LeakageBound ε₂ oa₁ oa₂ := le_trans h hε

/-! ### Compositional Lemmas: Map -/

/-- Mapping the result component preserves distributional trace independence. -/
theorem probLeakFree_map_fst
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : ProbLeakFree oa₁ oa₂) {δ : Type} (f₁ : α → γ) (f₂ : β → δ) :
    ProbLeakFree (Prod.map f₁ id <$> oa₁) (Prod.map f₂ id <$> oa₂) := by
  unfold ProbLeakFree at *
  simp only [Functor.map_map]; exact h

/-- Mapping the result component preserves approximate trace independence. -/
theorem leakageBound_map_fst
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {ε : ℝ} {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε oa₁ oa₂) {δ : Type} (f₁ : α → γ) (f₂ : β → δ) :
    LeakageBound ε (Prod.map f₁ id <$> oa₁) (Prod.map f₂ id <$> oa₂) := by
  unfold LeakageBound at *
  simp only [Functor.map_map]; exact h

/-- Mapping the result component preserves trace noninterference. -/
theorem traceNoninterference_map_fst
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : TraceNoninterference oa₁ oa₂) {δ : Type} (f₁ : α → γ) (f₂ : β → δ) :
    TraceNoninterference (Prod.map f₁ id <$> oa₁) (Prod.map f₂ id <$> oa₂) := by
  unfold TraceNoninterference at *
  rw [ProgramLogic.Relational.relTriple'_iff_relTriple] at h ⊢
  exact ProgramLogic.Relational.relTriple_map h

/-- Mapping the trace component with the same function preserves distributional trace
independence. -/
theorem probLeakFree_map_snd
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : ProbLeakFree oa₁ oa₂) {ω' : Type} (g : ω → ω') :
    ProbLeakFree (Prod.map id g <$> oa₁) (Prod.map id g <$> oa₂) := by
  unfold ProbLeakFree at *
  simp only [snd_map_prod_map_eq_map, evalDist_map] at h ⊢
  exact congrArg (Functor.map g) h

/-- Mapping the trace component with the same function preserves approximate trace
independence. -/
theorem leakageBound_map_snd
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {ε : ℝ} {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε oa₁ oa₂) {ω' : Type} (g : ω → ω') :
    LeakageBound ε (Prod.map id g <$> oa₁) (Prod.map id g <$> oa₂) := by
  unfold LeakageBound at *
  simp only [snd_map_prod_map_eq_map, evalDist_map] at h ⊢
  exact le_trans (SPMF.tvDist_map_le g _ _) h

/-- Mapping the trace component with the same function preserves trace noninterference. -/
theorem traceNoninterference_map_snd
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : TraceNoninterference oa₁ oa₂) {ω' : Type} (g : ω → ω') :
    TraceNoninterference (Prod.map id g <$> oa₁) (Prod.map id g <$> oa₂) := by
  unfold TraceNoninterference at *
  rw [ProgramLogic.Relational.relTriple'_iff_relTriple] at h ⊢
  exact ProgramLogic.Relational.relTriple_map
    (ProgramLogic.Relational.relTriple_post_mono h fun {_ _} hw =>
      congrArg g hw)

/-! ### Compositional Lemmas: Bind -/

private lemma snd_map_bind_snd {m : Type → Type _} [Monad m] [LawfulMonad m]
    {α' ω₁ γ' ω₂ : Type} (mx : m (α' × ω₁)) (f : ω₁ → m (γ' × ω₂)) :
    Prod.snd <$> (mx >>= fun z => f z.2) =
    (Prod.snd <$> mx) >>= fun w => Prod.snd <$> f w := by
  simp only [← bind_pure_comp, bind_assoc, pure_bind]

/-- Trace noninterference is preserved by sequential composition (bind).
The continuations may depend on both the result and the trace, but whenever the
traces match, the continuations must themselves be trace noninterfering. -/
theorem traceNoninterference_bind
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {δ ω' : Type}
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    {f₁ : (α × ω) → OracleComp spec₁ (γ × ω')}
    {f₂ : (β × ω) → OracleComp spec₂ (δ × ω')}
    (h : TraceNoninterference oa₁ oa₂)
    (hf : ∀ a b w, TraceNoninterference (f₁ (a, w)) (f₂ (b, w))) :
    TraceNoninterference (oa₁ >>= f₁) (oa₂ >>= f₂) := by
  unfold TraceNoninterference at *
  rw [ProgramLogic.Relational.relTriple'_iff_relTriple] at h ⊢
  refine ProgramLogic.Relational.relTriple_bind h fun z₁ z₂ hw => ?_
  obtain ⟨a, w₁⟩ := z₁; obtain ⟨b, w₂⟩ := z₂
  subst hw
  exact ProgramLogic.Relational.relTriple'_iff_relTriple.mp (hf a b w₁)

/-- Distributional trace independence is preserved by bind when the continuation
depends only on the trace (second component). -/
theorem probLeakFree_bind_of_trace_only
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {δ ω' : Type}
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : ProbLeakFree oa₁ oa₂)
    {f : ω → OracleComp spec₁ (γ × ω')} {g : ω → OracleComp spec₂ (δ × ω')}
    (hfg : ∀ w, ProbLeakFree (f w) (g w)) :
    ProbLeakFree (oa₁ >>= fun z => f z.2) (oa₂ >>= fun z => g z.2) := by
  unfold ProbLeakFree at *
  rw [snd_map_bind_snd _ f, snd_map_bind_snd _ g, evalDist_bind, evalDist_bind, h]
  congr 1; funext w; exact hfg w

/-- Approximate trace independence is preserved by bind when the continuation depends
only on the trace and produces identical trace distributions. -/
theorem leakageBound_bind_of_trace_only
    [spec₁.Fintype] [spec₁.Inhabited] [spec₂.Fintype] [spec₂.Inhabited]
    {ε : ℝ} {δ ω' : Type}
    {oa₁ : OracleComp spec₁ (α × ω)} {oa₂ : OracleComp spec₂ (β × ω)}
    (h : LeakageBound ε oa₁ oa₂)
    {f : ω → OracleComp spec₁ (γ × ω')} {g : ω → OracleComp spec₂ (δ × ω')}
    (hfg : ∀ w, ProbLeakFree (f w) (g w)) :
    LeakageBound ε (oa₁ >>= fun z => f z.2) (oa₂ >>= fun z => g z.2) := by
  unfold LeakageBound ProbLeakFree at *
  rw [snd_map_bind_snd _ f, snd_map_bind_snd _ g, evalDist_bind, evalDist_bind]
  rw [show (fun w => evalDist (Prod.snd <$> f w)) =
      fun w => evalDist (Prod.snd <$> g w) from funext hfg]
  exact le_trans (SPMF.tvDist_bind_right_le _ _ _) h

end OracleComp.Leakage
