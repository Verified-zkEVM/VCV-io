/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public meta import VCVio.ProgramLogic.Tactics.Common
public import VCVio.ProgramLogic.Relational.Basic
public meta import VCVio.ProgramLogic.Tactics.Relational.Internals
public import Loom.Triple.SpecLemmas

/-!
# Unary VCGen structural rules
-/

public meta section

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic
namespace TacticInternals
namespace Unary

universe u v

/-- Cached raw-`wp` structural leaf for `pure`.

The equality theorem `wp_pure` remains the canonical rewrite rule.
This lower-bound form lets raw `wp` goals use the cached `@[vcspec]`
backward-rule path before falling back to `@[wpStep]`. -/
theorem wp_pure_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec] {α : Type} (x : α)
    (post : α → ENNReal) :
    post x ≤ wp (pure x : OracleComp spec α) post := by
  rw [OracleComp.ProgramLogic.wp_pure]

/-- Cached raw-`wp` structural leaf for functorial map. -/
theorem wp_map_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec] {α β : Type}
    (f : α → β) (oa : OracleComp spec α) (post : β → ENNReal) :
    wp oa (post ∘ f) ≤ wp (f <$> oa) post := by
  rw [OracleComp.ProgramLogic.wp_map]

/-- Cached raw-`wp` structural leaf for conditionals. -/
theorem wp_ite_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec] {α : Type} (c : Prop) [Decidable c]
    (oa ob : OracleComp spec α) (post : α → ENNReal) :
    (if c then wp oa post else wp ob post) ≤ wp (if c then oa else ob) post := by
  rw [OracleComp.ProgramLogic.wp_ite]

/-- Cached raw-`wp` structural leaf for dependent conditionals. -/
theorem wp_dite_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec] {α : Type} (c : Prop) [Decidable c]
    (oa : c → OracleComp spec α) (ob : ¬c → OracleComp spec α) (post : α → ENNReal) :
    (if h : c then wp (oa h) post else wp (ob h) post) ≤ wp (dite c oa ob) post := by
  rw [OracleComp.ProgramLogic.wp_dite]

/-- Cached raw-`wp` structural leaf for `replicate (n + 1)`. -/
theorem wp_replicate_succ_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) (n : Nat) (post : List α → ENNReal) :
    wp oa (fun x => wp (oa.replicate n) (fun xs => post (x :: xs))) ≤
      wp (oa.replicate (n + 1)) post := by
  rw [OracleComp.ProgramLogic.wp_replicate_succ]

/-- Cached raw-`wp` structural leaf for `List.mapM` on `x :: xs`. -/
theorem wp_list_mapM_cons_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec] {α β : Type}
    (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ENNReal) :
    wp (f x) (fun y => wp (xs.mapM f) (fun ys => post (y :: ys))) ≤
      wp ((x :: xs).mapM f) post := by
  rw [OracleComp.ProgramLogic.wp_list_mapM_cons]

/-- Cached raw-`wp` structural leaf for `List.foldlM` on `x :: xs`. -/
theorem wp_list_foldlM_cons_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec] {α σ : Type}
    (x : α) (xs : List α) (f : σ → α → OracleComp spec σ)
    (init : σ) (post : σ → ENNReal) :
    wp (f init x) (fun s => wp (xs.foldlM f s) post) ≤
      wp ((x :: xs).foldlM f init) post := by
  rw [OracleComp.ProgramLogic.wp_list_foldlM_cons]

/-- Cached raw-`wp` structural leaf for oracle queries. -/
theorem wp_query_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec]
    (t : spec.Domain) (post : spec.Range t → ENNReal) :
    (∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ENNReal) * post u) ≤
      wp (query t : OracleComp spec (spec.Range t)) post := by
  simpa using le_of_eq (OracleComp.ProgramLogic.wp_HasQuery_query (spec := spec) t post).symm

/-- Cached raw-`wp` structural leaf for `HasQuery.query`. -/
theorem wp_HasQuery_query_le_vcspec {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec]
    (t : spec.Domain) (post : spec.Range t → ENNReal) :
    (∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ENNReal) * post u) ≤
      wp (spec := spec) (HasQuery.query t : OracleComp spec (spec.Range t)) post := by
  simpa using le_of_eq (OracleComp.ProgramLogic.wp_HasQuery_query (spec := spec) t post).symm

/-- Cached raw-`wp` structural leaf for uniform sampling. -/
theorem wp_uniformSample_le_vcspec {α : Type} [SampleableType α] (post : α → ENNReal) :
    (∑' u : α, Pr[= u | ($ᵗ α : ProbComp α)] * post u) ≤
      wp ($ᵗ α : ProbComp α) post := by
  rw [OracleComp.ProgramLogic.wp_uniformSample]

/-- Generic Loom triple bind step with the intermediate postcondition fixed to
the weakest precondition of the continuation. This is the `Std.Do'.Triple`
counterpart of `OracleComp.ProgramLogic.triple_bind_wp`, and lets unary
automation walk transformer-stack `do` blocks without guessing a user cut. -/
theorem stdDoTriple_bind_wp {m : Type u → Type v}
    {Pred EPred : Type u} {α β : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {pre : Pred} (x : m α) (f : α → m β) (post : β → Pred) (epost : EPred) :
    Std.Do'.Triple pre x (fun a => Std.Do'.wp (f a) post epost) epost →
      Std.Do'.Triple pre (x >>= f) post epost := by
  intro h
  exact Std.Do'.Triple.bind x f (fun a => Std.Do'.wp (f a) post epost) h
    (fun _ => Std.Do'.Triple.iff.mpr Lean.Order.PartialOrder.rel_refl)

/-- Close a Loom triple from the corresponding WP entailment.

This is just `Std.Do'.Triple.iff.mpr` packaged as a theorem so tactic code can expose
the weakest-precondition side condition and then run transformer-specific WP normalizers. -/
theorem stdDoTriple_of_wp_le {m : Type u → Type v}
    {Pred EPred : Type u} {α : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {pre : Pred} (x : m α) (post : α → Pred) (epost : EPred)
    (hpre : Lean.Order.PartialOrder.rel pre (Std.Do'.wp x post epost)) :
    Std.Do'.Triple pre x post epost :=
  Std.Do'.Triple.iff.mpr hpre

theorem wp_StateT_get_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {σ : Type u} (post : σ → σ → Pred) (epost : EPred) :
    Std.Do'.wp (MonadStateOf.get : StateT σ m σ) post epost =
      fun s => Std.Do'.wp (pure (s, s) : m (σ × σ))
        (fun p : σ × σ => post p.1 p.2) epost :=
  rfl

theorem wp_StateT_get_layer' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {σ : Type u} (post : σ → σ → Pred) (epost : EPred) :
    Std.Do'.wp (StateT.get : StateT σ m σ) post epost =
      fun s => Std.Do'.wp (pure (s, s) : m (σ × σ))
        (fun p : σ × σ => post p.1 p.2) epost :=
  rfl

theorem stdDoTriple_StateT_get_of_rel {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {σ : Type u} (pre : σ → Pred) (post : σ → σ → Pred) (epost : EPred)
    (h : ∀ s, Lean.Order.PartialOrder.rel (pre s) (post s s)) :
    Std.Do'.Triple pre (StateT.get : StateT σ m σ) post epost := by
  refine Std.Do'.Triple.iff.mpr ?_
  intro s
  change Lean.Order.PartialOrder.rel (pre s)
    (Std.Do'.wp (pure (s, s) : m (σ × σ))
      (fun p : σ × σ => post p.1 p.2) epost)
  exact Lean.Order.PartialOrder.rel_trans (h s)
    (Std.Do'.WP.wp_pure (m := m) (x := (s, s))
      (post := fun p : σ × σ => post p.1 p.2) (epost := epost))

theorem wp_StateT_set_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {σ : Type u} (s' : σ) (post : PUnit → σ → Pred) (epost : EPred) :
    Std.Do'.wp (MonadStateOf.set s' : StateT σ m PUnit) post epost =
      fun _ => Std.Do'.wp (pure (PUnit.unit, s') : m (PUnit × σ))
        (fun p : PUnit × σ => post p.1 p.2) epost :=
  rfl

theorem wp_StateT_run_get_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {σ : Type u} (s : σ) (post : σ → σ → Pred) (epost : EPred) :
    Std.Do'.wp ((MonadStateOf.get : StateT σ m σ).run s)
        (fun p : σ × σ => post p.1 p.2) epost =
      Std.Do'.wp (pure (s, s) : m (σ × σ)) (fun p : σ × σ => post p.1 p.2) epost :=
  rfl

theorem wp_StateT_run_get_layer' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {σ : Type u} (s : σ) (post : σ → σ → Pred) (epost : EPred) :
    Std.Do'.wp ((StateT.get : StateT σ m σ).run s)
        (fun p : σ × σ => post p.1 p.2) epost =
      Std.Do'.wp (pure (s, s) : m (σ × σ)) (fun p : σ × σ => post p.1 p.2) epost :=
  rfl

theorem wp_StateT_run_set_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {σ : Type u} (s s' : σ) (post : PUnit → σ → Pred) (epost : EPred) :
    Std.Do'.wp ((MonadStateOf.set s' : StateT σ m PUnit).run s)
        (fun p : PUnit × σ => post p.1 p.2) epost =
      Std.Do'.wp (pure (PUnit.unit, s') : m (PUnit × σ))
        (fun p : PUnit × σ => post p.1 p.2) epost :=
  rfl

theorem wp_StateT_run_set_layer' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {σ : Type u} (s s' : σ) (post : PUnit → σ → Pred) (epost : EPred) :
    Std.Do'.wp ((StateT.set s' : StateT σ m PUnit).run s)
        (fun p : PUnit × σ => post p.1 p.2) epost =
      Std.Do'.wp (pure (PUnit.unit, s') : m (PUnit × σ))
        (fun p : PUnit × σ => post p.1 p.2) epost :=
  rfl

theorem wp_StateT_map_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {σ α β : Type u} (f : α → β) (x : StateT σ m α) (post : β → σ → Pred)
    (epost : EPred) :
    Std.Do'.wp (f <$> x) post epost =
      fun s => Std.Do'.wp ((f <$> x).run s)
        (fun p : β × σ => post p.1 p.2) epost :=
  rfl

theorem wp_ReaderT_read_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {ρ : Type u} (post : ρ → ρ → Pred) (epost : EPred) :
    Std.Do'.wp (MonadReaderOf.read : ReaderT ρ m ρ) post epost =
      fun r => Std.Do'.wp (pure r : m ρ) (fun a => post a r) epost :=
  rfl

theorem wp_ReaderT_read_layer' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {ρ : Type u} (post : ρ → ρ → Pred) (epost : EPred) :
    Std.Do'.wp (ReaderT.read : ReaderT ρ m ρ) post epost =
      fun r => Std.Do'.wp (pure r : m ρ) (fun a => post a r) epost :=
  rfl

theorem stdDoTriple_ReaderT_read_of_rel {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {ρ : Type u} (pre : ρ → Pred) (post : ρ → ρ → Pred) (epost : EPred)
    (h : ∀ r, Lean.Order.PartialOrder.rel (pre r) (post r r)) :
    Std.Do'.Triple pre (MonadReaderOf.read : ReaderT ρ m ρ) post epost := by
  refine Std.Do'.Triple.iff.mpr ?_
  intro r
  change Lean.Order.PartialOrder.rel (pre r)
    (Std.Do'.wp (pure r : m ρ) (fun a : ρ => post a r) epost)
  exact Lean.Order.PartialOrder.rel_trans (h r)
    (Std.Do'.WP.wp_pure (m := m) (x := r)
      (post := fun a : ρ => post a r) (epost := epost))

theorem wp_ReaderT_run_read_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {ρ : Type u} (r : ρ) (post : ρ → ρ → Pred) (epost : EPred) :
    Std.Do'.wp ((MonadReaderOf.read : ReaderT ρ m ρ).run r) (fun a : ρ => post a r)
        epost =
      Std.Do'.wp (pure r : m ρ) (fun a : ρ => post a r) epost :=
  rfl

theorem wp_ReaderT_run_read_layer' {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {ρ : Type u} (r : ρ) (post : ρ → ρ → Pred) (epost : EPred) :
    Std.Do'.wp ((ReaderT.read : ReaderT ρ m ρ).run r) (fun a : ρ => post a r)
        epost =
      Std.Do'.wp (pure r : m ρ) (fun a : ρ => post a r) epost :=
  rfl

theorem mAlgOrdered_wp_OptionT_run_StateT_get {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec] {σ : Type} (s : σ)
    (post : σ → σ → ENNReal)
    (epost : Std.Do'.EPost.cons ENNReal Std.Do'.EPost.nil) :
    MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal)
      (((StateT.get : StateT σ (OptionT (OracleComp spec)) σ).run s).run)
      (epost.pushOption (fun p : σ × σ => post p.1 p.2)) = post s s := by
  change MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal)
      (pure (some (s, s)) : OracleComp spec (Option (σ × σ)))
      (epost.pushOption (fun p : σ × σ => post p.1 p.2)) = post s s
  rw [MAlgOrdered.wp_pure]

theorem mAlgOrdered_wp_OptionT_run_StateT_set {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec] {σ : Type} (s s' : σ)
    (post : PUnit → σ → ENNReal) (epost : Std.Do'.EPost.cons ENNReal Std.Do'.EPost.nil) :
    MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal)
      (((StateT.set s' : StateT σ (OptionT (OracleComp spec)) PUnit).run s).run)
      (epost.pushOption (fun p : PUnit × σ => post p.1 p.2)) = post PUnit.unit s' := by
  change MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal)
      (pure (some (PUnit.unit, s')) : OracleComp spec (Option (PUnit × σ)))
      (epost.pushOption (fun p : PUnit × σ => post p.1 p.2)) = post PUnit.unit s'
  rw [MAlgOrdered.wp_pure]

theorem mAlgOrdered_wp_OptionT_run_lift {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) (post : α → ENNReal)
    (epost : Std.Do'.EPost.cons ENNReal Std.Do'.EPost.nil) :
    MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal) (OptionT.lift oa).run
      (epost.pushOption post) =
        MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal) oa post := by
  change MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal)
      (oa >>= fun a => pure (some a) : OracleComp spec (Option α))
      (epost.pushOption post) =
    MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal) oa post
  rw [MAlgOrdered.wp_bind]
  refine congrArg (MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal) oa) ?_
  funext a
  rw [MAlgOrdered.wp_pure]

theorem mAlgOrdered_wp_OptionT_run_StateT_monadLift_lift {ι : Type u}
    {spec : OracleSpec ι} [IsUniformSpec spec]
    {σ α : Type} (oa : OracleComp spec α) (s : σ) (post : α → σ → ENNReal)
    (epost : Std.Do'.EPost.cons ENNReal Std.Do'.EPost.nil) :
    MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal)
      (((MonadLift.monadLift (OptionT.lift oa) :
        StateT σ (OptionT (OracleComp spec)) α).run s).run)
      (epost.pushOption (fun p : α × σ => post p.1 p.2)) =
        MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal) oa (fun a => post a s) := by
  simp [MonadLift.monadLift, OptionT.run_lift, MAlgOrdered.wp_map,
    Std.Do'.EPost.cons.pushOption]

theorem wp_StateT_OptionT_monadLift_lift {ι : Type u} {spec : OracleSpec ι}
    [IsUniformSpec spec] {σ α : Type}
    (oa : OracleComp spec α) (post : α → σ → ENNReal)
    (epost : Std.Do'.EPost.cons ENNReal Std.Do'.EPost.nil) :
    Std.Do'.wp
      (MonadLift.monadLift (OptionT.lift oa) : StateT σ (OptionT (OracleComp spec)) α)
      post epost =
        fun s => MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal) oa
          (fun a => post a s) := by
  funext s
  change MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal)
      (((MonadLift.monadLift (OptionT.lift oa) :
        StateT σ (OptionT (OracleComp spec)) α).run s).run)
      (epost.pushOption (fun p : α × σ => post p.1 p.2)) =
        MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal) oa (fun a => post a s)
  exact mAlgOrdered_wp_OptionT_run_StateT_monadLift_lift (spec := spec) oa s post epost

theorem mAlgOrdered_wp_OptionT_run_StateT_monadLift_lift_map {ι : Type u}
    {spec : OracleSpec ι} [IsUniformSpec spec]
    {σ α β : Type} (oa : OracleComp spec α) (s : σ) (f : α × σ → β)
    (post : β → ENNReal) (nonePost : ENNReal) :
    MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal)
      (((MonadLift.monadLift (OptionT.lift oa) :
        StateT σ (OptionT (OracleComp spec)) α).run s).run)
      (fun o => match Option.map f o with | some b => post b | none => nonePost) =
        MAlgOrdered.wp (m := OracleComp spec) (l := ENNReal) oa
          (fun a => post (f (a, s))) := by
  simp [MonadLift.monadLift, OptionT.run_lift, MAlgOrdered.wp_map]

theorem wp_ReaderT_map_layer {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Std.Do'.Assertion Pred] [Std.Do'.Assertion EPred] [Std.Do'.WP m Pred EPred]
    {ρ α β : Type u} (f : α → β) (x : ReaderT ρ m α) (post : β → ρ → Pred)
    (epost : EPred) :
    Std.Do'.wp (f <$> x) post epost =
      fun r => Std.Do'.wp ((f <$> x).run r) (fun b : β => post b r) epost :=
  rfl

attribute [vcspec]
  OracleComp.ProgramLogic.triple_pure
  wp_pure_le_vcspec
  wp_map_le_vcspec
  wp_ite_le_vcspec
  wp_dite_le_vcspec
  wp_replicate_succ_le_vcspec
  wp_list_mapM_cons_le_vcspec
  wp_list_foldlM_cons_le_vcspec
  wp_query_le_vcspec
  wp_HasQuery_query_le_vcspec
  wp_uniformSample_le_vcspec
  -- StateT
  Std.Do'.Spec.get_StateT
  Std.Do'.Spec.set_StateT
  Std.Do'.Spec.modifyGet_StateT
  Std.Do'.Spec.monadLift_StateT
  -- ReaderT
  Std.Do'.Spec.read_ReaderT
  Std.Do'.Spec.monadLift_ReaderT
  Std.Do'.Spec.adapt_ReaderT
  Std.Do'.Spec.withReader_ReaderT
  -- WriterT
  Std.Do'.Spec.tell_WriterT
  Std.Do'.Spec.monadLift_WriterT
  Std.Do'.Spec.mk_WriterT
  Std.Do'.WriterT.wp_pure
  Std.Do'.WriterT.wp_bind
  Std.Do'.WriterT.wp_tell
  Std.Do'.WriterT.wp_monadLift
  Std.Do'.WriterT.wp_map
  -- OptionT
  Std.Do'.Spec.run_OptionT
  Std.Do'.Spec.throw_OptionT
  Std.Do'.Spec.tryCatch_OptionT
  Std.Do'.Spec.orElse_OptionT
  Std.Do'.Spec.monadLift_OptionT
  -- ExceptT
  Std.Do'.Spec.run_ExceptT
  Std.Do'.Spec.throw_ExceptT
  Std.Do'.Spec.tryCatch_ExceptT
  Std.Do'.Spec.orElse_ExceptT
  Std.Do'.Spec.adapt_ExceptT
  Std.Do'.Spec.monadLift_ExceptT
  -- Lifted MonadExceptOf
  Std.Do'.Spec.throw_MonadExcept
  Std.Do'.Spec.tryCatch_MonadExcept
  Std.Do'.Spec.throw_ReaderT
  Std.Do'.Spec.throw_StateT
  Std.Do'.Spec.throw_ExceptT_lift
  Std.Do'.Spec.throw_Option_lift
  Std.Do'.Spec.tryCatch_ReaderT
  Std.Do'.Spec.tryCatch_StateT
  Std.Do'.Spec.tryCatch_ExceptT_lift
  Std.Do'.Spec.tryCatch_OptionT_lift
  -- Generic monad-transformer hooks
  Std.Do'.Spec.monadMap_StateT
  Std.Do'.Spec.monadMap_ReaderT
  Std.Do'.Spec.monadMap_ExceptT
  Std.Do'.Spec.monadMap_OptionT
  Std.Do'.Spec.monadMap_refl
  Std.Do'.Spec.monadMap_trans
  Std.Do'.Spec.liftWith_StateT
  Std.Do'.Spec.liftWith_ReaderT
  Std.Do'.Spec.liftWith_ExceptT
  Std.Do'.Spec.liftWith_OptionT
  Std.Do'.Spec.liftWith_refl
  Std.Do'.Spec.liftWith_trans
  Std.Do'.Spec.restoreM_StateT
  Std.Do'.Spec.restoreM_ReaderT
  Std.Do'.Spec.restoreM_ExceptT
  Std.Do'.Spec.restoreM_OptionT
  Std.Do'.Spec.restoreM_refl

end Unary
end TacticInternals
end OracleComp.ProgramLogic
