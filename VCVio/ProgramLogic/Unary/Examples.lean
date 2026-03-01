/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Unary.HoareTriple

/-!
# Examples for quantitative `OracleComp` triples
-/

open ENNReal

universe u

namespace OracleComp.ProgramLogic

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β : Type}

example (x : α) (post : α → ℝ≥0∞) :
    wp (spec := spec) (pure x) post = post x :=
  wp_pure (spec := spec) x post

example (pre : ℝ≥0∞) (oa : OracleComp spec α) (ob : α → OracleComp spec β)
    (cut : α → ℝ≥0∞) (post : β → ℝ≥0∞)
    (hoa : Triple (spec := spec) pre oa cut)
    (hob : ∀ x, Triple (cut x) (ob x) post) :
    Triple pre (oa >>= ob) post :=
  triple_bind (spec := spec) hoa hob

example (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    Pr[p | oa] = wp oa (fun x => if p x then 1 else 0) :=
  probEvent_eq_wp_indicator (spec := spec) oa p

end OracleComp.ProgramLogic

namespace MAlgOrdered

open MAlgOrdered

universe v

variable {m : Type u → Type v} {L : Type u}
variable [Monad m] [LawfulMonad m] [CompleteLattice L] [MAlgOrdered m L]
variable {α β σ ρ ε : Type u}

example (x : StateT σ m α) (f : α → StateT σ m β) (post : β → σ → L) :
    MAlgOrdered.wp (m := StateT σ m) (l := σ → L) (x >>= f) post =
      MAlgOrdered.wp (m := StateT σ m) (l := σ → L) x
        (fun a => MAlgOrdered.wp (m := StateT σ m) (l := σ → L) (f a) post) := by
  simpa using (MAlgOrdered.wp_bind (m := StateT σ m) (l := σ → L) x f post)

example (x : ReaderT ρ m α) (f : α → ReaderT ρ m β) (post : β → ρ → L) :
    MAlgOrdered.wp (m := ReaderT ρ m) (l := ρ → L) (x >>= f) post =
      MAlgOrdered.wp (m := ReaderT ρ m) (l := ρ → L) x
        (fun a => MAlgOrdered.wp (m := ReaderT ρ m) (l := ρ → L) (f a) post) := by
  simpa using (MAlgOrdered.wp_bind (m := ReaderT ρ m) (l := ρ → L) x f post)

example (x : ExceptT ε m α) (f : α → ExceptT ε m β) (post : β → L) :
    MAlgOrdered.wp (m := ExceptT ε m) (l := L) (x >>= f) post =
      MAlgOrdered.wp (m := ExceptT ε m) (l := L) x
        (fun a => MAlgOrdered.wp (m := ExceptT ε m) (l := L) (f a) post) := by
  simpa using (MAlgOrdered.wp_bind (m := ExceptT ε m) (l := L) x f post)

end MAlgOrdered
