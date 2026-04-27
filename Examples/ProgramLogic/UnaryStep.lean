/- 
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics.Unary
import VCVio.ProgramLogic.Unary.SimulateQ
import VCVio.OracleComp.Constructions.Replicate
import VCVio.OracleComp.Coercions.SubSpec

/-!
# Unary VCGen Step Examples

This file validates one-step unary tactic behavior for raw `wp` goals,
registered `@[vcspec]` hints, and `liftComp`.
-/

open ENNReal OracleSpec OracleComp
open Lean.Order
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic

universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β : Type}

/-! ## Notation examples -/

example (oa : OracleComp spec α) (f : α → OracleComp spec β) (post : β → ℝ≥0∞) :
    wp⟦oa >>= f⟧ post = wp⟦oa⟧ (fun u => wp⟦f u⟧ post) := by
  vcstep

/-! ## `vcstep` on raw `wp` goals -/

example (x : α) (post : α → ℝ≥0∞) :
    wp⟦(pure x : OracleComp spec α)⟧ post = post x := by
  vcstep

example (c : Prop) [Decidable c] (a b : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦if c then a else b⟧ post = if c then wp⟦a⟧ post else wp⟦b⟧ post := by
  vcstep

example (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    wp⟦oa.replicate (n + 1)⟧ post =
      wp⟦oa⟧ (fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs))) := by
  vcstep

example (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp⟦(x :: xs).mapM f⟧ post =
      wp⟦f x⟧ (fun y => wp⟦xs.mapM f⟧ (fun ys => post (y :: ys))) := by
  vcstep

example (x : α) (xs : List α) (f : β → α → OracleComp spec β)
    (init : β) (post : β → ℝ≥0∞) :
    wp⟦(x :: xs).foldlM f init⟧ post =
      wp⟦f init x⟧ (fun s => wp⟦xs.foldlM f s⟧ post) := by
  vcstep

example (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp⟦(query t : OracleComp spec (spec.Range t))⟧ post =
      ∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u := by
  vcstep

example (c : Prop) [Decidable c]
    (a : c → OracleComp spec α) (b : ¬c → OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦dite c a b⟧ post = if h : c then wp⟦a h⟧ post else wp⟦b h⟧ post := by
  vcstep

example [SampleableType α] (post : α → ℝ≥0∞) :
    wp⟦($ᵗ α : ProbComp α)⟧ post =
      ∑' u : α, Pr[= u | ($ᵗ α : ProbComp α)] * post u := by
  vcstep

example (f : α → β) (oa : OracleComp spec α) (post : β → ℝ≥0∞) :
    wp⟦f <$> oa⟧ post = wp⟦oa⟧ (post ∘ f) := by
  vcstep

example (impl : QueryImpl spec (OracleComp spec))
    (hImpl : ∀ (t : spec.Domain),
      evalDist (impl t) = evalDist (query t : OracleComp spec (spec.Range t)))
    (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦simulateQ impl oa⟧ post = wp⟦oa⟧ post := by
  simpa using OracleComp.ProgramLogic.wp_simulateQ_eq impl hImpl oa post

/-! ## Registered `@[vcspec]` theorems -/

@[irreducible] def wrappedTrue : OracleComp spec Bool := pure true

@[local vcspec] theorem triple_wrappedTrue :
    Triple 1 (wrappedTrue (spec := spec)) (fun y => if y = true then 1 else 0) := by
  simpa [wrappedTrue] using
    (triple_pure (spec := spec) true (fun y => if y = true then 1 else 0))

example :
    ⦃ (1 : ℝ≥0∞) ⦄ (wrappedTrue (spec := spec))
      ⦃ fun y => if y = true then (1 : ℝ≥0∞) else 0 ⦄ := by
  exact triple_wrappedTrue (spec := spec)

example :
    ⦃ (1 : ℝ≥0∞) ⦄ (wrappedTrue (spec := spec)) ⦃ fun _ => (1 : ℝ≥0∞) ⦄ := by
  vcstep

@[local vcspec] theorem stdDoTriple_wrappedTrue :
    Std.Do'.Triple (1 : ℝ≥0∞) (wrappedTrue (spec := spec))
      (fun y => if y = true then (1 : ℝ≥0∞) else 0) epost⟨⟩ := by
  exact triple_wrappedTrue (spec := spec)

example :
    ⦃ (1 : ℝ≥0∞) ⦄ (wrappedTrue (spec := spec)) ⦃ fun _ => (1 : ℝ≥0∞) ⦄ := by
  vcstep with stdDoTriple_wrappedTrue

example :
    Std.Do'.Triple (1 : ℝ≥0∞) (wrappedTrue (spec := spec))
      (fun _ => (1 : ℝ≥0∞)) epost⟨⟩ := by
  vcstep

@[irreducible] def wrappedTrueStep : OracleComp spec Bool := pure true

@[local vcspec] theorem triple_wrappedTrueStep (_haux : True) :
    Triple 1 (wrappedTrueStep (spec := spec)) (fun y => if y = true then 1 else 0) := by
  simpa [wrappedTrueStep] using
    (triple_pure (spec := spec) true (fun y => if y = true then 1 else 0))

example :
    ⦃ (1 : ℝ≥0∞) ⦄ (wrappedTrueStep (spec := spec))
      ⦃ fun y => if y = true then (1 : ℝ≥0∞) else 0 ⦄ := by
  exact triple_wrappedTrueStep (spec := spec) trivial

/--
`vcstep?` can get the specific path used to create a `vcstep` proof
example :
    ⦃ 1 ⦄ wrappedTrueStep (spec := spec) ⦃ fun y => if y = true then 1 else 0 ⦄ := by
  vcstep?
  trivial
-/
example :
    ⦃ 1 ⦄ wrappedTrueStep (spec := spec) ⦃ fun y => if y = true then 1 else 0 ⦄ := by
  vcstep with triple_wrappedTrueStep
  trivial

/-! ## `liftComp` -/

section LiftComp

variable {ι' : Type} {superSpec : OracleSpec ι'}
variable [superSpec.Fintype] [superSpec.Inhabited]
variable [h : spec ⊂ₒ superSpec] [LawfulSubSpec spec superSpec]

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦liftComp oa superSpec⟧ post = wp⟦oa⟧ post := by
  simpa using OracleComp.ProgramLogic.wp_liftComp
    (spec := spec) (superSpec := superSpec) oa post

end LiftComp
