/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import VCVio.ProgramLogic.Tactics.Unary
import VCVio.OracleComp.Constructions.Replicate

/-!
# Unary Triple / VCGen Examples

This file validates unary `Triple` stepping and structural `vcgen` decomposition.
-/

open ENNReal OracleSpec OracleComp
open Lean.Order
open OracleComp.ProgramLogic
open scoped OracleComp.ProgramLogic

universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β γ : Type}

/-! ## `vcstep` on `Triple` goals -/

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {pre : ℝ≥0∞} {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (hoa : ⦃ pre ⦄ oa ⦃ cut ⦄)
    (hob : ∀ x, ⦃ cut x ⦄ f x ⦃ post ⦄) :
    ⦃ pre ⦄ (oa >>= f) ⦃ post ⦄ := by
  vcstep
  exact hob

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {pre : ℝ≥0∞} {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (hoa : ⦃ pre ⦄ oa ⦃ cut ⦄)
    (hob : ∀ x, ⦃ cut x ⦄ f x ⦃ post ⦄) :
    ⦃ pre ⦄ (oa >>= f) ⦃ post ⦄ := by
  vcstep as ⟨x⟩
  exact hob x

example (oa : OracleComp spec α) (f : α → OracleComp spec Bool)
    (h : ∀ x ∈ support oa, Pr[= true | f x] = 1) :
    ⦃ 1 ⦄ (do
      let x ← oa
      f x) ⦃ fun y => if y = true then 1 else 0 ⦄ := by
  classical
  vcstep using (fun x => 𝟙⟦x ∈ support oa⟧)
  · simpa [propInd_eq_ite] using triple_support (oa := oa)
  · intro x
    by_cases hx : x ∈ support oa
    · simpa [propInd, hx] using triple_probOutput_eq_one (oa := f x) (x := true) (h := h x hx)
    · simpa [propInd, hx] using
        triple_zero (oa := f x) (post := fun y => if y = true then 1 else 0)

example (oa : OracleComp spec α) (n : ℕ) (pre : ℝ≥0∞) (post : List α → ℝ≥0∞)
    (h :
      pre ≤ wp⟦oa⟧(fun x => wp⟦oa.replicate n⟧(fun xs => post (x :: xs)))) :
    ⦃ pre ⦄ oa.replicate (n + 1) ⦃ post ⦄ := by
  vcgen

example (x : α) (xs : List α) (f : α → OracleComp spec β)
    (pre : ℝ≥0∞) (post : List β → ℝ≥0∞)
    (h : pre ≤ wp⟦f x⟧(fun y => wp⟦xs.mapM f⟧(fun ys => post (y :: ys)))) :
    ⦃ pre ⦄ (x :: xs).mapM f ⦃ post ⦄ := by
  vcgen

example (x : α) (xs : List α) (f : β → α → OracleComp spec β)
    (init : β) (pre : ℝ≥0∞) (post : β → ℝ≥0∞)
    (h : pre ≤ wp⟦f init x⟧(fun s => wp⟦xs.foldlM f s⟧post)) :
    ⦃ pre ⦄ (x :: xs).foldlM f init ⦃ post ⦄ := by
  vcgen

/-! ## `vcgen` exhaustive driver -/

example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (h1 : ⦃ 1 ⦄ oa ⦃ cut ⦄) (h2 : ∀ x, ⦃ cut x ⦄ ob x ⦃ post ⦄) :
    ⦃ 1 ⦄ (oa >>= ob) ⦃ post ⦄ := by
  vcgen

/-
These replay guards are regression sensors for VCVio-native suggestions.
The exact scripts below are allowed to improve as the planner evolves.
-/
/--
info: Try this:

  [apply] all_goals first | vcstep as ⟨x⟩ | skip
  all_goals first | vcstep | skip
-/
#guard_msgs in
example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (h1 : ⦃ 1 ⦄ oa ⦃ cut ⦄) (h2 : ∀ x, ⦃ cut x ⦄ ob x ⦃ post ⦄) :
    ⦃ 1 ⦄ (oa >>= ob) ⦃ post ⦄ := by
  vcgen?

example (x : α) (post : α → ℝ≥0∞) :
    ⦃ post x ⦄ (pure x : OracleComp spec α) ⦃ post ⦄ := by
  vcgen

example {oa : OracleComp spec α} {I : ℝ≥0∞} {n : ℕ}
    {pre : ℝ≥0∞} {post : List α → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ xs, I ≤ post xs)
    (hstep : ⦃ I ⦄ oa ⦃ fun _ => I ⦄) :
    ⦃ pre ⦄ oa.replicate n ⦃ post ⦄ := by
  vcstep inv I
  · exact hpre
  · intro xs; exact hpost xs
  · exact hstep

example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {oc : β → OracleComp spec γ}
    {cut1 : α → ℝ≥0∞} {cut2 : β → ℝ≥0∞} {post : γ → ℝ≥0∞}
    (h1 : ⦃ 1 ⦄ oa ⦃ cut1 ⦄)
    (h2 : ∀ x, ⦃ cut1 x ⦄ ob x ⦃ cut2 ⦄)
    (h3 : ∀ y, ⦃ cut2 y ⦄ oc y ⦃ post ⦄) :
    ⦃ 1 ⦄ (do
      let x ← oa
      let y ← ob x
      oc y) ⦃ post ⦄ := by
  vcgen

example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {post : β → ℝ≥0∞}
    (h : ⦃ 1 ⦄ oa ⦃ fun x => wp⟦ob x⟧post ⦄) :
    ⦃ 1 ⦄ (oa >>= ob) ⦃ post ⦄ := by
  vcgen

example (c : Prop) [Decidable c] {oa ob : OracleComp spec α}
    {pre : ℝ≥0∞} {post : α → ℝ≥0∞}
    (ht : ⦃ pre ⦄ oa ⦃ post ⦄) (hf : ⦃ pre ⦄ ob ⦃ post ⦄) :
    ⦃ pre ⦄ (if c then oa else ob) ⦃ post ⦄ := by
  vcgen

example (n : ℕ) {oa : n > 0 → OracleComp spec α} {ob : ¬(n > 0) → OracleComp spec α}
    {pre : ℝ≥0∞} {post : α → ℝ≥0∞}
    (ht : ∀ h, ⦃ pre ⦄ oa h ⦃ post ⦄) (hf : ∀ h, ⦃ pre ⦄ ob h ⦃ post ⦄) :
    ⦃ pre ⦄ (dite (n > 0) oa ob) ⦃ post ⦄ := by
  vcstep
  · exact ht _
  · exact hf _

example {f : α → OracleComp spec β} {g : OracleComp spec β}
    (x : Option α) {pre : ℝ≥0∞} {post : β → ℝ≥0∞}
    (hsome : ∀ a, ⦃ pre ⦄ f a ⦃ post ⦄) (hnone : ⦃ pre ⦄ g ⦃ post ⦄) :
    ⦃ pre ⦄ (match x with | some a => f a | none => g) ⦃ post ⦄ := by
  vcgen

/-! ### Loop invariants -/

example {oa : OracleComp spec α} {I : ℝ≥0∞} {n : ℕ}
    (hstep : ⦃ I ⦄ oa ⦃ fun _ => I ⦄) :
    ⦃ I ⦄ oa.replicate n ⦃ fun _ => I ⦄ := by
  vcgen

example {σ : Type} {f : σ → α → OracleComp spec σ} {l : List α} {s₀ : σ}
    {I : σ → ℝ≥0∞}
    (hstep : ∀ s x, x ∈ l → ⦃ I s ⦄ f s x ⦃ I ⦄) :
    ⦃ I s₀ ⦄ l.foldlM f s₀ ⦃ I ⦄ := by
  vcgen

example {f : α → OracleComp spec β} {l : List α} {I : ℝ≥0∞}
    (hstep : ∀ x, x ∈ l → ⦃ I ⦄ f x ⦃ fun _ => I ⦄) :
    ⦃ I ⦄ l.mapM f ⦃ fun _ => I ⦄ := by
  vcgen

/-! ### `vcgen using cut` and `vcgen inv I` driver variants -/

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {g : β → OracleComp spec γ} {pre : ℝ≥0∞}
    {cut : α → ℝ≥0∞} {cut2 : β → ℝ≥0∞} {post : γ → ℝ≥0∞}
    (hoa : ⦃ pre ⦄ oa ⦃ cut ⦄)
    (hf : ∀ x, ⦃ cut x ⦄ f x ⦃ cut2 ⦄)
    (hg : ∀ y, ⦃ cut2 y ⦄ g y ⦃ post ⦄) :
    ⦃ pre ⦄ (do let x ← oa; let y ← f x; g y) ⦃ post ⦄ := by
  vcstep using cut
  · exact hoa
  · intro x
    vcgen using cut2

example {oa : OracleComp spec α} {I : ℝ≥0∞} {n : ℕ}
    {pre : ℝ≥0∞} {post : List α → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ xs, I ≤ post xs)
    (hstep : ⦃ I ⦄ oa ⦃ fun _ => I ⦄) :
    ⦃ pre ⦄ oa.replicate n ⦃ post ⦄ := by
  vcgen inv I
