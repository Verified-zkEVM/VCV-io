/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics
import VCVio.OracleComp.Constructions.Replicate

/-!
# Unary VCGen Tactic Examples

This file validates unary `wp` / `Triple` / probability tactics from
`VCVio.ProgramLogic.Tactics`: `vcstep`, `vcgen`, `by_hoare`, `exp_norm`,
as well as basic notation.
-/

open ENNReal OracleSpec OracleComp
open OracleComp.ProgramLogic
open OracleComp.ProgramLogic.Relational
open scoped OracleComp.ProgramLogic

universe u

variable {ι : Type u} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α β γ : Type}

/-! ## Notation examples -/

example (oa : OracleComp spec α) (f : α → OracleComp spec β) (post : β → ℝ≥0∞) :
    wp⟦oa >>= f⟧ post = wp⟦oa⟧ (fun u => wp⟦f u⟧ post) := by
  vcstep

example (oa : OracleComp spec α) :
    ⟪oa ~ oa | EqRel α⟫ := by
  rvcstep

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
    wp⟦(liftM (query t) : OracleComp spec (spec.Range t))⟧ post =
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
      evalDist (impl t) = evalDist (liftM (query t) : OracleComp spec (spec.Range t)))
    (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦simulateQ impl oa⟧ post = wp⟦oa⟧ post := by
  vcstep
  exact hImpl

/-! ## Registered `@[vcspec]` theorems -/

@[irreducible] def wrappedTrue : OracleComp spec Bool := pure true

@[local vcspec] theorem triple_wrappedTrue :
    ⦃1⦄ wrappedTrue (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  simpa [wrappedTrue] using
    (triple_pure (spec := spec) true (fun y => if y = true then 1 else 0))

example :
    ⦃1⦄ wrappedTrue (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  vcstep

@[irreducible] def wrappedTrueStep : OracleComp spec Bool := pure true

@[local vcspec] theorem triple_wrappedTrueStep (_haux : True) :
    ⦃1⦄ wrappedTrueStep (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  simpa [wrappedTrueStep] using
    (triple_pure (spec := spec) true (fun y => if y = true then 1 else 0))

example :
    ⦃1⦄ wrappedTrueStep (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  vcstep
  trivial

/--
`vcstep?` can get the specific path used to create a `vcstep` proof
example :
    ⦃1⦄ wrappedTrueStep (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  vcstep?
  trivial
-/

example :
    ⦃1⦄ wrappedTrueStep (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  vcstep with triple_wrappedTrueStep
  trivial

/-! ## `liftComp` -/

section LiftComp

variable {ι' : Type} {superSpec : OracleSpec ι'}
variable [superSpec.Fintype] [superSpec.Inhabited]
variable [h : spec ⊂ₒ superSpec] [LawfulSubSpec spec superSpec]

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦liftComp oa superSpec⟧ post = wp⟦oa⟧ post := by
  vcstep

end LiftComp

/-! ## `vcstep` on `Triple` goals -/

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {pre : ℝ≥0∞} {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (hoa : ⦃pre⦄ oa ⦃cut⦄)
    (hob : ∀ x, ⦃cut x⦄ f x ⦃post⦄) :
    ⦃pre⦄ (oa >>= f) ⦃post⦄ := by
  vcstep
  exact hob

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {pre : ℝ≥0∞} {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (hoa : ⦃pre⦄ oa ⦃cut⦄)
    (hob : ∀ x, ⦃cut x⦄ f x ⦃post⦄) :
    ⦃pre⦄ (oa >>= f) ⦃post⦄ := by
  vcstep as ⟨x⟩
  exact hob x

example (oa : OracleComp spec α) (f : α → OracleComp spec Bool)
    (h : ∀ x ∈ support oa, Pr[= true | f x] = 1) :
    ⦃1⦄ (do
      let x ← oa
      f x) ⦃fun y => if y = true then 1 else 0⦄ := by
  classical
  vcstep using (fun x => ⌜x ∈ support oa⌝)
  · simpa [propInd_eq_ite] using triple_support (oa := oa)
  · intro x
    by_cases hx : x ∈ support oa
    · simpa [propInd, hx] using triple_probOutput_eq_one (oa := f x) (x := true) (h := h x hx)
    · simpa [propInd, hx] using
        triple_zero (oa := f x) (post := fun y => if y = true then 1 else 0)

example (oa : OracleComp spec α) (n : ℕ) (pre : ℝ≥0∞) (post : List α → ℝ≥0∞)
    (h :
      pre ≤ wp⟦oa⟧ (fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs)))) :
    ⦃pre⦄ oa.replicate (n + 1) ⦃post⦄ := by
  vcstep
  exact h

example (x : α) (xs : List α) (f : α → OracleComp spec β)
    (pre : ℝ≥0∞) (post : List β → ℝ≥0∞)
    (h : pre ≤ wp⟦f x⟧ (fun y => wp⟦xs.mapM f⟧ (fun ys => post (y :: ys)))) :
    ⦃pre⦄ (x :: xs).mapM f ⦃post⦄ := by
  vcstep
  exact h

example (x : α) (xs : List α) (f : β → α → OracleComp spec β)
    (init : β) (pre : ℝ≥0∞) (post : β → ℝ≥0∞)
    (h : pre ≤ wp⟦f init x⟧ (fun s => wp⟦xs.foldlM f s⟧ post)) :
    ⦃pre⦄ (x :: xs).foldlM f init ⦃post⦄ := by
  vcstep
  exact h

/-! ## `vcgen` exhaustive driver -/

example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (h1 : ⦃1⦄ oa ⦃cut⦄) (h2 : ∀ x, ⦃cut x⦄ ob x ⦃post⦄) :
    ⦃1⦄ (oa >>= ob) ⦃post⦄ := by
  vcgen

/-
`vcgen?` can expand the construction of a `vcgen` proof
example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (h1 : ⦃1⦄ oa ⦃cut⦄) (h2 : ∀ x, ⦃cut x⦄ ob x ⦃post⦄) :
    ⦃1⦄ (oa >>= ob) ⦃post⦄ := by
  vcgen?
-/

example (x : α) (post : α → ℝ≥0∞) :
    ⦃post x⦄ (pure x : OracleComp spec α) ⦃post⦄ := by
  vcgen

example {oa : OracleComp spec α} {I : ℝ≥0∞} {n : ℕ}
    {pre : ℝ≥0∞} {post : List α → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ xs, I ≤ post xs)
    (hstep : ⦃I⦄ oa ⦃fun _ => I⦄) :
    ⦃pre⦄ oa.replicate n ⦃post⦄ := by
  vcstep inv I
  · exact hpre
  · intro xs; exact hpost xs
  · exact hstep

example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {oc : β → OracleComp spec γ}
    {cut1 : α → ℝ≥0∞} {cut2 : β → ℝ≥0∞} {post : γ → ℝ≥0∞}
    (h1 : ⦃1⦄ oa ⦃cut1⦄)
    (h2 : ∀ x, ⦃cut1 x⦄ ob x ⦃cut2⦄)
    (h3 : ∀ y, ⦃cut2 y⦄ oc y ⦃post⦄) :
    ⦃1⦄ (do
      let x ← oa
      let y ← ob x
      oc y) ⦃post⦄ := by
  vcgen

example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {post : β → ℝ≥0∞}
    (h : ⦃1⦄ oa ⦃fun x => wp⟦ob x⟧ post⦄) :
    ⦃1⦄ (oa >>= ob) ⦃post⦄ := by
  vcgen

example (c : Prop) [Decidable c] {oa ob : OracleComp spec α}
    {pre : ℝ≥0∞} {post : α → ℝ≥0∞}
    (ht : ⦃pre⦄ oa ⦃post⦄) (hf : ⦃pre⦄ ob ⦃post⦄) :
    ⦃pre⦄ (if c then oa else ob) ⦃post⦄ := by
  vcgen

example (n : ℕ) {oa : n > 0 → OracleComp spec α} {ob : ¬(n > 0) → OracleComp spec α}
    {pre : ℝ≥0∞} {post : α → ℝ≥0∞}
    (ht : ∀ h, ⦃pre⦄ oa h ⦃post⦄) (hf : ∀ h, ⦃pre⦄ ob h ⦃post⦄) :
    ⦃pre⦄ (dite (n > 0) oa ob) ⦃post⦄ := by
  vcstep
  · exact ht _
  · exact hf _

example {f : α → OracleComp spec β} {g : OracleComp spec β}
    (x : Option α) {pre : ℝ≥0∞} {post : β → ℝ≥0∞}
    (hsome : ∀ a, ⦃pre⦄ f a ⦃post⦄) (hnone : ⦃pre⦄ g ⦃post⦄) :
    ⦃pre⦄ (match x with | some a => f a | none => g) ⦃post⦄ := by
  vcgen

/-! ### Loop invariants -/

example {oa : OracleComp spec α} {I : ℝ≥0∞} {n : ℕ}
    (hstep : ⦃I⦄ oa ⦃fun _ => I⦄) :
    ⦃I⦄ oa.replicate n ⦃fun _ => I⦄ := by
  vcgen

example {σ : Type} {f : σ → α → OracleComp spec σ} {l : List α} {s₀ : σ}
    {I : σ → ℝ≥0∞}
    (hstep : ∀ s x, x ∈ l → ⦃I s⦄ f s x ⦃I⦄) :
    ⦃I s₀⦄ l.foldlM f s₀ ⦃I⦄ := by
  vcgen

example {f : α → OracleComp spec β} {l : List α} {I : ℝ≥0∞}
    (hstep : ∀ x, x ∈ l → ⦃I⦄ f x ⦃fun _ => I⦄) :
    ⦃I⦄ l.mapM f ⦃fun _ => I⦄ := by
  vcgen

/-! ### Probability goal lowering -/

example {oa : OracleComp spec α} {p : α → Prop} [DecidablePred p]
    (h : ⦃1⦄ oa ⦃fun x => ⌜p x⌝⦄) :
    Pr[p | oa] = 1 := by
  vcgen

example {oa : OracleComp spec α} {p : α → Prop} [DecidablePred p]
    (h : ⦃1⦄ oa ⦃fun x => ⌜p x⌝⦄) :
    1 = Pr[p | oa] := by
  vcgen

example {oa : OracleComp spec Bool}
    (h : ⦃1⦄ oa ⦃fun y => if y = true then 1 else 0⦄) :
    Pr[= true | oa] = 1 := by
  vcgen

/-! ### Probability equality (swap / congr) -/

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f : α → β → OracleComp spec γ} {z : γ} :
    Pr[= z | mx >>= fun a => my >>= fun b => f a b] =
    Pr[= z | my >>= fun b => mx >>= fun a => f a b] := by
  vcstep

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {y : β}
    (h : ∀ x ∈ support mx, Pr[= y | f x] = Pr[= y | g x]) :
    Pr[= y | mx >>= f] = Pr[= y | mx >>= g] := by
  vcstep rw congr
  exact h _ ‹_›

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr[q | f x] = Pr[q | g x]) :
    Pr[q | mx >>= f] = Pr[q | mx >>= g] := by
  vcstep rw congr'
  exact h _

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr[q | f x] = Pr[q | g x]) :
    Pr[q | mx >>= f] = Pr[q | mx >>= g] := by
  vcstep rw congr' as ⟨x⟩
  exact h x

/--
info: Try this:

  [apply] vcstep rw congr as ⟨x, hx⟩
-/
#guard_msgs in
example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr[q | f x] = Pr[q | g x]) :
    Pr[q | mx >>= f] = Pr[q | mx >>= g] := by
  vcstep?
  exact h x

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f g : α → β → OracleComp spec γ} {q : γ → Prop}
    (h : ∀ x y, Pr[q | f x y] = Pr[q | g x y]) :
    Pr[q | mx >>= fun x => my >>= fun y => f x y] =
    Pr[q | mx >>= fun x => my >>= fun y => g x y] := by
  vcstep rw congr' as ⟨x, y⟩
  exact h x y

example : ⌜(True : Prop)⌝ * ⌜(True : Prop)⌝ = (1 : ℝ≥0∞) := by
  exp_norm

/-! ### Probability lower bounds -/

example {oa : OracleComp spec α} {p : α → Prop} [DecidablePred p] {r : ℝ≥0∞}
    (h : ⦃r⦄ oa ⦃fun x => ⌜p x⌝⦄) :
    r ≤ Pr[p | oa] := by
  vcstep
  exact h

example {oa : OracleComp spec α} [DecidableEq α] {x : α} {r : ℝ≥0∞}
    (h : ⦃r⦄ oa ⦃fun y => if y = x then 1 else 0⦄) :
    Pr[= x | oa] ≥ r := by
  vcstep
  exact h

example (c : Prop) [Decidable c] (oa ob : OracleComp spec α)
    (p : α → Prop) [DecidablePred p] :
    Pr[p | if c then oa else ob] =
      if c then wp⟦oa⟧ (fun x => ⌜p x⌝) else wp⟦ob⟧ (fun x => ⌜p x⌝) := by
  vcstep

/-! ### `by_hoare` -/

example (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    Pr[p | oa] = wp⟦oa⟧ (fun x => if p x then 1 else 0) := by
  by_hoare

example (oa : OracleComp spec α) [DecidableEq α] (x : α) :
    Pr[= x | oa] = wp⟦oa⟧ (fun y => if y = x then 1 else 0) := by
  by_hoare

/--
info: Try this:

  [apply] vcstep
---
info: Planner note: continuing in raw `wp` mode
-/
#guard_msgs in
example (c : Prop) [Decidable c] (oa ob : OracleComp spec α)
    (post : α → ℝ≥0∞) :
    wp⟦if c then oa else ob⟧ post =
      if c then wp⟦oa⟧ post else wp⟦ob⟧ post := by
  vcstep?

/-! ### `vcgen using cut` and `vcgen inv I` driver variants -/

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {g : β → OracleComp spec γ}
    {cut : α → ℝ≥0∞} {cut2 : β → ℝ≥0∞} {post : γ → ℝ≥0∞}
    (hoa : ⦃1⦄ oa ⦃cut⦄)
    (hf : ∀ x, ⦃cut x⦄ f x ⦃cut2⦄)
    (hg : ∀ y, ⦃cut2 y⦄ g y ⦃post⦄) :
    ⦃1⦄ (do let x ← oa; let y ← f x; g y) ⦃post⦄ := by
  vcstep using cut
  · exact hoa
  · intro x
    vcgen using cut2

example {oa : OracleComp spec α} {I : ℝ≥0∞} {n : ℕ}
    {pre : ℝ≥0∞} {post : List α → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ xs, I ≤ post xs)
    (hstep : ⦃I⦄ oa ⦃fun _ => I⦄) :
    ⦃pre⦄ oa.replicate n ⦃post⦄ := by
  vcgen inv I

/-! ### Support-cut synthesis -/

example (oa : OracleComp spec α) (f : α → OracleComp spec Bool)
    (h : ∀ x ∈ support oa, Pr[= true | f x] = 1) :
    ⦃1⦄ (do let x ← oa; f x) ⦃fun y => if y = true then 1 else 0⦄ := by
  vcstep
  intro x
  by_cases hx : x ∈ support oa
  · simpa [propInd, hx] using triple_probOutput_eq_one (oa := f x) (x := true) (h := h x hx)
  · simpa [propInd, hx] using
      triple_zero (oa := f x) (post := fun y => if y = true then 1 else 0)
