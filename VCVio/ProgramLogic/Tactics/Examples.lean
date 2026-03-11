/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.ProgramLogic.Tactics
import VCVio.OracleComp.Constructions.Replicate

/-!
# Examples and Tests for VCGen-Style Tactics

This file validates the user-facing tactic surface imported from
`VCVio.ProgramLogic.Tactics`.
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
  wp_step

example (oa : OracleComp spec α) :
    ⟪oa ~ oa | EqRel α⟫ := by
  rvcgen_step

/-! ## Unary examples -/

section Unary

example (x : α) (post : α → ℝ≥0∞) :
    wp⟦(pure x : OracleComp spec α)⟧ post = post x := by
  wp_step

example (c : Prop) [Decidable c] (a b : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦if c then a else b⟧ post = if c then wp⟦a⟧ post else wp⟦b⟧ post := by
  wp_step

example (oa : OracleComp spec α) (n : ℕ) (post : List α → ℝ≥0∞) :
    wp⟦oa.replicate (n + 1)⟧ post =
      wp⟦oa⟧ (fun x => wp⟦oa.replicate n⟧ (fun xs => post (x :: xs))) := by
  wp_step

example (x : α) (xs : List α) (f : α → OracleComp spec β) (post : List β → ℝ≥0∞) :
    wp⟦(x :: xs).mapM f⟧ post =
      wp⟦f x⟧ (fun y => wp⟦xs.mapM f⟧ (fun ys => post (y :: ys))) := by
  wp_step

example (x : α) (xs : List α) (f : β → α → OracleComp spec β)
    (init : β) (post : β → ℝ≥0∞) :
    wp⟦(x :: xs).foldlM f init⟧ post =
      wp⟦f init x⟧ (fun s => wp⟦xs.foldlM f s⟧ post) := by
  wp_step

example (t : spec.Domain) (post : spec.Range t → ℝ≥0∞) :
    wp⟦(liftM (query t) : OracleComp spec (spec.Range t))⟧ post =
      ∑' u : spec.Range t, (1 / Fintype.card (spec.Range t) : ℝ≥0∞) * post u := by
  wp_step

example (c : Prop) [Decidable c]
    (a : c → OracleComp spec α) (b : ¬c → OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦dite c a b⟧ post = if h : c then wp⟦a h⟧ post else wp⟦b h⟧ post := by
  wp_step

example [SampleableType α] (post : α → ℝ≥0∞) :
    wp⟦($ᵗ α : ProbComp α)⟧ post =
      ∑' u : α, Pr[= u | ($ᵗ α : ProbComp α)] * post u := by
  wp_step

example (f : α → β) (oa : OracleComp spec α) (post : β → ℝ≥0∞) :
    wp⟦f <$> oa⟧ post = wp⟦oa⟧ (post ∘ f) := by
  wp_step

example (impl : QueryImpl spec (OracleComp spec))
    (hImpl : ∀ (t : spec.Domain),
      evalDist (impl t) = evalDist (liftM (query t) : OracleComp spec (spec.Range t)))
    (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦simulateQ impl oa⟧ post = wp⟦oa⟧ post := by
  wp_step
  exact hImpl

@[irreducible] def wrappedTrue : OracleComp spec Bool := pure true

@[local vcgen] theorem triple_wrappedTrue :
    ⦃1⦄ wrappedTrue (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  simpa [wrappedTrue] using
    (triple_pure (spec := spec) true (fun y => if y = true then 1 else 0))

example :
    ⦃1⦄ wrappedTrue (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  qvcgen_step

@[irreducible] def wrappedTrueStep : OracleComp spec Bool := pure true

@[local vcgen] theorem triple_wrappedTrueStep (_haux : True) :
    ⦃1⦄ wrappedTrueStep (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  simpa [wrappedTrueStep] using
    (triple_pure (spec := spec) true (fun y => if y = true then 1 else 0))

example :
    ⦃1⦄ wrappedTrueStep (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  qvcgen_step
  trivial

example :
    ⦃1⦄ wrappedTrueStep (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  qvcgen_step?
  trivial

example :
    ⦃1⦄ wrappedTrueStep (spec := spec) ⦃fun y => if y = true then 1 else 0⦄ := by
  qvcgen_step with triple_wrappedTrueStep
  trivial

section LiftComp

variable {ι' : Type} {superSpec : OracleSpec ι'}
variable [superSpec.Fintype] [superSpec.Inhabited]
variable [h : spec ⊂ₒ superSpec] [LawfulSubSpec spec superSpec]

example (oa : OracleComp spec α) (post : α → ℝ≥0∞) :
    wp⟦liftComp oa superSpec⟧ post = wp⟦oa⟧ post := by
  wp_step

end LiftComp

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {pre : ℝ≥0∞} {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (hoa : ⦃pre⦄ oa ⦃cut⦄)
    (hob : ∀ x, ⦃cut x⦄ f x ⦃post⦄) :
    ⦃pre⦄ (oa >>= f) ⦃post⦄ := by
  qvcgen_step
  exact hob

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {pre : ℝ≥0∞} {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (hoa : ⦃pre⦄ oa ⦃cut⦄)
    (hob : ∀ x, ⦃cut x⦄ f x ⦃post⦄) :
    ⦃pre⦄ (oa >>= f) ⦃post⦄ := by
  qvcgen_step as ⟨x⟩
  exact hob x

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {pre : ℝ≥0∞} {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (hoa : ⦃pre⦄ oa ⦃cut⦄)
    (hob : ∀ x, ⦃cut x⦄ f x ⦃post⦄) :
    ⦃pre⦄ (oa >>= f) ⦃post⦄ := by
  qvcgen_step?
  exact hob x

example (oa : OracleComp spec α) (f : α → OracleComp spec Bool)
    (h : ∀ x ∈ support oa, Pr[= true | f x] = 1) :
    ⦃1⦄ (do
      let x ← oa
      f x) ⦃fun y => if y = true then 1 else 0⦄ := by
  classical
  qvcgen_step using (fun x => ⌜x ∈ support oa⌝)
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
  qvcgen_step
  exact h

example (x : α) (xs : List α) (f : α → OracleComp spec β)
    (pre : ℝ≥0∞) (post : List β → ℝ≥0∞)
    (h : pre ≤ wp⟦f x⟧ (fun y => wp⟦xs.mapM f⟧ (fun ys => post (y :: ys)))) :
    ⦃pre⦄ (x :: xs).mapM f ⦃post⦄ := by
  qvcgen_step
  exact h

example (x : α) (xs : List α) (f : β → α → OracleComp spec β)
    (init : β) (pre : ℝ≥0∞) (post : β → ℝ≥0∞)
    (h : pre ≤ wp⟦f init x⟧ (fun s => wp⟦xs.foldlM f s⟧ post)) :
    ⦃pre⦄ (x :: xs).foldlM f init ⦃post⦄ := by
  qvcgen_step
  exact h

example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (h1 : ⦃1⦄ oa ⦃cut⦄) (h2 : ∀ x, ⦃cut x⦄ ob x ⦃post⦄) :
    ⦃1⦄ (oa >>= ob) ⦃post⦄ := by
  qvcgen

example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {cut : α → ℝ≥0∞} {post : β → ℝ≥0∞}
    (h1 : ⦃1⦄ oa ⦃cut⦄) (h2 : ∀ x, ⦃cut x⦄ ob x ⦃post⦄) :
    ⦃1⦄ (oa >>= ob) ⦃post⦄ := by
  qvcgen?

example (x : α) (post : α → ℝ≥0∞) :
    ⦃post x⦄ (pure x : OracleComp spec α) ⦃post⦄ := by
  qvcgen

example {oa : OracleComp spec α} {I : ℝ≥0∞} {n : ℕ}
    {pre : ℝ≥0∞} {post : List α → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ xs, I ≤ post xs)
    (hstep : ⦃I⦄ oa ⦃fun _ => I⦄) :
    ⦃pre⦄ oa.replicate n ⦃post⦄ := by
  qvcgen_step inv I
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
  qvcgen

example {oa : OracleComp spec α} {ob : α → OracleComp spec β}
    {post : β → ℝ≥0∞}
    (h : ⦃1⦄ oa ⦃fun x => wp⟦ob x⟧ post⦄) :
    ⦃1⦄ (oa >>= ob) ⦃post⦄ := by
  qvcgen

example (c : Prop) [Decidable c] {oa ob : OracleComp spec α}
    {pre : ℝ≥0∞} {post : α → ℝ≥0∞}
    (ht : ⦃pre⦄ oa ⦃post⦄) (hf : ⦃pre⦄ ob ⦃post⦄) :
    ⦃pre⦄ (if c then oa else ob) ⦃post⦄ := by
  qvcgen

example (n : ℕ) {oa : n > 0 → OracleComp spec α} {ob : ¬(n > 0) → OracleComp spec α}
    {pre : ℝ≥0∞} {post : α → ℝ≥0∞}
    (ht : ∀ h, ⦃pre⦄ oa h ⦃post⦄) (hf : ∀ h, ⦃pre⦄ ob h ⦃post⦄) :
    ⦃pre⦄ (dite (n > 0) oa ob) ⦃post⦄ := by
  qvcgen

example {f : α → OracleComp spec β} {g : OracleComp spec β}
    (x : Option α) {pre : ℝ≥0∞} {post : β → ℝ≥0∞}
    (hsome : ∀ a, ⦃pre⦄ f a ⦃post⦄) (hnone : ⦃pre⦄ g ⦃post⦄) :
    ⦃pre⦄ (match x with | some a => f a | none => g) ⦃post⦄ := by
  qvcgen

example {oa : OracleComp spec α} {I : ℝ≥0∞} {n : ℕ}
    (hstep : ⦃I⦄ oa ⦃fun _ => I⦄) :
    ⦃I⦄ oa.replicate n ⦃fun _ => I⦄ := by
  qvcgen

example {σ : Type} {f : σ → α → OracleComp spec σ} {l : List α} {s₀ : σ}
    {I : σ → ℝ≥0∞}
    (hstep : ∀ s x, x ∈ l → ⦃I s⦄ f s x ⦃I⦄) :
    ⦃I s₀⦄ l.foldlM f s₀ ⦃I⦄ := by
  qvcgen

example {f : α → OracleComp spec β} {l : List α} {I : ℝ≥0∞}
    (hstep : ∀ x, x ∈ l → ⦃I⦄ f x ⦃fun _ => I⦄) :
    ⦃I⦄ l.mapM f ⦃fun _ => I⦄ := by
  qvcgen

example {oa : OracleComp spec α} {p : α → Prop} [DecidablePred p]
    (h : ⦃1⦄ oa ⦃fun x => ⌜p x⌝⦄) :
    Pr[p | oa] = 1 := by
  qvcgen

example {oa : OracleComp spec α} {p : α → Prop} [DecidablePred p]
    (h : ⦃1⦄ oa ⦃fun x => ⌜p x⌝⦄) :
    1 = Pr[p | oa] := by
  qvcgen

example {oa : OracleComp spec Bool}
    (h : ⦃1⦄ oa ⦃fun y => if y = true then 1 else 0⦄) :
    Pr[= true | oa] = 1 := by
  qvcgen

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f : α → β → OracleComp spec γ} {z : γ} :
    Pr[= z | mx >>= fun a => my >>= fun b => f a b] =
    Pr[= z | my >>= fun b => mx >>= fun a => f a b] := by
  qvcgen_step

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {y : β}
    (h : ∀ x ∈ support mx, Pr[= y | f x] = Pr[= y | g x]) :
    Pr[= y | mx >>= f] = Pr[= y | mx >>= g] := by
  qvcgen_step rw congr
  exact h _ ‹_›

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr[q | f x] = Pr[q | g x]) :
    Pr[q | mx >>= f] = Pr[q | mx >>= g] := by
  qvcgen_step rw congr'
  exact h _

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr[q | f x] = Pr[q | g x]) :
    Pr[q | mx >>= f] = Pr[q | mx >>= g] := by
  qvcgen_step rw congr' as ⟨x⟩
  exact h x

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr[q | f x] = Pr[q | g x]) :
    Pr[q | mx >>= f] = Pr[q | mx >>= g] := by
  qvcgen_step?
  exact h x

example : ⌜(True : Prop)⌝ * ⌜(True : Prop)⌝ = (1 : ℝ≥0∞) := by
  exp_norm

example (oa : OracleComp spec α) (p : α → Prop) [DecidablePred p] :
    Pr[p | oa] = wp⟦oa⟧ (fun x => if p x then 1 else 0) := by
  by_hoare

example (oa : OracleComp spec α) [DecidableEq α] (x : α) :
    Pr[= x | oa] = wp⟦oa⟧ (fun y => if y = x then 1 else 0) := by
  by_hoare

/-! ### `qvcgen using cut` and `qvcgen inv I` driver variants -/

example {oa : OracleComp spec α} {f : α → OracleComp spec β}
    {g : β → OracleComp spec γ}
    {cut : α → ℝ≥0∞} {cut2 : β → ℝ≥0∞} {post : γ → ℝ≥0∞}
    (hoa : ⦃1⦄ oa ⦃cut⦄)
    (hf : ∀ x, ⦃cut x⦄ f x ⦃cut2⦄)
    (hg : ∀ y, ⦃cut2 y⦄ g y ⦃post⦄) :
    ⦃1⦄ (do let x ← oa; let y ← f x; g y) ⦃post⦄ := by
  qvcgen using cut

example {oa : OracleComp spec α} {I : ℝ≥0∞} {n : ℕ}
    {pre : ℝ≥0∞} {post : List α → ℝ≥0∞}
    (hpre : pre ≤ I) (hpost : ∀ xs, I ≤ post xs)
    (hstep : ⦃I⦄ oa ⦃fun _ => I⦄) :
    ⦃pre⦄ oa.replicate n ⦃post⦄ := by
  qvcgen inv I

/-! ### Support-cut synthesis -/

example (oa : OracleComp spec α) (f : α → OracleComp spec Bool)
    (h : ∀ x ∈ support oa, Pr[= true | f x] = 1) :
    ⦃1⦄ (do let x ← oa; f x) ⦃fun y => if y = true then 1 else 0⦄ := by
  qvcgen_step
  intro x
  by_cases hx : x ∈ support oa
  · simpa [propInd, hx] using triple_probOutput_eq_one (oa := f x) (x := true) (h := h x hx)
  · simpa [propInd, hx] using
      triple_zero (oa := f x) (post := fun y => if y = true then 1 else 0)

end Unary

/-! ## Relational VCGen examples -/

section Relational

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ f₂ : α → OracleComp spec β}
    (hoa : ⟪oa₁ ~ oa₂ | EqRel α⟫)
    (hf : ∀ a₁ a₂, EqRel α a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | EqRel β⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | EqRel β⟫ := by
  rvcgen_step
  exact hoa

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcgen_step using S
  · exact hoa

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcgen_step using S
  · exact hoa

example (f : α → OracleComp spec β) :
    ∀ x, ⟪f x ~ f x | EqRel β⟫ := by
  rvcgen_step as ⟨x⟩
  rvcgen_step

example (t : spec.Domain) :
    ⟪(liftM (query t) : OracleComp spec (spec.Range t))
     ~ (liftM (query t) : OracleComp spec (spec.Range t))
     | EqRel (spec.Range t)⟫ := by
  rvcgen_step

example [SampleableType α]
    {f : α → α} (hf : Function.Bijective f) :
    ⟪($ᵗ α : ProbComp α) ~ ($ᵗ α : ProbComp α) | fun x y => y = f x⟫ := by
  rvcgen_step using f
  · exact hf
  · intro x
    rfl

example [SampleableType α]
    {f : α → α} (hf : Function.Bijective f) :
    ⟪($ᵗ α : ProbComp α) ~ ($ᵗ α : ProbComp α) | fun x y => y = f x⟫ := by
  rvcgen_step
  · exact hf
  · intro x
    rfl

example {oa₁ oa₂ : OracleComp spec α} (n : ℕ)
    (h : ⟪oa₁ ~ oa₂ | EqRel α⟫) :
    ⟪oa₁.replicate n ~ oa₂.replicate n | EqRel (List α)⟫ := by
  rvcgen_step
  exact h

example {oa : OracleComp spec α} {ob : OracleComp spec β} (n : ℕ)
    {R : RelPost α β}
    (h : ⟪oa ~ ob | R⟫) :
    ⟪oa.replicate n ~ ob.replicate n | List.Forall₂ R⟫ := by
  rvcgen_step
  exact h

example {xs : List α} {f : α → OracleComp spec β} {g : α → OracleComp spec β}
    (hfg : ∀ a, ⟪f a ~ g a | EqRel β⟫) :
    ⟪xs.mapM f ~ xs.mapM g | EqRel (List β)⟫ := by
  rvcgen_step
  exact hfg

example {xs : List α} {ys : List β}
    {S : α → β → Prop}
    {f : α → OracleComp spec γ} {g : β → OracleComp spec γ}
    {R : RelPost γ γ}
    (hxy : List.Forall₂ S xs ys)
    (hfg : ∀ a b, S a b → ⟪f a ~ g b | R⟫) :
    ⟪xs.mapM f ~ ys.mapM g | List.Forall₂ R⟫ := by
  rvcgen_step using S
  · exact hxy
  · exact hfg

example {xs : List α} {ys : List β}
    {S : α → β → Prop}
    {f : α → OracleComp spec γ} {g : β → OracleComp spec γ}
    {R : RelPost γ γ}
    (hxy : List.Forall₂ S xs ys)
    (hfg : ∀ a b, S a b → ⟪f a ~ g b | R⟫) :
    ⟪xs.mapM f ~ ys.mapM g | List.Forall₂ R⟫ := by
  rvcgen_step?
  · exact hxy
  · exact hfg

example {σ₁ σ₂ : Type}
    {xs : List α}
    {f : σ₁ → α → OracleComp spec σ₁}
    {g : σ₂ → α → OracleComp spec σ₂}
    {S : σ₁ → σ₂ → Prop}
    {s₁ : σ₁} {s₂ : σ₂}
    (hs : S s₁ s₂)
    (hfg : ∀ a t₁ t₂, S t₁ t₂ → ⟪f t₁ a ~ g t₂ a | S⟫) :
    ⟪xs.foldlM f s₁ ~ xs.foldlM g s₂ | S⟫ := by
  rvcgen_step
  · exact hs
  · exact hfg

example {σ₁ σ₂ : Type}
    {xs : List α} {ys : List β}
    {Rin : α → β → Prop}
    {f : σ₁ → α → OracleComp spec σ₁}
    {g : σ₂ → β → OracleComp spec σ₂}
    {S : σ₁ → σ₂ → Prop}
    {s₁ : σ₁} {s₂ : σ₂}
    (hs : S s₁ s₂)
    (hxy : List.Forall₂ Rin xs ys)
    (hfg : ∀ a b, Rin a b → ∀ t₁ t₂, S t₁ t₂ → ⟪f t₁ a ~ g t₂ b | S⟫) :
    ⟪xs.foldlM f s₁ ~ ys.foldlM g s₂ | S⟫ := by
  rvcgen_step using Rin
  · exact hs
  · exact hxy
  · exact hfg

example (a : α) :
    ⟪(pure a : OracleComp spec α) ~ (pure a : OracleComp spec α) | EqRel α⟫ := by
  rvcgen_step

example {c : Prop} [Decidable c]
    {oa₁ oa₂ ob₁ ob₂ : OracleComp spec α}
    (h1 : ⟪oa₁ ~ ob₁ | EqRel α⟫)
    (h2 : ⟪oa₂ ~ ob₂ | EqRel α⟫) :
    ⟪(if c then oa₁ else oa₂) ~ (if c then ob₁ else ob₂) | EqRel α⟫ := by
  rvcgen_step
  · exact h1
  · exact h2

example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R R' : RelPost α β}
    (h : ⟪oa ~ ob | R⟫)
    (hpost : ∀ x y, R x y → R' x y) :
    ⟪oa ~ ob | R'⟫ := by
  rel_conseq
  · exact h
  · exact hpost

example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R R' : RelPost α β}
    (h : ⟪oa ~ ob | R⟫)
    (hpost : ∀ x y, R x y → R' x y) :
    ⟪oa ~ ob | R'⟫ := by
  rel_conseq with R
  · exact h
  · exact hpost

private def inlineId (oa : OracleComp spec α) : OracleComp spec α := oa

example (oa : OracleComp spec α) :
    ⟪inlineId oa ~ oa | EqRel α⟫ := by
  rel_inline inlineId

/-! ### Auto relational hint consumption -/

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcgen_step
  · exact hoa

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcgen_step?
  simpa [OracleComp.ProgramLogic.Relational.RelWP] using hoa

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ : α → OracleComp spec β} {f₂ : α → OracleComp spec γ}
    {S : RelPost α α} {R : RelPost β γ}
    (hoa : ⟪oa₁ ~ oa₂ | S⟫)
    (hf : ∀ a₁ a₂, S a₁ a₂ → ⟪f₁ a₁ ~ f₂ a₂ | R⟫) :
    ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫ := by
  rvcgen

/-! ### Relational consequence close -/

example {oa : OracleComp spec α} {ob : OracleComp spec β}
    {R R' : RelPost α β}
    (h : ⟪oa ~ ob | R⟫)
    (hpost : ∀ x y, R x y → R' x y) :
    ⟪oa ~ ob | R'⟫ := by
  rvcgen

end Relational

/-! ## Proof mode entry / exit examples -/

section EntryExit

example {g₁ g₂ g₃ : OracleComp spec α}
    (h₁ : g₁ ≡ₚ g₂) (h₂ : g₂ ≡ₚ g₃) :
    g₁ ≡ₚ g₃ := by
  game_trans g₂
  · exact h₁
  · exact h₂

section ByUpto

variable {σ : Type} {ι : Type} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α : Type}

example
    (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (bad : σ → Prop) [DecidablePred bad]
    (oa : OracleComp spec α) (s₀ : σ)
    (h_init : ¬bad s₀)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s →
      (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₁ t).run s), bad x.2)
    (h_mono₂ : ∀ (t : spec.Domain) (s : σ), bad s →
      ∀ x ∈ support ((impl₂ t).run s), bad x.2) :
    tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀)
      ≤ Pr[bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀].toReal := by
  by_upto bad
  · exact h_init
  · exact h_agree
  · exact h_mono₁
  · exact h_mono₂

end ByUpto

section RelSim

variable {σ₁ σ₂ : Type} {ι : Type} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α : Type}

example
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      R_state s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    ⟪(simulateQ impl₁ oa).run s₁
     ~ (simulateQ impl₂ oa).run s₂
     | fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2⟫ := by
  rvcgen_step using R_state
  all_goals first | exact himpl | exact hs

example
    (impl₁ : QueryImpl spec (StateT σ₁ (OracleComp spec)))
    (impl₂ : QueryImpl spec (StateT σ₂ (OracleComp spec)))
    (R_state : σ₁ → σ₂ → Prop)
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s₁ : σ₁) (s₂ : σ₂),
      R_state s₁ s₂ →
      RelTriple ((impl₁ t).run s₁) ((impl₂ t).run s₂)
        (fun p₁ p₂ => p₁.1 = p₂.1 ∧ R_state p₁.2 p₂.2))
    (s₁ : σ₁) (s₂ : σ₂) (hs : R_state s₁ s₂) :
    ⟪(simulateQ impl₁ oa).run' s₁
     ~ (simulateQ impl₂ oa).run' s₂
     | EqRel α⟫ := by
  rvcgen_step
  all_goals first | exact himpl | exact hs

end RelSim

section RelSimDist

variable {σ : Type} {ι : Type} {spec : OracleSpec ι}
variable [spec.Fintype] [spec.Inhabited]
variable {α : Type}

example
    (impl₁ : QueryImpl spec (StateT σ (OracleComp spec)))
    (impl₂ : QueryImpl spec (StateT σ (OracleComp spec)))
    (oa : OracleComp spec α)
    (himpl : ∀ (t : spec.Domain) (s : σ),
      evalDist ((impl₁ t).run s) = evalDist ((impl₂ t).run s))
    (s₁ s₂ : σ) (hs : s₁ = s₂) :
    ⟪(simulateQ impl₁ oa).run' s₁
     ~ (simulateQ impl₂ oa).run' s₂
     | EqRel α⟫ := by
  rvcgen_step
  · exact himpl
  · exact hs

end RelSimDist

section GameEquiv

example (oa : OracleComp spec α) :
    oa ≡ₚ oa := by
  rvcgen

example (oa : OracleComp spec α) :
    oa ≡ₚ oa := by
  rvcgen?

example [SampleableType α]
    (f : α → α) (hf : Function.Bijective f) :
    (f <$> ($ᵗ α : ProbComp α)) ≡ₚ ($ᵗ α : ProbComp α) := by
  conv_rhs => rw [← id_map ($ᵗ α : ProbComp α)]
  by_equiv
  rvcgen
  · exact hf
  · exact rfl

example {oa₁ oa₂ : OracleComp spec α}
    {f₁ f₂ : α → OracleComp spec β}
    {g₁ g₂ : β → OracleComp spec γ}
    {R : RelPost β β}
    (h12 : ⟪oa₁ >>= f₁ ~ oa₂ >>= f₂ | R⟫)
    (h23 : ∀ b₁ b₂, R b₁ b₂ → ⟪g₁ b₁ ~ g₂ b₂ | EqRel γ⟫) :
    (oa₁ >>= f₁ >>= g₁) ≡ₚ (oa₂ >>= f₂ >>= g₂) := by
  rvcgen using R

end GameEquiv

section ByDist

example {game₁ game₂ : OracleComp spec Bool} {ε₁ ε₂ : ℝ}
    (hbound : AdvBound game₁ ε₁) (htv : tvDist game₁ game₂ ≤ ε₂) :
    AdvBound game₂ (ε₁ + ε₂) := by
  by_dist ε₂
  · exact hbound
  · exact htv

end ByDist

section RelDist

variable {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
variable {α : Type}

example {oa ob : OracleComp spec α}
    (h : evalDist oa = evalDist ob) :
    ⟪oa ~ ob | EqRel α⟫ := by
  rel_dist
  exact h

end RelDist

end EntryExit

/-! ## Probability rewrite examples -/

section Probability

variable {ι : Type} {spec : OracleSpec ι} [spec.Fintype] [spec.Inhabited]
variable {α β γ δ ε : Type}

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {y : β}
    (h : ∀ x ∈ support mx, Pr[= y | f x] = Pr[= y | g x]) :
    Pr[= y | mx >>= f] = Pr[= y | mx >>= g] := by
  qvcgen_step
  exact h _ ‹_›

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f : α → β → OracleComp spec γ} {y : γ} :
    Pr[= y | mx >>= fun a => my >>= fun b => f a b] =
    Pr[= y | my >>= fun b => mx >>= fun a => f a b] := by
  qvcgen_step rw

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {mz : OracleComp spec γ} {f : α → β → γ → OracleComp spec δ} {y : δ} :
    Pr[= y | mx >>= fun a => my >>= fun b => mz >>= fun c => f a b c] =
    Pr[= y | mx >>= fun a => mz >>= fun c => my >>= fun b => f a b c] := by
  qvcgen_step rw under 1

example {mw : OracleComp spec α} {mx : OracleComp spec β}
    {my : OracleComp spec γ} {mz : OracleComp spec δ}
    {f : α → β → γ → δ → OracleComp spec ε} {out : ε} :
    Pr[= out | mw >>= fun w => mx >>= fun x => my >>= fun y => mz >>= fun z => f w x y z] =
    Pr[= out | mw >>= fun w => mx >>= fun x => mz >>= fun z => my >>= fun y => f w x y z] := by
  qvcgen_step rw under 2

example {mx : OracleComp spec α} {f g : α → OracleComp spec β} {q : β → Prop}
    (h : ∀ x, Pr[q | f x] = Pr[q | g x]) :
    Pr[q | mx >>= f] = Pr[q | mx >>= g] := by
  qvcgen_step rw congr'
  exact h _

example {mx : OracleComp spec α} {my : OracleComp spec β}
    {f : α → β → OracleComp spec γ} {q : γ → Prop} :
    Pr[q | mx >>= fun a => my >>= fun b => f a b] =
    Pr[q | my >>= fun b => mx >>= fun a => f a b] := by
  qvcgen

end Probability
