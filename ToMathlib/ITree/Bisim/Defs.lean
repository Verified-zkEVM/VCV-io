/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
module

public import ToMathlib.ITree.Construct

/-! # Bisimulation for Interaction Trees

This module defines the two equivalences on `ITree F α` used throughout the
algebraic theory:

* `ITree.Bisim t s` — *strong* (a.k.a. structural) bisimulation. Two ITrees
  are strongly bisimilar iff their one-step shapes match and the
  continuations are pointwise bisimilar. By the universal property of
  `PFunctor.M`, strong bisimulation coincides with definitional equality;
  for that reason we set `Bisim = (· = ·)`.

* `ITree.WeakBisim t s` — *weak* bisimulation (Coq `eutt`). Two ITrees are
  weakly bisimilar iff, after stripping any *finitely many* leading `step`
  nodes from each side, their observable heads agree (pure leaves, visible
  queries, or paired silent steps) and continuations are pointwise weakly
  bisimilar. This is the intended notion of ITree equivalence for
  reasoning about programs.

## Design

The naive coinductive definition with `tauL` / `tauR` constructors
directly appearing in a coinductive predicate is **unsound**: it admits
`WeakBisim (pure r) diverge` via repeated `tauR` applications, because
the greatest fixed point closes under the (unbounded) coinductive
stripping. The fix follows Xia et al. (POPL 2020): wrap τ-stripping in
an *inductive* relation `TauSteps` (so each stripping chain is finite),
and let each coinductive "step" of `WeakBisim` consist of stripping
finitely many τ's from each side and then matching observable heads via
the `Match` functor.

We define `WeakBisim` as the Tarski greatest fixed point of the
one-step functor packaged by `TauSteps` + `Match`, i.e. as the largest
relation `R` that is closed under the functor. This `∃ R, …` form is
used because Lean 4.29's `coinductive` keyword requires syntactic
monotonicity, which does not see through the separately-declared
`Match` inductive.

## Implementation notes

Lean 4.29 supports `coinductive` *predicates*, but the monotonicity
checker is syntactic. We therefore use the explicit Tarski formulation
`∃ R, R t s ∧ closure`. The coinduction principle is then the
constructor itself (`WeakBisim.coinduct`), and the standard algebraic
laws (reflexivity, symmetry, transitivity) are recovered by exhibiting
an appropriate witness relation `R` in each case.
-/

@[expose] public section

universe u

namespace ITree

variable {F : PFunctor.{u, u}} {α : Type u}

/-! ### Strong bisimulation -/

/-- Strong bisimulation on interaction trees. Two ITrees are strongly
bisimilar iff they are equal as elements of the M-type `PFunctor.M (Poly F α)`,
which by `PFunctor.M.bisim` is the same as having matching one-step shapes
with pointwise-bisimilar continuations. -/
@[reducible]
def Bisim (t s : ITree F α) : Prop := t = s

@[inherit_doc] scoped infix:50 " ≅ " => ITree.Bisim

namespace Bisim

variable {t s u : ITree F α}

@[refl] theorem refl' (t : ITree F α) : t ≅ t := rfl

@[symm] theorem symm' (h : t ≅ s) : s ≅ t := Eq.symm h

@[trans] theorem trans' (h₁ : t ≅ s) (h₂ : s ≅ u) : t ≅ u := Eq.trans h₁ h₂

/-- One-step characterisation: two ITrees are strongly bisimilar iff their
`shape'` agrees. Provable by `PFunctor.M.bisim`. -/
theorem dest (h : t ≅ s) : shape' t = shape' s := by
  cases h; rfl

end Bisim

/-! ### Finite τ-stripping

`TauSteps t t'` captures the (deterministic, partial) operation of
stripping finitely many leading silent-step nodes from `t` to reach `t'`.
Being an inductive family, every derivation has a finite length. -/

/-- `TauSteps t t'` iff `t'` is obtained from `t` by stripping finitely
many leading `step` nodes. -/
inductive TauSteps : ITree F α → ITree F α → Prop where
  /-- Strip zero steps: `t` is reachable from itself. -/
  | refl (t : ITree F α) : TauSteps t t
  /-- Strip one step from a step-headed tree and continue stripping. -/
  | step {t t' : ITree F α} (c : PUnit.{u + 1} → ITree F α)
      (ht : shape' t = ⟨.step, c⟩) (hr : TauSteps (c PUnit.unit) t') :
      TauSteps t t'

namespace TauSteps

/-- Transitivity of τ-stripping. -/
theorem trans {t s u : ITree F α} (h₁ : TauSteps t s) (h₂ : TauSteps s u) :
    TauSteps t u := by
  induction h₁ with
  | refl _ => exact h₂
  | step c ht _ ih => exact .step c ht (ih h₂)

/-- Stripping one step is available when the head is a step. -/
theorem one {t : ITree F α} (c : PUnit.{u + 1} → ITree F α)
    (ht : shape' t = ⟨.step, c⟩) : TauSteps t (c PUnit.unit) :=
  TauSteps.step (t' := c PUnit.unit) c ht (TauSteps.refl _)

/-- The `.step` relation is deterministic on step-headed trees. -/
theorem cont_eq {t : ITree F α} {c c' : PUnit.{u + 1} → ITree F α}
    (h : shape' t = ⟨.step, c⟩) (h' : shape' t = ⟨.step, c'⟩) : c = c' := by
  have hmk := h.symm.trans h'
  exact eq_of_heq (Sigma.mk.inj hmk).2

/-- `TauSteps` is linear: any two strippings from the same tree are
comparable. Uses determinism of `shape'`. -/
theorem linear {t a b : ITree F α}
    (ha : TauSteps t a) (hb : TauSteps t b) :
    TauSteps a b ∨ TauSteps b a := by
  induction ha generalizing b with
  | refl _ => exact Or.inl hb
  | @step t t' c ht hr ih =>
      cases hb with
      | refl _ => exact Or.inr (TauSteps.step (t' := t') c ht hr)
      | @step _ _ c' ht' hr' =>
          have hcc : c = c' := cont_eq ht ht'
          subst hcc
          exact ih hr'

end TauSteps

/-! ### Head match relation

`Match R t s` pins two trees whose observable heads agree. There is no
τ-stripping here: stripping happens separately via `TauSteps` before
invoking `Match`. -/

/-- One-step observable head match. Two trees have matching heads iff
both are pure leaves carrying the same value, both are queries with the
same event name and pointwise `R`-related continuations, or both are
step-headed with `R`-related step continuations. -/
inductive Match (R : ITree F α → ITree F α → Prop) :
    ITree F α → ITree F α → Prop where
  /-- Both heads are pure leaves with the same value. -/
  | pure {t s : ITree F α} (r : α)
      (ht : shape' t = ⟨.pure r, PEmpty.elim⟩)
      (hs : shape' s = ⟨.pure r, PEmpty.elim⟩) :
      Match R t s
  /-- Both heads are visible queries on the same event. -/
  | query {t s : ITree F α} (a : F.A) (c c' : F.B a → ITree F α)
      (ht : shape' t = ⟨.query a, c⟩) (hs : shape' s = ⟨.query a, c'⟩)
      (h : ∀ b, R (c b) (c' b)) :
      Match R t s
  /-- Both heads are silent steps, with continuations related by `R`. -/
  | tau {t s : ITree F α} (ct cs : PUnit.{u + 1} → ITree F α)
      (ht : shape' t = ⟨.step, ct⟩) (hs : shape' s = ⟨.step, cs⟩)
      (h : R (ct PUnit.unit) (cs PUnit.unit)) :
      Match R t s

namespace Match

/-- Monotonicity: `Match` is monotone in its relation parameter. -/
theorem mono {R R' : ITree F α → ITree F α → Prop}
    (h : ∀ a b, R a b → R' a b) {t s : ITree F α}
    (hM : Match R t s) : Match R' t s := by
  cases hM with
  | pure r ht hs => exact .pure r ht hs
  | query a c c' ht hs hcc => exact .query a c c' ht hs (fun b => h _ _ (hcc b))
  | tau ct cs ht hs hr => exact .tau ct cs ht hs (h _ _ hr)

/-- `Match` is symmetric in the two sides when `R` is swapped. -/
theorem swap {R : ITree F α → ITree F α → Prop} {t s : ITree F α}
    (hM : Match R t s) : Match (fun x y => R y x) s t := by
  cases hM with
  | pure r ht hs => exact .pure r hs ht
  | query a c c' ht hs hcc => exact .query a c' c hs ht (fun b => hcc b)
  | tau ct cs ht hs hr => exact .tau cs ct hs ht hr

end Match

/-! ### Weak bisimulation -/

/-- One-step unfolding functor for weak bisimulation: strip finitely many
τ's from each side (via `TauSteps`) and then match observable heads (via
`Match`). `WeakBisim` is the Tarski greatest fixed point of this functor. -/
def WeakBisimF (R : ITree F α → ITree F α → Prop) (t s : ITree F α) : Prop :=
  ∃ t' s' : ITree F α, TauSteps t t' ∧ TauSteps s s' ∧ Match R t' s'

/-- `WeakBisimF` is monotone in its relation parameter. -/
theorem WeakBisimF.mono {R R' : ITree F α → ITree F α → Prop}
    (h : ∀ a b, R a b → R' a b) {t s : ITree F α}
    (hF : WeakBisimF R t s) : WeakBisimF R' t s := by
  obtain ⟨t', s', ht, hs, hm⟩ := hF
  exact ⟨t', s', ht, hs, hm.mono h⟩

/-- Weak bisimulation (Coq `eutt`). Two trees are weakly bisimilar iff
there exists a relation `R` containing the pair that is closed under
one-step unfolding into `WeakBisimF`. Equivalently, `WeakBisim` is the
largest such relation (Tarski greatest fixed point). -/
def WeakBisim (t s : ITree F α) : Prop :=
  ∃ R : ITree F α → ITree F α → Prop,
    (∀ a b, R a b → WeakBisimF R a b) ∧ R t s

@[inherit_doc] scoped infix:50 " ≈ " => ITree.WeakBisim

namespace WeakBisim

/-- Coinduction principle: any relation closed under `WeakBisimF` is
contained in `WeakBisim`. This is the Tarski greatest fixed point
characterization. -/
theorem coinduct (R : ITree F α → ITree F α → Prop)
    (h : ∀ a b, R a b → WeakBisimF R a b)
    {a b : ITree F α} (hab : R a b) : a ≈ b :=
  ⟨R, h, hab⟩

/-- `WeakBisim` is closed under `WeakBisimF`. -/
theorem unfold {t s : ITree F α} (h : t ≈ s) : WeakBisimF WeakBisim t s := by
  obtain ⟨R, hcl, hR⟩ := h
  obtain ⟨t', s', ht, hs, hm⟩ := hcl _ _ hR
  exact ⟨t', s', ht, hs, hm.mono (fun x y hxy => ⟨R, hcl, hxy⟩)⟩

/-- Extract the stripped-heads match witness. -/
theorem dest {t s : ITree F α} (h : t ≈ s) :
    ∃ t' s' : ITree F α, TauSteps t t' ∧ TauSteps s s' ∧ Match WeakBisim t' s' :=
  unfold h

/-- Folding rule: supplying a `WeakBisimF WeakBisim`-match recovers
`WeakBisim`. -/
theorem fold {t s : ITree F α} (h : WeakBisimF WeakBisim t s) : t ≈ s := by
  obtain ⟨t', s', ht, hs, hm⟩ := h
  refine coinduct (fun a b => a ≈ b ∨
      (a = t ∧ b = s)) ?_ (Or.inr ⟨rfl, rfl⟩)
  rintro a b (hab | ⟨rfl, rfl⟩)
  · exact (unfold hab).mono (fun x y hxy => Or.inl hxy)
  · exact ⟨t', s', ht, hs, hm.mono (fun x y hxy => Or.inl hxy)⟩

end WeakBisim

end ITree
