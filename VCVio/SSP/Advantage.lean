/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.SSP.Composition
import VCVio.CryptoFoundations.SecExp

/-!
# State-Separating Proofs: Advantage and the Reduction Lemma

This file bridges the SSP `Package` layer to VCVio's probability machinery and proves the
basic SSP advantage lemma.

* `Package.advantage` measures the Boolean distinguishing advantage between two packages
  `G₀ G₁ : Package unifSpec E σ` against an external adversary `A : OracleComp E Bool`. It
  is built directly out of `ProbComp.boolDistAdvantage` from `VCVio.CryptoFoundations.SecExp`.

* `Package.simulateQ_link_run` is the structural fact that running a linked package on an
  adversary equals running the inner package on the outer-package's interpretation of that
  adversary. This is the SSP "reduction lemma" `Adv (G₀, G₁) (A ∘ P) = Adv (P ∘ G₀, P ∘ G₁) A`
  in its program-equivalence form. The real-valued advantage equality is then immediate.

The triangle inequality is already provided by `ProbComp.boolDistAdvantage_triangle` in
`VCVio.CryptoFoundations.SecExp`; we re-export an `advantage_triangle` corollary for
ergonomic use at the package level.
-/

universe u v w

open OracleSpec OracleComp ProbComp

namespace VCVio.SSP

namespace Package

variable {ιᵢ ιₘ ιₑ : Type}
  {I : OracleSpec ιᵢ} {M : OracleSpec ιₘ} {E : OracleSpec ιₑ}
  {σ σ₁ σ₂ : Type}

/-! ### Bridging to `ProbComp` -/

/-- Run a probability-only package (imports = `unifSpec`) against an adversary. The result is
a `ProbComp`, ready to be measured with `Pr[= true | _]` and `boolDistAdvantage`. -/
@[reducible]
def runProb {α : Type} (P : Package unifSpec E σ) (A : OracleComp E α) : ProbComp α :=
  P.run A

/-! ### Advantage and triangle inequality -/

/-- The Boolean distinguishing advantage between two probability-only packages, against a
single Boolean-valued adversary. The internal state types `σ₀, σ₁` of the two games are
independent: from the adversary's point of view only the export interface and the resulting
output distribution matter. -/
noncomputable def advantage {σ₀ σ₁ : Type}
    (G₀ : Package unifSpec E σ₀) (G₁ : Package unifSpec E σ₁)
    (A : OracleComp E Bool) : ℝ :=
  (G₀.runProb A).boolDistAdvantage (G₁.runProb A)

@[simp]
lemma advantage_self (G : Package unifSpec E σ) (A : OracleComp E Bool) :
    G.advantage G A = 0 := by
  simp [advantage, ProbComp.boolDistAdvantage]

lemma advantage_symm {σ₀ σ₁ : Type}
    (G₀ : Package unifSpec E σ₀) (G₁ : Package unifSpec E σ₁)
    (A : OracleComp E Bool) :
    G₀.advantage G₁ A = G₁.advantage G₀ A := by
  unfold advantage ProbComp.boolDistAdvantage
  exact abs_sub_comm _ _

/-- If two packages run an adversary to the same `ProbComp Bool` *up to `evalDist`*, their
distinguishing advantages against any third package coincide. This is the basic "replace by
equivalent game" rule that underlies SSP game-hopping at the advantage level: only the
output distributions matter, not the syntactic form of the resulting `OracleComp`. -/
lemma advantage_eq_of_evalDist_runProb_eq {σ₀ σ₀' σ₁ : Type}
    {G₀ : Package unifSpec E σ₀} {G₀' : Package unifSpec E σ₀'}
    {G₁ : Package unifSpec E σ₁} {A : OracleComp E Bool}
    (h : evalDist (G₀.runProb A) = evalDist (G₀'.runProb A)) :
    G₀.advantage G₁ A = G₀'.advantage G₁ A := by
  unfold advantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl h]

lemma advantage_eq_of_evalDist_runProb_eq_right {σ₀ σ₁ σ₁' : Type}
    {G₀ : Package unifSpec E σ₀}
    {G₁ : Package unifSpec E σ₁} {G₁' : Package unifSpec E σ₁'}
    {A : OracleComp E Bool}
    (h : evalDist (G₁.runProb A) = evalDist (G₁'.runProb A)) :
    G₀.advantage G₁ A = G₀.advantage G₁' A := by
  unfold advantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl h]

lemma advantage_triangle {σ₀ σ₁ σ₂ : Type}
    (G₀ : Package unifSpec E σ₀) (G₁ : Package unifSpec E σ₁) (G₂ : Package unifSpec E σ₂)
    (A : OracleComp E Bool) :
    G₀.advantage G₂ A ≤ G₀.advantage G₁ A + G₁.advantage G₂ A :=
  ProbComp.boolDistAdvantage_triangle _ _ _

/-! ### Structural reduction for `link` -/

/-- The `Prod` reshaping used in the linked package's handler. -/
@[reducible]
def linkReshape (α : Type) (s₁ : Type) (s₂ : Type) :
    (α × s₁) × s₂ → α × (s₁ × s₂) := fun p => (p.1.1, (p.1.2, p.2))

/-- Structural fact: running `(P.link Q).impl` is the same as nesting the simulations,
threaded through both states. This is the unbundled form from which the SSP reduction
lemma follows.

Statement:
`(simulateQ (P.link Q).impl A).run (s₁, s₂) =`
`  reshape <$> (simulateQ Q.impl ((simulateQ P.impl A).run s₁)).run s₂`. -/
theorem simulateQ_link_run {α : Type}
    (P : Package M E σ₁) (Q : Package I M σ₂)
    (A : OracleComp E α) (s₁ : σ₁) (s₂ : σ₂) :
    (simulateQ (P.link Q).impl A).run (s₁, s₂) =
      (linkReshape α σ₁ σ₂) <$>
        (simulateQ Q.impl ((simulateQ P.impl A).run s₁)).run s₂ := by
  induction A using OracleComp.inductionOn generalizing s₁ s₂ with
  | pure x =>
    -- Both sides reduce to `pure (x, (s₁, s₂)) : OracleComp I _`.
    change (pure (x, (s₁, s₂)) : OracleComp I (α × (σ₁ × σ₂))) =
      linkReshape α σ₁ σ₂ <$> (simulateQ Q.impl (pure (x, s₁))).run s₂
    rw [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind t k ih =>
    -- Step 1: rewrite LHS using the definition of `(P.link Q).impl t` and StateT bind.
    have hLHS : (simulateQ (P.link Q).impl (liftM (query t) >>= k)).run (s₁, s₂) =
        (simulateQ Q.impl ((P.impl t).run s₁)).run s₂ >>=
          fun (p : (E.Range t × σ₁) × σ₂) =>
            (simulateQ (P.link Q).impl (k p.1.1)).run (p.1.2, p.2) := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      change ((P.link Q).impl t >>= fun a => simulateQ (P.link Q).impl (k a)).run (s₁, s₂) = _
      rw [StateT.run_bind]
      change (linkReshape (E.Range t) σ₁ σ₂ <$>
          (simulateQ Q.impl ((P.impl t).run s₁)).run s₂) >>= _ = _
      rw [bind_map_left]
    -- Step 2: rewrite RHS using simulateQ_bind for both monads and StateT bind.
    have hRHS : (simulateQ Q.impl ((simulateQ P.impl (liftM (query t) >>= k)).run s₁)).run s₂ =
        (simulateQ Q.impl ((P.impl t).run s₁)).run s₂ >>=
          fun (p : (E.Range t × σ₁) × σ₂) =>
            (simulateQ Q.impl ((simulateQ P.impl (k p.1.1)).run p.1.2)).run p.2 := by
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
        OracleQuery.input_query, id_map]
      change (simulateQ Q.impl ((P.impl t >>=
          fun a => simulateQ P.impl (k a)).run s₁)).run s₂ = _
      rw [StateT.run_bind, simulateQ_bind, StateT.run_bind]
    -- Step 3: combine, then map and use the IH pointwise.
    rw [hLHS, hRHS, map_bind]
    refine bind_congr fun p => ?_
    exact ih p.1.1 p.1.2 p.2

/-- The SSP **reduction lemma** in its program-equivalence form: linking the outer reduction
package `P` to game `Q` and running against adversary `A` produces the same `OracleComp`
output distribution as running `Q` against `simulateQ P.impl A` (the "outer-shifted"
adversary).

This is the analogue of SSProve's `swap_link_left` / `link_assoc`-driven move that turns
`A ∘ (P ∘ Q)` into `(A ∘ P) ∘ Q` at the level of distributions. -/
theorem run_link {α : Type}
    (P : Package M E σ₁) (Q : Package I M σ₂) (A : OracleComp E α) :
    (P.link Q).run A =
      (Prod.fst : α × σ₁ → α) <$>
        (simulateQ Q.impl ((simulateQ P.impl A).run P.init)).run' Q.init := by
  change (Prod.fst : α × (σ₁ × σ₂) → α) <$>
      (simulateQ (P.link Q).impl A).run (P.init, Q.init) = _
  rw [simulateQ_link_run, StateT.run'_eq, ← Functor.map_map]
  simp [linkReshape]

/-- Specialization of `run_link` for two stateless packages. The link of two `ofStateless`
packages reduces to nested `simulateQ` calls without any state to thread. -/
@[simp]
theorem run_link_ofStateless {α : Type}
    (hP : QueryImpl E (OracleComp M)) (hQ : QueryImpl M (OracleComp I))
    (A : OracleComp E α) :
    ((Package.ofStateless hP).link (Package.ofStateless hQ)).run A =
      simulateQ hQ (simulateQ hP A) := by
  -- Direct induction on `A`. Both sides are functorial in `A`; the only base case is
  -- `pure x`, which trivially gives `pure x` on both sides; the inductive case threads
  -- through a query then continues by induction.
  induction A using OracleComp.inductionOn with
  | pure x =>
    simp only [Package.run, Package.link, Package.ofStateless, simulateQ_pure]
    rfl
  | query_bind t k ih =>
    -- LHS: rewrite via `run_link` and the runState facts for stateless packages.
    have hLHS := run_link (Package.ofStateless hP) (Package.ofStateless hQ)
      (liftM (query t) >>= k)
    -- Rewrite the inner `simulateQ` of the outer stateless package using
    -- `runState_ofStateless` (which is exactly `(simulateQ ... ).run PUnit.unit`).
    have hP_runState : ∀ (β : Type) (B : OracleComp E β),
        (simulateQ (Package.ofStateless hP).impl B).run PUnit.unit
          = (·, PUnit.unit.{1}) <$> simulateQ hP B := fun _ B => runState_ofStateless hP B
    have hQ_runState : ∀ (β : Type) (B : OracleComp M β),
        (simulateQ (Package.ofStateless hQ).impl B).run PUnit.unit
          = (·, PUnit.unit.{1}) <$> simulateQ hQ B := fun _ B => runState_ofStateless hQ B
    rw [hLHS]
    -- Now the goal involves `(simulateQ Q.impl ((simulateQ P.impl _).run PUnit.unit)).run'
    -- PUnit.unit`. Apply `hP_runState` to the inner term.
    change Prod.fst <$> (simulateQ (Package.ofStateless hQ).impl
        ((simulateQ (Package.ofStateless hP).impl (liftM (query t) >>= k)).run
          PUnit.unit)).run' PUnit.unit = _
    rw [hP_runState]
    -- Now `simulateQ (ofStateless hQ).impl ((·, PUnit.unit) <$> simulateQ hP _)`.
    -- Use `simulateQ_map` to pull the map out, then `runState_ofStateless` again.
    rw [simulateQ_map]
    -- Now we have a `(·, PUnit.unit) <$> simulateQ ...` inside `StateT PUnit (OracleComp I)`.
    -- Reduce `.run' PUnit.unit` of that to a plain `OracleComp I` map.
    rw [StateT.run'_eq, StateT.run_map, hQ_runState]
    simp [Functor.map_map]

/-- Two `ProbComp`-valued query implementations that agree on every input *under `evalDist`*
yield identical evaluations of any `simulateQ`. This is the SSP-flavoured "rewrite the handler
up to evalDist" rule used to discharge program equivalences whose underlying computations
are not propositionally equal but agree distributionally. -/
lemma simulateQ_evalDist_congr {α : Type}
    {h₁ h₂ : QueryImpl E ProbComp}
    (hh : ∀ (q : E.Domain), evalDist (h₁ q) = evalDist (h₂ q)) (A : OracleComp E α) :
    evalDist (simulateQ h₁ A) = evalDist (simulateQ h₂ A) := by
  induction A using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, evalDist_bind]
    rw [hh t]
    refine bind_congr fun u => ?_
    exact ih u

end Package

end VCVio.SSP
