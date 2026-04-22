/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.SSP.Package

/-!
# State-Separating Proofs: Advantage and `evalDist` congruences

This file bridges the SSP `Package` layer to VCVio's probability machinery.

* `Package.runProb` reads off the `ProbComp` produced by running a probability-only package
  (imports `= unifSpec`) against an adversary.
* `Package.advantage` measures the Boolean distinguishing advantage between two packages
  `G₀ G₁ : Package unifSpec E σ` against an external adversary `A : OracleComp E Bool`. It
  is built directly out of `ProbComp.boolDistAdvantage` from `VCVio.CryptoFoundations.SecExp`,
  and inherits its triangle inequality.
* `Package.simulateQ_evalDist_congr` is the SSP-flavoured "rewrite the handler up to
  evalDist" rule: two query implementations that agree pointwise under `evalDist` yield the
  same simulation distribution, even when the underlying `ProbComp`s are not propositionally
  equal.

The program-level reduction lemmas (`simulateQ_link_run`, `run_link`, `run_link_ofStateless`)
live in `VCVio.SSP.Composition`, since they do not involve `ProbComp` and are stated for the
fully universe-polymorphic `Package`.

## Universe layout

Everything in this file is fixed at `Type 0`: `ProbComp : Type → Type` and the adversary
returns a `Bool : Type`, so the export indices, ranges, and state are all `Type`. Only the
import range universe and import index universe could a priori be larger, but `runProb` ties
the import to `unifSpec : OracleSpec ℕ` whose own indices and ranges are in `Type`. -/

universe uₑ

open OracleSpec OracleComp ProbComp

namespace VCVio.SSP

namespace Package

variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ} {σ : Type}

/-! ### Bridging to `ProbComp` -/

/-- Run a probability-only package (imports = `unifSpec`) against an adversary. The result is
a `ProbComp`, ready to be measured with `Pr[= true | _]` and `boolDistAdvantage`. -/
@[reducible]
def runProb {α : Type} (P : Package unifSpec E σ) (A : OracleComp E α) : ProbComp α :=
  P.run A

/-- `runProb` unfolds to `run` definitionally; exposed as a simp lemma so that SSP-facing
lemmas phrased in terms of `runProb` rewrite cleanly against `run`-phrased ones in
`VCVio.SSP.Composition`. -/
@[simp]
lemma runProb_eq_run {α : Type} (P : Package unifSpec E σ) (A : OracleComp E α) :
    P.runProb A = P.run A := rfl

/-! ### Advantage and triangle inequality -/

/-- The Boolean distinguishing advantage between two probability-only packages, against a
single Boolean-valued adversary. The internal state types `σ₀, σ₁` of the two games are
independent: from the adversary's point of view only the export interface and the resulting
output distribution matter.

This quantity is always nonnegative and symmetric in its first two arguments (see
`advantage_symm`), so it should be read as an *unsigned* gap rather than a signed quantity. -/
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

/-! ### `evalDist` congruence for handlers -/

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

/-- Stateful generalization of `simulateQ_evalDist_congr`: two `StateT σ ProbComp`-valued query
implementations that agree on every (input, state) pair *under `evalDist`* yield identical
evaluations of `(simulateQ _ A).run s` for every starting state `s`.

This is the lemma to use when both sides of a game equivalence are stateful packages with the
same internal state type and only their per-query handlers differ up to distribution (e.g., a
`dhTripleReal`-vs-`dhTripleRand` swap propagated through a stateless reduction). -/
lemma simulateQ_StateT_evalDist_congr {α : Type}
    {h₁ h₂ : QueryImpl E (StateT σ ProbComp)}
    (hh : ∀ (q : E.Domain) (s : σ), evalDist ((h₁ q).run s) = evalDist ((h₂ q).run s))
    (A : OracleComp E α) (s : σ) :
    evalDist ((simulateQ h₁ A).run s) = evalDist ((simulateQ h₂ A).run s) := by
  induction A using OracleComp.inductionOn generalizing s with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query, OracleQuery.input_query,
      id_map, StateT.run_bind, evalDist_bind]
    rw [hh t s]
    refine bind_congr fun p => ?_
    exact ih p.1 p.2

/-! ### Functoriality of `runProb`

`Package.runProb` commutes with monadic map on the adversary: rerouting the output of an
adversary `A : OracleComp E α` through a post-processing function `f : α → β` before running the
package yields the same distribution as running the package and then applying `f`. -/

lemma runProb_map {α β : Type} (P : Package unifSpec E σ) (f : α → β) (A : OracleComp E α) :
    P.runProb (f <$> A) = f <$> P.runProb A := by
  change P.run (f <$> A) = f <$> P.run A
  unfold Package.run
  rw [simulateQ_map, map_bind]
  refine bind_congr fun s₀ => ?_
  rw [StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map, Functor.map_map]

end Package

end VCVio.SSP
