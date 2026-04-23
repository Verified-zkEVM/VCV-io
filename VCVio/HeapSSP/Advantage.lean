/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.HeapSSP.Package

/-!
# HeapSSP: Advantage and `evalDist` congruences

Heap-package counterpart of `VCVio.SSP.Advantage`.

* `Package.runProb` reads off the `ProbComp` produced by running a
  probability-only heap-package (imports `= unifSpec`) against an adversary.
* `Package.advantage` measures the Boolean distinguishing advantage between
  two probability-only heap-packages
  `G₀ G₁ : Package unifSpec E Ident` against an external Boolean adversary
  `A : OracleComp E Bool`. Built directly on `ProbComp.boolDistAdvantage`
  from `VCVio.CryptoFoundations.SecExp`, and inherits its triangle inequality.
* `Package.simulateQ_evalDist_congr` and its stateful generalisation
  `simulateQ_StateT_evalDist_congr` are the heap-package analogues of the
  SSP "rewrite the handler up to evalDist" rule: per-input handler equality
  under `evalDist` upgrades to a whole-adversary `evalDist` equality. They
  are stated for *any* import spec `I` with `[I.Fintype]` `[I.Inhabited]`,
  so that they apply uniformly to `unifSpec`-imports games (the bridge to
  `Package.advantage`) and to sum-imports games such as
  `Package.par`-composites (where the import is `I₁ + I₂`).
* `Package.simulateQ_StateT_evalDist_congr_of_bij` is the bijection-aware
  variant, used when the two heaps differ but are isomorphic. The bijection
  is on the *underlying state type* (here `Heap Ident`) rather than on
  identifier sets directly.

The program-level reduction lemmas (`simulateQ_link_run`,
`run_link_eq_run_shiftLeft`, `par_init`, ...) live in
`VCVio.HeapSSP.Composition` and are independent of `ProbComp`.

## Universe layout

The advantage-bridge lemmas (`runProb`, `advantage`, ...) are pinned to
`unifSpec : OracleSpec ℕ`, since `ProbComp.boolDistAdvantage` is itself
`unifSpec`-specific. The handler-congruence lemmas
(`simulateQ_evalDist_congr`, `simulateQ_StateT_evalDist_congr`,
`simulateQ_StateT_evalDist_congr_of_bij`) accept an arbitrary import
`I : OracleSpec.{uᵢ, 0} ιᵢ` with `[I.Fintype]` `[I.Inhabited]`. The export
index lives in `Type uₑ`; everything else (state, output type) is `Type 0`,
matching the rest of the HeapSSP layer. -/

universe uᵢ uₑ

open OracleSpec OracleComp ProbComp

namespace VCVio.HeapSSP

namespace Package

variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ}
  {Ident : Type} [CellSpec.{0, 0} Ident]

/-! ### Bridging to `ProbComp` -/

/-- Run a probability-only heap-package (imports = `unifSpec`) against an
adversary. The result is a `ProbComp`, ready to be measured with
`Pr[= true | _]` and `boolDistAdvantage`. -/
@[reducible]
def runProb {α : Type} (P : Package unifSpec E Ident) (A : OracleComp E α) :
    ProbComp α :=
  P.run A

/-- `runProb` unfolds to `run` definitionally. Exposed as a simp lemma so
that heap-SSP-facing lemmas phrased in terms of `runProb` rewrite cleanly
against `run`-phrased ones in `VCVio.HeapSSP.Composition`. -/
@[simp]
lemma runProb_eq_run {α : Type} (P : Package unifSpec E Ident)
    (A : OracleComp E α) : P.runProb A = P.run A := rfl

/-! ### Advantage and triangle inequality -/

/-- The Boolean distinguishing advantage between two probability-only
heap-packages, against a single Boolean-valued adversary. The internal
identifier sets `Ident₀, Ident₁` of the two games are independent: from
the adversary's point of view only the export interface and the resulting
output distribution matter.

This quantity is always nonnegative and symmetric in its first two
arguments (see `advantage_symm`), so it should be read as an *unsigned*
gap rather than a signed quantity. -/
noncomputable def advantage {Ident₀ Ident₁ : Type}
    [CellSpec.{0, 0} Ident₀] [CellSpec.{0, 0} Ident₁]
    (G₀ : Package unifSpec E Ident₀) (G₁ : Package unifSpec E Ident₁)
    (A : OracleComp E Bool) : ℝ :=
  (G₀.runProb A).boolDistAdvantage (G₁.runProb A)

@[simp]
lemma advantage_self (G : Package unifSpec E Ident) (A : OracleComp E Bool) :
    G.advantage G A = 0 := by
  simp [advantage, ProbComp.boolDistAdvantage]

lemma advantage_symm {Ident₀ Ident₁ : Type}
    [CellSpec.{0, 0} Ident₀] [CellSpec.{0, 0} Ident₁]
    (G₀ : Package unifSpec E Ident₀) (G₁ : Package unifSpec E Ident₁)
    (A : OracleComp E Bool) :
    G₀.advantage G₁ A = G₁.advantage G₀ A := by
  unfold advantage ProbComp.boolDistAdvantage
  exact abs_sub_comm _ _

/-- If two heap-packages run an adversary to the same `ProbComp Bool`
*up to `evalDist`*, their distinguishing advantages against any third
heap-package coincide. The basic "replace by equivalent game" rule
underlying SSP-style game-hopping at the advantage level. -/
lemma advantage_eq_of_evalDist_runProb_eq {Ident₀ Ident₀' Ident₁ : Type}
    [CellSpec.{0, 0} Ident₀] [CellSpec.{0, 0} Ident₀']
    [CellSpec.{0, 0} Ident₁]
    {G₀ : Package unifSpec E Ident₀} {G₀' : Package unifSpec E Ident₀'}
    {G₁ : Package unifSpec E Ident₁} {A : OracleComp E Bool}
    (h : evalDist (G₀.runProb A) = evalDist (G₀'.runProb A)) :
    G₀.advantage G₁ A = G₀'.advantage G₁ A := by
  unfold advantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl h]

lemma advantage_eq_of_evalDist_runProb_eq_right
    {Ident₀ Ident₁ Ident₁' : Type}
    [CellSpec.{0, 0} Ident₀] [CellSpec.{0, 0} Ident₁]
    [CellSpec.{0, 0} Ident₁']
    {G₀ : Package unifSpec E Ident₀}
    {G₁ : Package unifSpec E Ident₁} {G₁' : Package unifSpec E Ident₁'}
    {A : OracleComp E Bool}
    (h : evalDist (G₁.runProb A) = evalDist (G₁'.runProb A)) :
    G₀.advantage G₁ A = G₀.advantage G₁' A := by
  unfold advantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl h]

lemma advantage_triangle {Ident₀ Ident₁ Ident₂ : Type}
    [CellSpec.{0, 0} Ident₀] [CellSpec.{0, 0} Ident₁]
    [CellSpec.{0, 0} Ident₂]
    (G₀ : Package unifSpec E Ident₀) (G₁ : Package unifSpec E Ident₁)
    (G₂ : Package unifSpec E Ident₂) (A : OracleComp E Bool) :
    G₀.advantage G₂ A ≤ G₀.advantage G₁ A + G₁.advantage G₂ A :=
  ProbComp.boolDistAdvantage_triangle _ _ _

/-! ### `evalDist` congruence for handlers

Stated for an arbitrary import `I : OracleSpec.{uᵢ, 0} ιᵢ` with
`[I.Fintype]` `[I.Inhabited]`. The `unifSpec`-imports specialisation is
recovered by instantiating `I := unifSpec`. -/

section EvalDistCongr

variable {ιᵢ : Type uᵢ} {I : OracleSpec.{uᵢ, 0} ιᵢ} [I.Fintype] [I.Inhabited]

/-- Two `OracleComp I`-valued query implementations that agree on every
input *under `evalDist`* yield identical evaluations of any `simulateQ`.
The heap-SSP-flavoured "rewrite the handler up to evalDist" rule. -/
lemma simulateQ_evalDist_congr {α : Type}
    {h₁ h₂ : QueryImpl E (OracleComp I)}
    (hh : ∀ (q : E.Domain), evalDist (h₁ q) = evalDist (h₂ q))
    (A : OracleComp E α) :
    evalDist (simulateQ h₁ A) = evalDist (simulateQ h₂ A) := by
  induction A using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, evalDist_bind]
    rw [hh t]
    refine bind_congr fun u => ?_
    exact ih u

/-- Stateful generalisation of `simulateQ_evalDist_congr`: two
`StateT (Heap Ident) (OracleComp I)`-valued query implementations that
agree on every (input, heap) pair *under `evalDist`* yield identical
evaluations of `(simulateQ _ A).run h` for every starting heap `h`.

The lemma to use when both sides of a game equivalence are stateful
heap-packages with the same identifier set and only their per-query
handlers differ up to distribution. Polymorphic in the import `I`, so it
applies both to probability-only games (`I = unifSpec`) and to compound
games such as `Package.par`-composites (`I = I₁ + I₂`). -/
lemma simulateQ_StateT_evalDist_congr {α : Type}
    {h₁ h₂ : QueryImpl E (StateT (Heap Ident) (OracleComp I))}
    (hh : ∀ (q : E.Domain) (h : Heap Ident),
        evalDist ((h₁ q).run h) = evalDist ((h₂ q).run h))
    (A : OracleComp E α) (h : Heap Ident) :
    evalDist ((simulateQ h₁ A).run h) =
      evalDist ((simulateQ h₂ A).run h) := by
  induction A using OracleComp.inductionOn generalizing h with
  | pure x => simp [simulateQ_pure, StateT.run_pure]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind, evalDist_bind]
    rw [hh t h]
    refine bind_congr fun p => ?_
    exact ih p.1 p.2

/-- Bijection-aware variant of `simulateQ_StateT_evalDist_congr`. If two
stateful handlers on *different* heap types `Heap Ident₁`, `Heap Ident₂`
agree under a heap-level bijection `φ : Heap Ident₁ ≃ Heap Ident₂`
pointwise at each query (via `Prod.map id φ.symm` on the output pair),
then their whole-adversary runs agree pointwise at corresponding starting
heaps.

Used when matching two heap representations that are isomorphic as
*states* but not propositionally equal as identifier sets (e.g. the
canonical `Heap.split` reshape `Heap (α ⊕ β) ≃ Heap α × Heap β` lifted
inside a `par`-composed package). -/
lemma simulateQ_StateT_evalDist_congr_of_bij {α : Type}
    {Ident₁ Ident₂ : Type}
    [CellSpec.{0, 0} Ident₁] [CellSpec.{0, 0} Ident₂]
    (h₁ : QueryImpl E (StateT (Heap Ident₁) (OracleComp I)))
    (h₂ : QueryImpl E (StateT (Heap Ident₂) (OracleComp I)))
    (φ : Heap Ident₁ ≃ Heap Ident₂)
    (hh : ∀ (q : E.Domain) (h : Heap Ident₁),
      evalDist ((h₁ q).run h) =
      evalDist (Prod.map id φ.symm <$> (h₂ q).run (φ h)))
    (A : OracleComp E α) (h : Heap Ident₁) :
    evalDist ((simulateQ h₁ A).run h) =
    evalDist (Prod.map id φ.symm <$> (simulateQ h₂ A).run (φ h)) := by
  induction A using OracleComp.inductionOn generalizing h with
  | pure x =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, Prod.map_apply,
      id_eq, Equiv.symm_apply_apply]
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_query, OracleQuery.cont_query,
      OracleQuery.input_query, id_map, StateT.run_bind, map_bind,
      evalDist_bind, evalDist_map, hh t h]
    simp only [map_eq_bind_pure_comp, bind_assoc]
    refine bind_congr fun p => ?_
    rcases p with ⟨x, h'⟩
    have hih := ih x (φ.symm h')
    rw [Equiv.apply_symm_apply] at hih
    simpa [Prod.map] using hih

end EvalDistCongr

/-! ### Functoriality of `runProb`

`Package.runProb` commutes with monadic map on the adversary: rerouting
the output of an adversary `A : OracleComp E α` through a post-processing
function `f : α → β` before running the package yields the same
distribution as running the package and then applying `f`. -/

lemma runProb_map {α β : Type} (P : Package unifSpec E Ident) (f : α → β)
    (A : OracleComp E α) :
    P.runProb (f <$> A) = f <$> P.runProb A := by
  change P.run (f <$> A) = f <$> P.run A
  unfold Package.run
  rw [simulateQ_map, map_bind]
  refine bind_congr fun h₀ => ?_
  rw [StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
    Functor.map_map]

end Package

end VCVio.HeapSSP
