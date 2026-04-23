/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.SSP.Advantage
import VCVio.SSP.Composition

/-!
# State-Separating Proofs: Distributional Equivalence

`Package.DistEquiv G₀ G₁` (notation `G₀ ≡ᵈ G₁`) says that two probability-only packages produce
identical output distributions against *every* adversary, on every output type. This is SSProve's
"perfect equivalence": the Boolean distinguishing advantage between `G₀` and `G₁` is zero on every
adversary, but more generally `G₀.runProb A` and `G₁.runProb A` agree under `evalDist` for any
output type.

The state types `σ₀, σ₁` of the two games may be unrelated; only their behaviour against adversaries
matters. This is exactly the "behavioural equivalence" of state-separating proofs.

## API surface

* **Relation laws**: `refl`, `symm`, `trans`, plus a `Trans` instance for `calc` blocks and a named
  `Equivalence` witness when the state type is fixed.
* **Constructors**:
  * `of_run_evalDist`: from a per-adversary `evalDist` equality (the unfolded definition).
  * `of_step`: same state type, agree per-query under `evalDist`. The lemma version of
    `Package.simulateQ_StateT_evalDist_congr` from `VCVio.SSP.Advantage`.
  * `of_step_bij`: bijected state type, agree per-query under `evalDist` modulo the bijection. The
    lemma version of `Package.simulateQ_StateT_evalDist_congr_of_bij`.
* **Bridge to `Package.advantage`**: `advantage_left`, `advantage_right`, `advantage_zero`. A
  `≡ᵈ`-hop on either side preserves the Boolean distinguishing advantage.
* **Bridge to `runProb`**: `runProb_evalDist_eq`, the inverse of `of_run_evalDist`.

## Composition

* **`link` congruence in the inner argument**: `link_inner_congr` swaps the inner game of a
  linked composition along a `≡ᵈ`-hop, leveraging `Package.run_link_eq_run_shiftLeft`. The
  bound (perfect) case is exactly the SSProve "ε = 0 in the inner game" reduction.
* The outer-side congruence and `par_congr` are not in this file: the former requires a notion
  of equivalence for *open* packages (per-handler under `evalDist`), and the latter requires
  parallel-composition structural reductions that have not yet been proved.
-/

universe uₘ uₑ

open OracleSpec OracleComp ProbComp

namespace VCVio.SSP

namespace Package

variable {ιₑ : Type uₑ} {E : OracleSpec.{uₑ, 0} ιₑ}

/-- Two probability-only packages are *distributionally equivalent* if they produce the same
output distribution against every adversary, on every output type.

Equivalent characterisations:
* The Boolean distinguishing advantage `G₀.advantage G₁ A` is zero on every Boolean-valued
  adversary `A` (`DistEquiv.advantage_zero`).
* For every `α` and every adversary `A : OracleComp E α`, `evalDist (G₀.runProb A) =
  evalDist (G₁.runProb A)` (the literal definition).

The state types `σ₀, σ₁` of the two games are independent: only the export interface and the
resulting output distribution matter from an adversary's point of view. -/
def DistEquiv {σ₀ σ₁ : Type}
    (G₀ : Package unifSpec E σ₀) (G₁ : Package unifSpec E σ₁) : Prop :=
  ∀ {α : Type} (A : OracleComp E α), evalDist (G₀.runProb A) = evalDist (G₁.runProb A)

@[inherit_doc DistEquiv]
scoped infix:50 " ≡ᵈ " => Package.DistEquiv

namespace DistEquiv

variable {σ σ₀ σ₁ σ₂ : Type}

/-! ### Relation laws -/

@[refl]
protected theorem refl (G : Package unifSpec E σ) : G ≡ᵈ G := fun _ => rfl

@[symm]
protected theorem symm {G₀ : Package unifSpec E σ₀} {G₁ : Package unifSpec E σ₁}
    (h : G₀ ≡ᵈ G₁) : G₁ ≡ᵈ G₀ :=
  fun A => (h A).symm

@[trans]
protected theorem trans
    {G₀ : Package unifSpec E σ₀} {G₁ : Package unifSpec E σ₁} {G₂ : Package unifSpec E σ₂}
    (h₀₁ : G₀ ≡ᵈ G₁) (h₁₂ : G₁ ≡ᵈ G₂) : G₀ ≡ᵈ G₂ :=
  fun A => (h₀₁ A).trans (h₁₂ A)

instance trans_instance : @Trans (Package unifSpec E σ₀) (Package unifSpec E σ₁)
    (Package unifSpec E σ₂) DistEquiv DistEquiv DistEquiv where
  trans := DistEquiv.trans

/-- When the state type is fixed, `≡ᵈ` is an `Equivalence`. -/
theorem _root_.VCVio.SSP.Package.equivalence_distEquiv (E : OracleSpec.{uₑ, 0} ιₑ) (σ : Type) :
    Equivalence (DistEquiv (E := E) (σ₀ := σ) (σ₁ := σ)) where
  refl := DistEquiv.refl
  symm := DistEquiv.symm
  trans := DistEquiv.trans

/-! ### Constructors -/

/-- Build a `DistEquiv` from the literal per-adversary `evalDist` equality. This is the unfolded
definition, exposed for clients that already have the distribution equality in hand. -/
theorem of_run_evalDist
    {G₀ : Package unifSpec E σ₀} {G₁ : Package unifSpec E σ₁}
    (h : ∀ {α : Type} (A : OracleComp E α),
        evalDist (G₀.runProb A) = evalDist (G₁.runProb A)) :
    G₀ ≡ᵈ G₁ := h

/-- Recover the per-adversary `evalDist` equality from a `DistEquiv` witness. The inverse of
`of_run_evalDist`. -/
theorem runProb_evalDist_eq
    {G₀ : Package unifSpec E σ₀} {G₁ : Package unifSpec E σ₁}
    (h : G₀ ≡ᵈ G₁) {α : Type} (A : OracleComp E α) :
    evalDist (G₀.runProb A) = evalDist (G₁.runProb A) := h A

/-- Build a `DistEquiv` from a per-adversary *propositional* equality at the `runProb` level. -/
theorem of_run_eq
    {G₀ : Package unifSpec E σ₀} {G₁ : Package unifSpec E σ₁}
    (h : ∀ {α : Type} (A : OracleComp E α), G₀.runProb A = G₁.runProb A) :
    G₀ ≡ᵈ G₁ :=
  fun A => by rw [h A]

/-- **Step constructor (same state).** Two probability-only packages with identical state type are
distributionally equivalent if their inits agree under `evalDist` and their per-query handlers
agree under `evalDist` on every state.

This is the lemma form of `Package.simulateQ_StateT_evalDist_congr` from
`VCVio.SSP.Advantage`, lifted to the package level: the per-handler hypothesis
discharges the simulation step, and the init hypothesis discharges the setup step. -/
theorem of_step {G₀ G₁ : Package unifSpec E σ}
    (h_init : evalDist G₀.init = evalDist G₁.init)
    (h_impl : ∀ (q : E.Domain) (s : σ),
        evalDist ((G₀.impl q).run s) = evalDist ((G₁.impl q).run s)) :
    G₀ ≡ᵈ G₁ := by
  intro α A
  change evalDist (G₀.run A) = evalDist (G₁.run A)
  unfold Package.run
  rw [evalDist_bind, evalDist_bind, h_init]
  refine bind_congr fun s₀ => ?_
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  congr 1
  exact simulateQ_StateT_evalDist_congr h_impl A s₀

/-- **Step constructor (under state bijection).** Two probability-only packages with isomorphic
state types `σ₀ ≃ σ₁` are distributionally equivalent if their inits agree under `evalDist`
modulo the bijection (RHS init is mapped through `φ.symm`) and their per-query handlers agree
under `evalDist` modulo the bijection (RHS handler output is mapped through `Prod.map id φ.symm`).

This is the lemma form of `Package.simulateQ_StateT_evalDist_congr_of_bij` from
`VCVio.SSP.Advantage`, lifted to the package level: the per-handler hypothesis with bijection
discharges the simulation step, and the init hypothesis discharges the setup step.

This is the constructor used in `VCVio.CryptoFoundations.FiatShamir.Sigma.SSP.Hops` to relate
`cmaSim` to `cmaToNma.link nma`, where the state types are isomorphic but not propositionally
equal. -/
theorem of_step_bij
    (G₀ : Package unifSpec E σ₀) (G₁ : Package unifSpec E σ₁) (φ : σ₀ ≃ σ₁)
    (h_init : evalDist G₀.init = evalDist (φ.symm <$> G₁.init))
    (h_impl : ∀ (q : E.Domain) (s : σ₀),
        evalDist ((G₀.impl q).run s) =
          evalDist (Prod.map id φ.symm <$> (G₁.impl q).run (φ s))) :
    G₀ ≡ᵈ G₁ := by
  intro α A
  change evalDist (G₀.run A) = evalDist (G₁.run A)
  unfold Package.run
  rw [evalDist_bind, evalDist_bind, h_init, evalDist_map]
  -- LHS bind is now `(φ.symm <$> evalDist G₁.init) >>= …`. Push the map into the bind.
  rw [bind_map_left]
  refine bind_congr fun s₁ => ?_
  -- Goal: evalDist ((simulateQ G₀.impl A).run' (φ.symm s₁))
  --      = evalDist ((simulateQ G₁.impl A).run' s₁)
  rw [StateT.run'_eq, StateT.run'_eq, evalDist_map, evalDist_map]
  -- Apply the bijected congruence at state s₀ := φ.symm s₁; then `φ (φ.symm s₁) = s₁`.
  have hbij := simulateQ_StateT_evalDist_congr_of_bij G₀.impl G₁.impl φ h_impl A (φ.symm s₁)
  rw [Equiv.apply_symm_apply] at hbij
  rw [hbij, evalDist_map]
  -- Goal: Prod.fst <$> Prod.map id φ.symm <$> evalDist (...)
  --     = Prod.fst <$> evalDist (...)
  -- Combine the two `<$>` and collapse `(Prod.map id φ.symm a).1 = a.1`.
  simp only [Functor.map_map, Prod.map_fst, id_eq]

/-! ### Bridge to `Package.advantage` -/

/-- A distributional equivalence on the LEFT side preserves the Boolean distinguishing
advantage. -/
theorem advantage_left
    {G₀ : Package unifSpec E σ₀} {G₀' : Package unifSpec E σ}
    (h : G₀ ≡ᵈ G₀')
    (G₁ : Package unifSpec E σ₁) (A : OracleComp E Bool) :
    G₀.advantage G₁ A = G₀'.advantage G₁ A :=
  advantage_eq_of_evalDist_runProb_eq (h A)

/-- A distributional equivalence on the RIGHT side preserves the Boolean distinguishing
advantage. -/
theorem advantage_right
    (G₀ : Package unifSpec E σ₀)
    {G₁ : Package unifSpec E σ₁} {G₁' : Package unifSpec E σ}
    (h : G₁ ≡ᵈ G₁') (A : OracleComp E Bool) :
    G₀.advantage G₁ A = G₀.advantage G₁' A :=
  advantage_eq_of_evalDist_runProb_eq_right (h A)

/-- Distributionally equivalent packages have zero distinguishing advantage. -/
theorem advantage_zero
    {G₀ : Package unifSpec E σ₀} {G₁ : Package unifSpec E σ₁}
    (h : G₀ ≡ᵈ G₁) (A : OracleComp E Bool) :
    G₀.advantage G₁ A = 0 := by
  rw [advantage_left h G₁ A, advantage_self]

/-! ### Compositional congruences (`link`) -/

section LinkCongr

variable {ιₘ : Type uₘ} {M : OracleSpec.{uₘ, 0} ιₘ}
variable {σ_P : Type}

/-- **Inner-game congruence for `link`.** Swapping the inner game of a linked composition along
a `≡ᵈ`-hop preserves distributional equivalence: the outer reduction `P` is absorbed into the
shifted adversary `P.shiftLeft A`, and the equivalence on the inner game closes the proof.

This is the SSP "replace the inner game" rule, the program-level counterpart of
`Package.advantage_link_left_eq_advantage_shiftLeft` in `VCVio.SSP.Hybrid`. -/
theorem link_inner_congr (P : Package M E σ_P)
    {Q₀ : Package unifSpec M σ₀} {Q₁ : Package unifSpec M σ₁}
    (h : Q₀ ≡ᵈ Q₁) :
    P.link Q₀ ≡ᵈ P.link Q₁ := by
  intro α A
  change evalDist ((P.link Q₀).run A) = evalDist ((P.link Q₁).run A)
  rw [run_link_eq_run_shiftLeft, run_link_eq_run_shiftLeft]
  exact h (P.shiftLeft A)

end LinkCongr

end DistEquiv

end Package

end VCVio.SSP
