/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ToMathlib.PFunctor.Free.Displayed.Append
public import ToMathlib.PFunctor.Free.Replicate

/-!
# State-indexed dependent chains over `FreeM`

`FreeM.stateChain` is the `n`-stage dependent composition where stage `i`
runs the tree `s i state` (with `state : Stage i`) and advances the state
via `advance i state path`. It is the FreeM-substrate analogue of
`Spec.stateChain`, and the displayed-layer `Decoration.stateChain` /
`Decoration.Over.stateChain` lift this iteration to per-node decorations.

Like `replicate`, `stateChain` is purely structural (iterated
`FreeM.append`), so it lives below the protocol layer.
-/

@[expose] public section

universe u v w w₂ w₃ w₄

namespace PFunctor
namespace FreeM

variable {P : PFunctor.{u, v}} {α : Type w}

/-- `n`-stage dependent composition: at stage `i` with state `state : Stage i`,
run `s i state`, then advance the state via `advance i state path` and continue. -/
def stateChain (a : α) (Stage : Nat → Type w)
    (s : (i : Nat) → Stage i → FreeM P α)
    (advance : (i : Nat) → (state : Stage i) → Path (s i state) → Stage (i + 1)) :
    (n : Nat) → (i : Nat) → Stage i → FreeM P α
  | 0, _, _ => FreeM.pure a
  | n + 1, i, state =>
      (s i state).append
        (fun path => stateChain a Stage s advance n (i + 1) (advance i state path))

@[simp, grind =]
theorem stateChain_zero (a : α) (Stage : Nat → Type w)
    (s : (i : Nat) → Stage i → FreeM P α)
    (advance : (i : Nat) → (state : Stage i) → Path (s i state) → Stage (i + 1))
    (i : Nat) (state : Stage i) :
    FreeM.stateChain a Stage s advance 0 i state = FreeM.pure a := rfl

@[simp]
theorem stateChain_succ (a : α) (Stage : Nat → Type w)
    (s : (i : Nat) → Stage i → FreeM P α)
    (advance : (i : Nat) → (state : Stage i) → Path (s i state) → Stage (i + 1))
    (n : Nat) (i : Nat) (state : Stage i) :
    FreeM.stateChain a Stage s advance (n + 1) i state =
      (s i state).append
        (fun path => FreeM.stateChain a Stage s advance n (i + 1) (advance i state path)) :=
  rfl

namespace Displayed
namespace Decoration

/-- Per-node decoration along a state chain: at stage `i` with state `state`,
use the per-stage decoration `deco i state`. -/
def stateChain {Γ : P.A → Type w₂}
    {a : α} {Stage : Nat → Type w}
    {s : (i : Nat) → Stage i → FreeM P α}
    {advance : (i : Nat) → (state : Stage i) → Path (s i state) → Stage (i + 1)}
    (deco : (i : Nat) → (state : Stage i) → Decoration Γ (s i state)) :
    (n : Nat) → (i : Nat) → (state : Stage i) →
    Decoration Γ (FreeM.stateChain a Stage s advance n i state)
  | 0, _, _ => ⟨⟩
  | n + 1, i, state =>
      Decoration.append (deco i state)
        (fun path => Decoration.stateChain deco n (i + 1) (advance i state path))

@[simp]
theorem stateChain_zero {Γ : P.A → Type w₂}
    {a : α} {Stage : Nat → Type w}
    {s : (i : Nat) → Stage i → FreeM P α}
    {advance : (i : Nat) → (state : Stage i) → Path (s i state) → Stage (i + 1)}
    (deco : (i : Nat) → (state : Stage i) → Decoration Γ (s i state))
    (i : Nat) (state : Stage i) :
    Decoration.stateChain (a := a) (advance := advance) deco 0 i state =
      (⟨⟩ : Decoration Γ (FreeM.stateChain a Stage s advance 0 i state)) :=
  rfl

@[simp]
theorem stateChain_succ {Γ : P.A → Type w₂}
    {a : α} {Stage : Nat → Type w}
    {s : (i : Nat) → Stage i → FreeM P α}
    {advance : (i : Nat) → (state : Stage i) → Path (s i state) → Stage (i + 1)}
    (deco : (i : Nat) → (state : Stage i) → Decoration Γ (s i state))
    (n : Nat) (i : Nat) (state : Stage i) :
    Decoration.stateChain (a := a) (advance := advance) deco (n + 1) i state =
      Decoration.append (deco i state)
        (fun path =>
          Decoration.stateChain (a := a) deco n (i + 1) (advance i state path)) :=
  rfl

namespace Over

/-- Dependent decoration layer along a state chain, fibered over a base
`Decoration.stateChain`. -/
def stateChain {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    {a : α} {Stage : Nat → Type w}
    {s : (i : Nat) → Stage i → FreeM P α}
    {advance : (i : Nat) → (state : Stage i) → Path (s i state) → Stage (i + 1)}
    {deco : (i : Nat) → (state : Stage i) → Decoration Γ (s i state)}
    (rDeco : (i : Nat) → (state : Stage i) →
      Decoration.Over Γ F (s i state) (deco i state)) :
    (n : Nat) → (i : Nat) → (state : Stage i) →
    Decoration.Over Γ F
      (FreeM.stateChain a Stage s advance n i state)
      (Decoration.stateChain deco n i state)
  | 0, _, _ => ⟨⟩
  | n + 1, i, state =>
      Decoration.Over.append (rDeco i state)
        (fun path => Over.stateChain rDeco n (i + 1) (advance i state path))

@[simp]
theorem stateChain_zero {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    {a : α} {Stage : Nat → Type w}
    {s : (i : Nat) → Stage i → FreeM P α}
    {advance : (i : Nat) → (state : Stage i) → Path (s i state) → Stage (i + 1)}
    {deco : (i : Nat) → (state : Stage i) → Decoration Γ (s i state)}
    (rDeco : (i : Nat) → (state : Stage i) →
      Decoration.Over Γ F (s i state) (deco i state))
    (i : Nat) (state : Stage i) :
    Decoration.Over.stateChain (a := a) (advance := advance) rDeco 0 i state =
      (⟨⟩ : Decoration.Over Γ F
        (FreeM.stateChain a Stage s advance 0 i state)
        (Decoration.stateChain deco 0 i state)) :=
  rfl

@[simp]
theorem stateChain_succ {Γ : P.A → Type w₂} {F : (a : P.A) → Γ a → Type w₃}
    {a : α} {Stage : Nat → Type w}
    {s : (i : Nat) → Stage i → FreeM P α}
    {advance : (i : Nat) → (state : Stage i) → Path (s i state) → Stage (i + 1)}
    {deco : (i : Nat) → (state : Stage i) → Decoration Γ (s i state)}
    (rDeco : (i : Nat) → (state : Stage i) →
      Decoration.Over Γ F (s i state) (deco i state))
    (n : Nat) (i : Nat) (state : Stage i) :
    Decoration.Over.stateChain (a := a) (advance := advance) rDeco (n + 1) i state =
      Decoration.Over.append (rDeco i state)
        (fun path =>
          Decoration.Over.stateChain (a := a) rDeco n (i + 1) (advance i state path)) :=
  rfl

/-- `Decoration.Over.map` commutes with `Over.stateChain`. -/
theorem map_stateChain {Γ : P.A → Type w₂}
    {F : (a : P.A) → Γ a → Type w₃} {G : (a : P.A) → Γ a → Type w₄}
    (η : ∀ a γ, F a γ → G a γ)
    {a : α} {Stage : Nat → Type w}
    {s : (i : Nat) → Stage i → FreeM P α}
    {advance : (i : Nat) → (state : Stage i) → Path (s i state) → Stage (i + 1)}
    {deco : (i : Nat) → (state : Stage i) → Decoration Γ (s i state)}
    (rDeco : (i : Nat) → (state : Stage i) →
      Decoration.Over Γ F (s i state) (deco i state)) :
    (n : Nat) → (i : Nat) → (state : Stage i) →
    Decoration.Over.map η
        (FreeM.stateChain a Stage s advance n i state)
        (Decoration.stateChain deco n i state)
        (Decoration.Over.stateChain rDeco n i state) =
      Decoration.Over.stateChain
        (fun j t => Decoration.Over.map η (s j t) (deco j t) (rDeco j t)) n i state
  | 0, _, _ => rfl
  | n + 1, i, state => by
      change Decoration.Over.map η ((s i state).append _) _
          (Decoration.Over.append (rDeco i state) _) = _
      rw [Decoration.Over.map_append η (s i state) _
            (deco i state) _ (rDeco i state) _]
      refine congrArg
        (Decoration.Over.append
          (Decoration.Over.map η (s i state) (deco i state) (rDeco i state))) ?_
      funext path
      exact map_stateChain η rDeco n (i + 1) (advance i state path)

end Over

/-- `Decoration.map` commutes with `Decoration.stateChain`. -/
theorem map_stateChain {Γ : P.A → Type w₂} {Δ : P.A → Type w₃}
    (f : ∀ a, Γ a → Δ a)
    {a : α} {Stage : Nat → Type w}
    {s : (i : Nat) → Stage i → FreeM P α}
    {advance : (i : Nat) → (state : Stage i) → Path (s i state) → Stage (i + 1)}
    (deco : (i : Nat) → (state : Stage i) → Decoration Γ (s i state)) :
    (n : Nat) → (i : Nat) → (state : Stage i) →
    Decoration.map f
        (FreeM.stateChain a Stage s advance n i state)
        (Decoration.stateChain deco n i state) =
      Decoration.stateChain
        (fun j t => Decoration.map f (s j t) (deco j t)) n i state
  | 0, _, _ => rfl
  | n + 1, i, state => by
      change Decoration.map f ((s i state).append _)
          (Decoration.append (deco i state) _) = _
      rw [Decoration.map_append f (s i state) _ (deco i state) _]
      congr 1; funext path
      exact map_stateChain f deco n (i + 1) (advance i state path)

end Decoration
end Displayed
end FreeM
end PFunctor
