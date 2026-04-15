/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

/-!
# Sender / receiver roles

`Interaction.Role` marks which side of a two-party protocol acts at each node.
`Action` and `Dual` package the active/passive node shapes for the focal side
and its environment; `interact` runs one round.
-/

universe u

namespace Interaction

/-- Which side speaks at a protocol node: sender (proposes a move) or receiver (observes). -/
inductive Role where
  | sender
  | receiver

namespace Role

/-- Exchange sender and receiver (duality on the role type). -/
def swap : Role → Role
  | .sender => .receiver
  | .receiver => .sender

/-- Focal party's action type: when acting, the focal party may use effects to
choose the next move itself; when observing, it responds to any received move. -/
def Action (role : Role) (m : Type u → Type u) (X : Type u) (Cont : X → Type u) : Type u :=
  match role with
  | .sender => m ((x : X) × Cont x)
  | .receiver => (x : X) → m (Cont x)

/-- Environment / dual view: sender branch observes the chosen move and may
continue effectfully; receiver branch samples the move and continuation. -/
def Dual (role : Role) (m : Type u → Type u) (X : Type u) (Cont : X → Type u) : Type u :=
  match role with
  | .sender => (x : X) → m (Cont x)
  | .receiver => m ((x : X) × Cont x)

/-- Run one round: pair an `Action` with the matching `Dual` and continue in `k`. -/
def interact {m : Type u → Type u} [Monad m] {X : Type u}
    {ACont DCont : X → Type u} {Result : Type u} :
    (role : Role) → role.Action m X ACont → role.Dual m X DCont →
    ((x : X) → ACont x → DCont x → m Result) → m Result
  | .sender, mAction, dualFn, k => do
      let ⟨x, cont⟩ ← mAction
      let dualCont ← dualFn x
      k x cont dualCont
  | .receiver, recvFn, mDual, k => do
      let ⟨x, dualCont⟩ ← mDual
      let cont ← recvFn x
      k x cont dualCont

end Role
end Interaction
