/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
import Lean
import Loom.Tactic.VCGen
import Loom.Test.Driver
import Loom.Test.Specs

open Lean Parser Meta Elab Tactic Sym Loom Lean.Order Std.Do'

/-!
Same benchmark as `vcgen_add_sub_cancel` but using a deep transformer stack.
-/

abbrev M := ExceptT String <| ReaderT String <| ExceptT Nat <| StateT Nat <| ExceptT Unit <| StateM Unit

/-
Known issues:
* Using `StateT String` instead of `ReaderT String` picks the wrong spec for `MonadStateOf.get`; namely that on `String`.
  It seems we need to disambiguate discrimination tree lookup results with defeq.
* Even using `ReaderT String` it doesn't work. TODO: Why?
* But just using `ExceptT String` works.
-/

def step (v : Nat) : M Unit := do
  let s ← getThe Nat
  set (s + v)
  let s ← getThe Nat
  set (s - v)

def loop (n : Nat) : M Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post epost s₁ s₂, post s₁ s₂ ⟨⟩ ⊑ wp (loop n) (fun _ => post) epost s₁ s₂ ⟨⟩

@[lspec high]
theorem Spec.M_getThe_Nat :
  Triple (fun s₁ s₂ => post s₂ s₁ s₂) (getThe (m := M) Nat) post epost := by
  sorry
  -- sorry

@[lspec high]
theorem Spec.M_set_Nat (n : Nat) :
  Triple (fun s₁ _ => post ⟨⟩ s₁ n) (set (m := M) n) post epost := by
  sorry

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def runTests := runBenchUsingTactic ``Goal [``loop, ``step] `(tactic| (intro post epost s₁ s₂; mvcgen' with grind)) `(tactic| fail)

#eval runTests [1000]
