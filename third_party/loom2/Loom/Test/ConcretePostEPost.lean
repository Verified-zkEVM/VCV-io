import Lean
import Loom.Test.Driver
import Loom.Tactic.VCGen

open Loom Lean Meta Order Std.Do'

/-
Benchmark for the spec-generalization path where both `post` and `epost` are concrete in
an `@[lspec]` theorem. `mvcgen'` must abstract them back out using `WP.wp_consequence_econs`.
-/

def concreteGet : StateM Nat Nat := get

@[lspec high]
theorem spec_concreteGet :
    ⦃ fun s => s = s ⦄ concreteGet ⦃ x, fun s => x = s ⦄ := by
  simpa [concreteGet] using
    (Spec.get_StateT
      (m := Id) (Pred := Prop) (EPred := EPost.nil)
      (σ := Nat) (post := fun x s => x = s) (epost := ⟨⟩))

def step (n : Nat) : StateM Nat Unit := do
  let x ← concreteGet
  set (x + n + 1)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n + 1 => step n; loop n

def Goal (n : Nat) : Prop :=
  ∀ s, True ⊑ wp (loop n) (fun _ _ => True) ⟨⟩ s

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def runTests := runBenchUsingTactic
    ``Goal [``loop, ``step]
    `(tactic| (intro s; mvcgen' with grind))
    `(tactic| fail)

-- #eval runTests [1000]
