import Lean
import Loom.Test.Driver
import Loom.Triple.SpecLemmas
import Loom.Test.Specs
import Loom.Tactic.VCGen

open Loom Lean Meta Order Std.Do'

-- Spec for MonadStateOf.get (defined in VCGen.lean's test section, replicated here)
@[lspec high] theorem spec_get_StateT {m : Type u → Type v} {Pred EPred : Type u}
    [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
    {σ : Type u} (post : σ → σ → Pred) (epost : EPred) :
    Triple (fun s => post s s) (get : StateT σ m σ) post epost := by
  exact ⟨WP.get_StateT_wp post epost⟩

-- -- Specs for the standalone `get`/`set` functions (which elaborate to MonadState.get/set,
-- -- a different head constant from MonadStateOf.get/set used above).
-- @[lspec high] theorem spec_get_StateT' {m : Type u → Type v} {Pred EPred : Type u}
--     [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
--     {σ : Type u} (post : σ → σ → Pred) (epost : EPred) :
--     Triple (fun s => post s s) (get : StateT σ m σ) post epost :=
--   by simpa using (spec_get_StateT (m := m) (Pred := Pred) (EPred := EPred) (σ := σ) post epost)

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ post s, post s ⊑ wp (loop n) (fun _ => post) ⟨⟩ s

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

-- set_option trace.Loom.Tactic.vcgen true

def runTests := runBenchUsingTactic
    ``Goal [``loop, ``step]
    `(tactic| (intro post; mvcgen' with grind))
    `(tactic| fail)

-- example : Goal 1 := by
--   intro post s
--   simp only [loop, step]
--   mvcgen' with grind


-- #eval
--   runBenchUsingTactic
--     ``Goal [``loop, ``step]
--     `(tactic| (intro post s; mvcgen' with grind))
--     `(tactic| skip)
--     [1000]

-- #eval
--   runBenchUsingTactic
--     ``Goal [``loop, ``step]
--     `(tactic| (intro post s; mvcgen'))
--     `(tactic| grind)
--     [1000]
