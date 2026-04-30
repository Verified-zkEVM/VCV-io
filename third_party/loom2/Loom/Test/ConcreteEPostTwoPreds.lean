import Lean
import Loom.Test.Driver
import Loom.Tactic.VCGen

open Loom Lean Meta Order Std.Do'

abbrev M := ExceptT Nat (Except String)

def throwNatOrString (n : Nat) : M PUnit := do
  if n = 30 then
    throwThe Nat 7
  else if n = 239 then
    throwThe String "inner"
  else
    pure ()

@[lspec high]
theorem spec_throwNatOrString (n : Nat) :
    Triple True (throwNatOrString n) (fun _ => True) epost⟨(· = 7), (· = "inner")⟩ := by
  rw [Triple.iff]; unfold throwNatOrString;
  mvcgen' <;> grind

def step (n : Nat) : ExceptT Nat (Except String) PUnit := do
  throwNatOrString n
  pure ()

def loop (n : Nat) : ExceptT Nat (Except String) PUnit := do
  match n with
  | 0 => pure ()
  | n + 1 =>
    step n
    loop n

def Goal (n : Nat) : Prop :=
  True ⊑ wp (loop n) (fun _ => True) epost⟨(· = 7), (· = "inner")⟩

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

def runTests := runBenchUsingTactic
    ``Goal [``loop, ``step]
    `(tactic| mvcgen' with grind)
    `(tactic| fail)

-- #eval runTests [1000]
