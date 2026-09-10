/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import VCVio.EvalDist.Notation
public import VCVio.EvalDist.Defs.Instances
public import VCVio.EvalDist.Instances.OptionT
public import VCVio.OracleComp.ProbComp

/-!
# Sampling-block notation checks

These checks exercise ordinary `do` binding and control flow, generic probability lemmas,
failure without normalization, and the raw-distribution observation used by ArkLib.
-/

public section

open OracleComp
open scoped ProbabilityTheory

namespace VCVioTest.ProbabilityNotation

section generic

universe v

variable {m : Type → Type v} [Monad m] [LawfulMonad m]
  [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
  {α β : Type}

example (mx : m α) (p : α → Prop) :
    Pr_{let x ← mx}[p x] = Pr[p | mx] :=
  probOutput_true_eq_probEvent mx p

example (mx : m α) (p : α → Prop) :
    Pr_{{let x ← mx}}[p x] = Pr[p | mx] :=
  probOutput_true_eq_probEvent mx p

example (mx : m α) (p : α → Bool) :
    Pr_{let x ← mx}[p x] = Pr[(fun x => p x = true) | mx] :=
  probOutput_true_eq_probEvent mx _

example (mx : m α) (f : α → m β) (p : β → Prop) :
    Pr_{let x ← mx; let y ← f x}[p y] = Pr[p | mx >>= f] := by
  simpa only [bind_assoc] using probOutput_true_eq_probEvent (mx >>= f) p

example (mx : m (Nat × Nat)) :
    Pr_{let (x, y) ← mx; let z := x + y}[z = y + x] = Pr[fun _ => True | mx] := by
  simpa only [Nat.add_comm, eq_self] using
    probOutput_true_eq_probEvent mx (fun _ => True)

example (mx : m Nat) (p : Nat → Prop) :
    Pr_{
      let x ← mx
      let mut y := x
      y := y + 1
    }[p y] = Pr[(fun x => p (x + 1)) | mx] :=
  probOutput_true_eq_probEvent mx _

example (mx : m Nat) :
    Pr_{
      let x ← mx
      if x = 0 then return False
    }[True] = Pr[(fun x => x ≠ 0) | mx] := by
  have h : (fun x : Nat => if x = 0 then (pure False : m Prop) else pure True) =
      (fun x => pure (x ≠ 0)) := by
    funext x
    by_cases hx : x = 0 <;> simp [hx]
  change Pr[= True | mx >>= _] = _
  rw [h]
  exact probOutput_true_eq_probEvent mx _

end generic

example (p : PMF Nat) (event : Nat → Prop) :
    Pr_{let x ← p}[event x] = (do let x ← p; return event x) True :=
  PMF.probOutput_eq_apply _ _

example (mx : ProbComp Bool) :
    Pr_{let b ← mx}[b] = Pr[= true | mx] := by
  simp only [probOutput_true_eq_probEvent, probEvent_eq_eq_probOutput]

example : Pr_{let _ ← (failure : OptionT ProbComp Unit)}[True] = 0 := by
  simp

example (mx : OptionT ProbComp Nat) :
    Pr_{let _ ← mx}[True] = 1 - Pr[⊥ | mx] := by
  simp only [probOutput_true_eq_probEvent, probEvent_True_eq_sub]

end VCVioTest.ProbabilityNotation
