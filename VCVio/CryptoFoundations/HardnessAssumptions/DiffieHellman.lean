/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.HardnessAssumptions.HardHomogeneousSpace

/-!
# Diffie-Hellman Assumptions

This file defines the discrete log (DLog), computational Diffie-Hellman (CDH), and
decisional Diffie-Hellman (DDH) problems over an abstract finite commutative group.

The group is parameterized by a type `G` with `CommGroup`, `Fintype`, `DecidableEq`, and
`SampleableType` instances, together with a distinguished generator `g`.

Exponents are sampled uniformly from `Fin (Fintype.card G)`.

## Connection to Hard Homogeneous Spaces

These are concrete instantiations of the abstract experiments in `HardHomogeneousSpace.lean`:
- DLog ≈ vectorization (find the "vector" between two points)
- CDH ≈ parallelization (complete a parallelogram)
- DDH ≈ parallel testing (distinguish real from random fourth point)

TODO: formalize the `AddTorsor` instance making this reduction explicit.
-/

open OracleComp OracleSpec ENNReal

namespace DiffieHellman

variable {G : Type} [CommGroup G] [Fintype G] [DecidableEq G] [SampleableType G]

section DLog

/-- A discrete log adversary: given `g` and `g^a`, outputs a candidate exponent. -/
def DLogAdversary (G : Type) := G → G → ProbComp ℕ

/-- Discrete log experiment: the adversary wins if it recovers the exponent `a`
from `(g, g^a)`. -/
def dlogExp (g : G) (adversary : DLogAdversary G) : ProbComp Bool := do
  let a ← $ᵗ Fin (Fintype.card G)
  let h := g ^ a.val
  let a' ← adversary g h
  return decide (g ^ a' = h)

end DLog

section CDH

/-- A CDH adversary: given `(g, g^a, g^b)`, outputs a candidate for `g^(a*b)`. -/
def CDHAdversary (G : Type) := G → G → G → ProbComp G

/-- CDH experiment: the adversary wins if it computes `g^(a*b)` from `(g, g^a, g^b)`. -/
def cdhExp (g : G) (adversary : CDHAdversary G) : ProbComp Bool := do
  let a ← $ᵗ Fin (Fintype.card G)
  let b ← $ᵗ Fin (Fintype.card G)
  let result ← adversary g (g ^ a.val) (g ^ b.val)
  return decide (result = g ^ (a.val * b.val))

end CDH

section DDH

/-- A DDH adversary: given `(g, g^a, g^b, h)`, guesses whether `h = g^(a*b)`. -/
def DDHAdversary (G : Type) := G → G → G → G → ProbComp Bool

/-- DDH experiment: the adversary must distinguish `(g, g^a, g^b, g^(ab))` from
`(g, g^a, g^b, g^c)` where `c` is uniformly random. -/
def ddhExp (g : G) (adversary : DDHAdversary G) : ProbComp Bool := do
  let a ← $ᵗ Fin (Fintype.card G)
  let b ← $ᵗ Fin (Fintype.card G)
  let bit ← $ᵗ Bool
  let h ← if bit then
    pure (g ^ (a.val * b.val))
  else
    (fun c => g ^ c.val) <$> ($ᵗ Fin (Fintype.card G))
  let b' ← adversary g (g ^ a.val) (g ^ b.val) h
  return (bit == b')

noncomputable def ddhAdvantage (g : G) (adversary : DDHAdversary G) : ℝ≥0∞ :=
  Pr[= true | ddhExp g adversary] - 1 / 2

end DDH

end DiffieHellman

/-! ## Old commented code (for reference)

-- namespace DiffieHellman
--
-- def DHVec (p : ℕ) [Fact (Nat.Prime (p + 1))] : Type := { x : ZMod (p + 1) // x ≠ 0 }
-- ...
-- (the old approach tried to build AddGroup/HomogenousSpace instances on ZMod units
-- directly, but was mathematically incomplete with many sorry's)
--
-- end DiffieHellman
-/
