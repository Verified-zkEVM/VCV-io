/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Entropy Smoothing

This file defines the entropy-smoothing distinguishing game used by hashed ElGamal-style
constructions: the adversary distinguishes a real hash output `hash hk (z • g)` from an
independent uniform element of the output space.
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace EntropySmoothing

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {HK : Type} [SampleableType HK]
variable {M : Type} [AddCommGroup M] [SampleableType M] [DecidableEq M] [Fintype M]

/-- Real entropy-smoothing experiment. The adversary sees `(hk, hash hk (z • g))`
for uniform `hk` and `z`, and tries to distinguish this from the ideal experiment. -/
def realExp (g : G) (hash : HK → G → M) (adversary : HK × M → ProbComp Bool) :
    ProbComp Bool := do
  let hk ← $ᵗ HK
  let z ← $ᵗ F
  adversary (hk, hash hk (z • g))

/-- Ideal entropy-smoothing experiment. The adversary sees `(hk, h)` for independent
uniform `hk` and uniform `h : M`. -/
def idealExp (adversary : HK × M → ProbComp Bool) : ProbComp Bool := do
  let hk ← $ᵗ HK
  let h ← $ᵗ M
  adversary (hk, h)

/-- Entropy-smoothing distinguishing advantage. -/
noncomputable def advantage (g : G) (hash : HK → G → M)
    (adversary : HK × M → ProbComp Bool) : ℝ :=
  |(Pr[= true | realExp F g hash adversary]).toReal -
    (Pr[= true | idealExp adversary]).toReal|

end EntropySmoothing
