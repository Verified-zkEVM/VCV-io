/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio

/-!
# ElGamal Encryption

This file defines an anologue of the ElGamal Encryption scheme and proves it is IND-CPA secure
We use `AddTorsor` as a natural analogue to a hard homogeneous space, which gives the
standard ElGamal algorithm when the group action is exponentiation in a finite field.
-/

open OracleSpec OracleComp AsymmEncAlg

section scratch

-- TODO: we need automation for this. Does iris stuff help here?
lemma pull_up_4_helper {ι : Type*} {spec : OracleSpec ι} [spec.FiniteRange]
    {α β γ δ ε : Type}
    (oa : OracleComp spec α) (ob : OracleComp spec β)
    (oc : OracleComp spec γ) (od : OracleComp spec δ)
    (oe : α → β → γ → δ → OracleComp spec ε) (z : ε) :
    [= z | do let a ← oa; let b ← ob; let c ← oc; let d ← od; oe a b c d] =
      [= z | do let d ← od; let a ← oa; let b ← ob; let c ← oc; oe a b c d] := by
  sorry

lemma probOutput_uniformSelect_bool_bind_eq_add {α : Type}
    (oa : Bool → ProbComp α) (x : α) : -- should be anything $ᵗ Bool can lift to
    [= x | ($ᵗ Bool) >>= oa] = [= x | oa true] / 2 + [= x | oa false] / 2 := by
  sorry

end scratch

/-- Elgemal-style encryption adapted to a homogeneous space with group structure on points.
Messages are base points in `P` (in practice this is some encoding of messages),
The public key is a pair of base points in `P` chosen uniformly at random,
and the secret key is their vectorization in `G`. Signatures are also a pair of base points. -/
@[simps!] def elgamalAsymmEnc (G P : Type) [SelectableType G] [SelectableType P]
    [AddGroup G] [Group P] [AddTorsor G P] : AsymmEncAlg ProbComp
    (M := P) (PK := P × P) (SK := G) (C := P × P) where
  keygen := do
    let x₀ ←$ᵗ P; let sk ←$ᵗ G
    return ((x₀, sk +ᵥ x₀), sk)
  encrypt := fun (x₀, pk) msg => do
    let g ←$ᵗ G
    return (g +ᵥ x₀, msg * (g +ᵥ pk))
  decrypt := fun sk (c₁, c₂) => do
    return c₂ / (sk +ᵥ c₁)
  __ := ExecutionMethod.default

namespace elgamalAsymmEnc

variable {G P : Type} [SelectableType G] [SelectableType P]
    [AddCommGroup G] [Group P] [AddTorsor G P]

@[simp] lemma toExecutionMethod_eq :
    (elgamalAsymmEnc G P).toExecutionMethod = ExecutionMethod.default := rfl

theorem Correct [DecidableEq P] : (elgamalAsymmEnc G P).PerfectlyCorrect := by
  have : ∀ (msg x : P) (g₁ g₂ : G), msg * (g₂ +ᵥ (g₁ +ᵥ x)) / (g₁ +ᵥ (g₂ +ᵥ x)) = msg :=
    fun m x g₁ g₂ => by rw [vadd_comm g₁ g₂ x, mul_div_cancel_right]
  simp [this]

section IND_CPA

def IND_CPA_parallelTesting_reduction
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) :
    parallelTestingAdversary G P := fun x x₁ x₂ x₃ => do
  let so : QueryImpl (P × P →ₒ P × P) ProbComp := ⟨fun (query () (m₁, _m₂)) =>
    return (x₂, m₁ * x₃)⟩
  simulateQ (idOracle ++ₛₒ so) (adversary (x, x₁))

/-- The reduction from ElGamal IND-CPA to parallel testing succeeds exactly as often
as the original adversary does, because the simulation oracle is exact. -/
theorem IND_CPA_advantage_eq_parallelTesting_advantage [DecidableEq G] [DecidableEq P]
    (adversary : (elgamalAsymmEnc G P).IND_CPA_adversary) :
    (IND_CPA_advantage adversary) =
      (parallelTestingAdvantage (IND_CPA_parallelTesting_reduction adversary)) := by
  refine congr_arg (· - 1/2) ?_
  simp only [probOutput_IND_CPA_experiment_eq_add, parallelTesting_experiment,
    elgamalAsymmEnc_keygen, StateT.run'_eq, guard_eq, bind_map_left, bind_assoc,
    Nat.cast_ofNat, Bool.not_eq_true, pure_bind]
  rw [pull_up_4_helper]
  rw [probOutput_uniformSelect_bool_bind_eq_add]
  congr 2
  · refine probOutput_bind_congr' _ _ fun x => ?_
    refine probOutput_bind_congr' _ _ fun g₁ => ?_
    unfold IND_CPA_parallelTesting_reduction IND_CPA_queryImpl'
    simp
    sorry -- caching simulation oracles behave the same on same inputs
  · refine probOutput_bind_congr' _ _ fun x => ?_
    refine probOutput_bind_congr' _ _ fun g₁ => ?_
    unfold IND_CPA_parallelTesting_reduction IND_CPA_queryImpl'
    simp
    sorry -- random things look random

end IND_CPA

end elgamalAsymmEnc
