/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FujisakiOkamoto.Defs
import VCVio.CryptoFoundations.AsymmEncAlg.IND_CPA
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.QueryTracking.RandomOracle

/-!
# Fujisaki-Okamoto T Transform

This file defines the derandomizing T transform:

- coins are derived from a random oracle on the plaintext
- decryption re-derives the coins and checks re-encryption
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

universe u v

namespace TTransform

/-- The full oracle world for the T-transform: unrestricted public randomness plus a random oracle
mapping plaintexts to encryption coins. -/
abbrev oracleSpec (M R : Type) :=
  unifSpec + (M →ₒ R)

/-- Cache state for the T-transform's lazy coins oracle. -/
abbrev QueryCache (M R : Type) :=
  (M →ₒ R).QueryCache

/-- Query implementation for the T-transform hash oracle. -/
def queryImpl {M R : Type} [DecidableEq M] [SampleableType R] :
    QueryImpl (M →ₒ R) (StateT (QueryCache M R) ProbComp) :=
  randomOracle

end TTransform

open TTransform

variable {M PK SK R C : Type}

/-- Decryption for the T transform: decrypt deterministically, then re-query the coins oracle and
check that re-encryption reproduces the ciphertext. -/
def TTransform.decrypt (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    [DecidableEq C] (pk : PK) (sk : SK) (c : C) :
    OracleComp (TTransform.oracleSpec M R) (Option M) := do
  match pke.decrypt sk c with
  | none => return none
  | some msg =>
      let r ← query (spec := TTransform.oracleSpec M R) (Sum.inr msg)
      return if pke.encrypt pk msg r = c then some msg else none

/-- The HHK17 T transform, realized as a monadic `AsymmEncAlg` in the random-oracle world
`unifSpec + (M →ₒ R)`. -/
def TTransform (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    [DecidableEq M] [DecidableEq C] [SampleableType R] :
    AsymmEncAlg (OracleComp (TTransform.oracleSpec M R)) M PK (PK × SK) C where
  keygen := do
    let (pk, sk) ← (monadLift pke.keygen : OracleComp (TTransform.oracleSpec M R) (PK × SK))
    return (pk, (pk, sk))
  encrypt := fun pk msg => do
    let r ← query (spec := TTransform.oracleSpec M R) (Sum.inr msg)
    return pke.encrypt pk msg r
  decrypt := fun (pk, sk) c => TTransform.decrypt pke pk sk c
  exec := fun comp =>
    let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (QueryCache M R) ProbComp)
    StateT.run' (simulateQ (idImpl + TTransform.queryImpl (M := M) (R := R)) comp) ∅
  lift_probComp := monadLift
  exec_lift_probComp := by
    intro α c
    simpa using
      (exec_lift_probComp_withHashOracle
        (hashImpl := TTransform.queryImpl (M := M) (R := R))
        (s := (∅ : QueryCache M R))
        c)

namespace TTransform

/-- Structural query bound for T-transform OW-PCVA adversaries: uniform-sampling queries are
unrestricted, while `qH`, `qP`, and `qV` bound the hash, plaintext-checking, and validity
oracles respectively. -/
def OW_PCVA_Adversary.MakesAtMostQueries
    {M PK SK R C : Type} [DecidableEq M] [DecidableEq C] [SampleableType R]
    {pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C}
    (adversary : OW_PCVA_Adversary (TTransform pke)) (qH qP qV : ℕ) : Prop :=
  ∀ pk cStar, OracleComp.IsQueryBound (adversary pk cStar) (qH, qP, qV)
    (fun t b => match t, b with
      | .inl (.inl _), _ => True
      | .inl (.inr _), (qH', _, _) => 0 < qH'
      | .inr (.inl _), (_, qP', _) => 0 < qP'
      | .inr (.inr _), (_, _, qV') => 0 < qV')
    (fun t b => match t, b with
      | .inl (.inl _), b' => b'
      | .inl (.inr _), (qH', qP', qV') => (qH' - 1, qP', qV')
      | .inr (.inl _), (qH', qP', qV') => (qH', qP' - 1, qV')
      | .inr (.inr _), (qH', qP', qV') => (qH', qP', qV' - 1))

/-- The T-transform security statement. The exact reduction is still deferred, but the oracle
surface and query-budget parameters now match the HHK-style OW-PCVA game. -/
theorem OW_PCVA_bound
    {M PK SK R C : Type}
    [DecidableEq M] [DecidableEq C] [SampleableType M] [SampleableType R]
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (adversary : OW_PCVA_Adversary (TTransform pke))
    (correctnessBound gamma epsMsg : ℝ)
    (qH qP qV : ℕ) :
    adversary.MakesAtMostQueries qH qP qV →
    ∃ cpaAdv₁ cpaAdv₂ : pke.toAsymmEncAlg.IND_CPA_adversary,
      (OW_PCVA_Advantage (encAlg := TTransform pke) adversary).toReal ≤
        2 * (pke.toAsymmEncAlg.IND_CPA_advantage cpaAdv₁).toReal +
        2 * (pke.toAsymmEncAlg.IND_CPA_advantage cpaAdv₂).toReal +
        correctnessBound +
        (qV : ℝ) * gamma +
        2 * ((qH + qP + 1 : ℕ) : ℝ) * epsMsg := by
  sorry

end TTransform
