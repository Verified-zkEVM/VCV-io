/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FujisakiOkamoto.TTransform
import VCVio.CryptoFoundations.KeyEncapMech
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.Coercions.Add

/-!
# Fujisaki-Okamoto U Transform

This file defines the U-transform family on top of the T-transform oracle world.
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

namespace FujisakiOkamoto

/-- A reusable FO hash world packages the public hash-oracle interface together with the
variant-specific ways of deriving encryption coins and shared keys. -/
structure Variant (M PK C R K : Type) where
  ι : Type
  hashOracleSpec : OracleSpec ι
  QueryCache : Type
  initCache : QueryCache
  queryImpl : QueryImpl hashOracleSpec (StateT QueryCache ProbComp)
  deriveCoins : PK → M → OracleComp (unifSpec + hashOracleSpec) R
  deriveKey : PK → M → C → OracleComp (unifSpec + hashOracleSpec) K

/-- Rejection behavior is factored out from the FO hash world so explicit and implicit rejection
share the same core construction. -/
structure RejectionPolicy (K C : Type) where
  FallbackState : Type
  keygen : ProbComp FallbackState
  onReject : FallbackState → C → Option K

/-- Explicit rejection returns `none` and carries no extra secret state. -/
def explicitRejection {K C : Type} : RejectionPolicy K C where
  FallbackState := PUnit
  keygen := pure PUnit.unit
  onReject := fun _ _ => none

/-- Implicit rejection stores a PRF key and derives a fallback shared key from the ciphertext. -/
def implicitRejection {K C KPRF : Type} (prf : PRFScheme KPRF C K) : RejectionPolicy K C where
  FallbackState := KPRF
  keygen := prf.keygen
  onReject := fun kPrf c => some (prf.eval kPrf c)

/-- Execute an FO computation by combining public randomness with the variant-specific hash world. -/
def exec {M PK C R K : Type} (variant : Variant M PK C R K)
    {α : Type} (comp : OracleComp (unifSpec + variant.hashOracleSpec) α) : ProbComp α :=
  let idImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT variant.QueryCache ProbComp)
  StateT.run' (simulateQ (idImpl + variant.queryImpl) comp) variant.initCache

/-- Lifted probabilistic computations ignore the FO hash world. -/
theorem exec_lift_probComp {M PK C R K : Type} (variant : Variant M PK C R K)
    {α : Type} (c : ProbComp α) :
    FujisakiOkamoto.exec variant (monadLift c) = c := by
  simpa [exec] using
    (exec_lift_probComp_withHashOracle
      (hashImpl := variant.queryImpl)
      (s := variant.initCache)
      c)

/-- Generic FO construction parameterized by a hash world and a rejection policy. -/
def scheme
    {M PK SK R C K : Type}
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (variant : Variant M PK C R K)
    (policy : RejectionPolicy K C)
    [SampleableType M] [DecidableEq C] :
    KEMScheme (OracleComp (unifSpec + variant.hashOracleSpec))
      K PK ((PK × SK) × policy.FallbackState) C where
  keygen := do
    let (pk, sk) ← (monadLift pke.keygen :
      OracleComp (unifSpec + variant.hashOracleSpec) (PK × SK))
    let fb ← (monadLift policy.keygen :
      OracleComp (unifSpec + variant.hashOracleSpec) policy.FallbackState)
    return (pk, ((pk, sk), fb))
  encaps := fun pk => do
    let msg ← (monadLift ($ᵗ M : ProbComp M) :
      OracleComp (unifSpec + variant.hashOracleSpec) M)
    let r ← variant.deriveCoins pk msg
    let c := pke.encrypt pk msg r
    let k ← variant.deriveKey pk msg c
    return (c, k)
  decaps := fun ((pk, sk), fb) c => do
    match pke.decrypt sk c with
    | none => return policy.onReject fb c
    | some msg =>
        let r ← variant.deriveCoins pk msg
        if pke.encrypt pk msg r = c then
          let k ← variant.deriveKey pk msg c
          return some k
        else
          return policy.onReject fb c
  exec := FujisakiOkamoto.exec variant
  lift_probComp := monadLift
  exec_lift_probComp := by
    intro α c
    simpa using FujisakiOkamoto.exec_lift_probComp (variant := variant) (c := c)

end FujisakiOkamoto

namespace UTransform

/-- The public hash-oracle interface for the two-RO U-transform: one oracle derives encryption
coins from plaintexts and the other derives shared keys from the chosen derivation input. -/
abbrev hashOracleSpec (M R KD K : Type) :=
  (M →ₒ R) + (KD →ₒ K)

/-- The full oracle world for the U-transform, consisting of unrestricted public randomness plus
the two public hash oracles. -/
abbrev oracleSpec (M R KD K : Type) :=
  unifSpec + hashOracleSpec M R KD K

/-- Cache state for the U-transform's two lazy random oracles. -/
abbrev QueryCache (M R KD K : Type) :=
  (M →ₒ R).QueryCache × (KD →ₒ K).QueryCache

/-- Lazy random oracle for encryption coins, threaded through the combined U-transform state. -/
def coinOracleImpl {M R KD K : Type} [DecidableEq M] [SampleableType R] :
    QueryImpl (M →ₒ R) (StateT (QueryCache M R KD K) ProbComp) := fun msg => do
  let st ← get
  match st.1 msg with
  | some r => return r
  | none =>
      let r ← liftM ($ᵗ R : ProbComp R)
      set (st.1.cacheQuery msg r, st.2)
      return r

/-- Lazy random oracle for key derivation, threaded through the combined U-transform state. -/
def keyOracleImpl {M R KD K : Type} [DecidableEq KD] [SampleableType K] :
    QueryImpl (KD →ₒ K) (StateT (QueryCache M R KD K) ProbComp) := fun kd => do
  let st ← get
  match st.2 kd with
  | some k => return k
  | none =>
      let k ← liftM ($ᵗ K : ProbComp K)
      set (st.1, st.2.cacheQuery kd k)
      return k

/-- Query implementation for the full two-RO FO hash world. -/
def queryImpl {M R KD K : Type}
    [DecidableEq M] [DecidableEq KD] [SampleableType R] [SampleableType K] :
    QueryImpl (hashOracleSpec M R KD K) (StateT (QueryCache M R KD K) ProbComp) :=
  coinOracleImpl (M := M) (R := R) (KD := KD) (K := K) +
    keyOracleImpl (M := M) (R := R) (KD := KD) (K := K)

/-- Two-RO FO hash world: one oracle derives coins from the message, the other derives the shared
key from a variant-chosen encoding of `(m, c)`. -/
def variant
    {M PK C R KD K : Type}
    (kdInput : M → C → KD)
    [DecidableEq M] [DecidableEq KD] [SampleableType R] [SampleableType K] :
    FujisakiOkamoto.Variant M PK C R K where
  ι := _
  hashOracleSpec := hashOracleSpec M R KD K
  QueryCache := QueryCache M R KD K
  initCache := (∅, ∅)
  queryImpl := queryImpl (M := M) (R := R) (KD := KD) (K := K)
  deriveCoins := fun _pk msg =>
    query (spec := oracleSpec M R KD K) (Sum.inr (Sum.inl msg))
  deriveKey := fun _pk msg c =>
    query (spec := oracleSpec M R KD K) (Sum.inr (Sum.inr (kdInput msg c)))

end UTransform

open UTransform

variable {M PK SK R C KD K KPRF : Type}

/-- The generic two-RO U-transform family. The argument `kdInput` chooses whether the shared key
is derived from `m`, `(m, c)`, or some other encoding of the recovered plaintext and ciphertext. -/
def UTransform
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    [DecidableEq M] [DecidableEq C] [DecidableEq KD]
    [SampleableType M] [SampleableType R] [SampleableType K] :
    KEMScheme (OracleComp (UTransform.oracleSpec M R KD K))
      K PK ((PK × SK) × policy.FallbackState) C :=
  FujisakiOkamoto.scheme pke
    (UTransform.variant (PK := PK) (kdInput := kdInput) (M := M) (C := C) (R := R) (KD := KD)
      (K := K))
    policy

namespace UTransform

/-- The generic U-transform CCA bound. The proof is intentionally deferred, but the reduction
artifacts are now existentially quantified rather than passed in as unrelated inputs. -/
theorem IND_CCA_bound
    {M PK SK R C KD K KPRF : Type}
    [DecidableEq M] [DecidableEq C] [DecidableEq KD]
    [SampleableType M] [SampleableType R] [SampleableType K]
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (prf : PRFScheme KPRF C K)
    (kdInput : M → C → KD)
    (adversary : (UTransform pke kdInput (FujisakiOkamoto.implicitRejection prf)).IND_CCA_Adversary)
    (correctnessBound₁ correctnessBound₂ : ℝ) :
    ∃ prfAdv : PRFScheme.PRFAdversary C K,
      ∃ owAdv : OW_PCVA_Adversary (TTransform pke),
        (UTransform pke kdInput (FujisakiOkamoto.implicitRejection prf)).IND_CCA_Advantage
            adversary ≤
          PRFScheme.prfAdvantage prf prfAdv +
          correctnessBound₁ +
          correctnessBound₂ +
          (OW_PCVA_Advantage (encAlg := TTransform pke) owAdv).toReal := by
  sorry

end UTransform
