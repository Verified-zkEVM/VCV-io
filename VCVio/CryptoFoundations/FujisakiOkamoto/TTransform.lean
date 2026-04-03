/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.FujisakiOkamoto.Defs
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.QueryTracking.QueryRuntime
import VCVio.OracleComp.QueryTracking.RandomOracle
import VCVio.OracleComp.SimSemantics.BundledSemantics

/-!
# Fujisaki-Okamoto T Transform

This file defines the derandomizing T transform:

- coins are derived from a random oracle on the plaintext
- decryption re-derives the coins and checks re-encryption
-/


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
def TTransform.decrypt {m : Type → Type v} [Monad m]
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    [DecidableEq C] [HasQuery (M →ₒ R) m] (pk : PK) (sk : SK) (c : C) :
    m (Option M) := do
  match pke.decrypt sk c with
  | none => return none
  | some msg =>
      let r ← HasQuery.query (spec := (M →ₒ R)) msg
      return if pke.encrypt pk msg r = c then some msg else none

/-- The HHK17 T transform, realized as a monadic `AsymmEncAlg` in the random-oracle world
`unifSpec + (M →ₒ R)`. -/
def TTransform {m : Type → Type v} [Monad m]
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    [DecidableEq M] [DecidableEq C] [SampleableType R]
    [MonadLiftT ProbComp m] [HasQuery (M →ₒ R) m] :
    AsymmEncAlg m M PK (PK × SK) C where
  keygen := do
    let (pk, sk) ← (monadLift pke.keygen : m (PK × SK))
    return (pk, (pk, sk))
  encrypt := fun pk msg => do
    let r ← HasQuery.query (spec := (M →ₒ R)) msg
    return pke.encrypt pk msg r
  decrypt := fun (pk, sk) c => TTransform.decrypt (m := m) pke pk sk c

section naturality

variable {m : Type → Type u} [Monad m]
  {n : Type → Type v} [Monad n]
  [MonadLiftT ProbComp m] [MonadLiftT ProbComp n]
  [HasQuery (M →ₒ R) m] [HasQuery (M →ₒ R) n]

/-- The T-transform is natural in any oracle-semantics morphism that preserves both the
plaintext-to-coins query capability and the distinguished lift of `ProbComp`. -/
theorem map_construction
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    [DecidableEq M] [DecidableEq C] [SampleableType R]
    (F : HasQuery.QueryHom (M →ₒ R) m n)
    (hLift : HasQuery.PreservesProbCompLift (m := m) (n := n) F.toMonadHom) :
    (TTransform (m := m) pke).map F.toMonadHom =
      TTransform (m := n) pke := by
  cases pke with
  | mk keygen encrypt decrypt =>
      apply AsymmEncAlg.ext
      · simp only [AsymmEncAlg.map, TTransform, MonadHom.mmap_bind, MonadHom.mmap_pure,
          hLift keygen]
      · funext pk msg
        simp only [AsymmEncAlg.map, TTransform, MonadHom.mmap_bind, MonadHom.mmap_pure,
          HasQuery.map_query]
      · funext x c
        cases hdec : decrypt x.2 c with
        | none =>
            simp only [AsymmEncAlg.map, TTransform, TTransform.decrypt, MonadHom.mmap_bind,
              MonadHom.mmap_pure, hdec]
        | some msg =>
            simp only [AsymmEncAlg.map, TTransform, TTransform.decrypt, MonadHom.mmap_bind,
              MonadHom.mmap_pure, HasQuery.map_query, hdec]

end naturality

section costAccounting

variable {m : Type → Type u} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]

/-- Output projection of unit-cost-instrumented T-transform encryption. -/
theorem fst_map_encrypt_run_withAddCost
    (runtime : QueryRuntime (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    [DecidableEq M] [DecidableEq C] [SampleableType R]
    (pk : PK) (msg : M) :
    letI : HasQuery (M →ₒ R) m := runtime.toHasQuery
    letI : HasQuery (M →ₒ R) (AddWriterT ℕ m) :=
      (runtime.withAddCost fun _ ↦ 1).toHasQuery
    Prod.fst <$> ((TTransform (m := AddWriterT ℕ m) pke).encrypt pk msg).run =
      (TTransform (m := m) pke).encrypt pk msg := by
  simp [TTransform, QueryRuntime.withAddCost_impl, AddWriterT.addTell]

/-- Cost projection of unit-cost-instrumented T-transform encryption. -/
theorem snd_map_encrypt_run_withAddCost
    (runtime : QueryRuntime (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    [DecidableEq M] [DecidableEq C] [SampleableType R]
    (pk : PK) (msg : M) :
    letI : HasQuery (M →ₒ R) m := runtime.toHasQuery
    letI : HasQuery (M →ₒ R) (AddWriterT ℕ m) :=
      (runtime.withAddCost fun _ ↦ 1).toHasQuery
    Prod.snd <$> ((TTransform (m := AddWriterT ℕ m) pke).encrypt pk msg).run =
      (fun _ ↦ Multiplicative.ofAdd 1) <$> (TTransform (m := m) pke).encrypt pk msg := by
  simp [TTransform, QueryRuntime.withAddCost_impl, AddWriterT.addTell]

/-- Output projection of unit-cost-instrumented T-transform decryption. -/
theorem fst_map_decrypt_run_withAddCost
    (runtime : QueryRuntime (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    [DecidableEq M] [DecidableEq C] [SampleableType R]
    (pk : PK) (sk : SK) (c : C) :
    letI : HasQuery (M →ₒ R) m := runtime.toHasQuery
    letI : HasQuery (M →ₒ R) (AddWriterT ℕ m) :=
      (runtime.withAddCost fun _ ↦ 1).toHasQuery
    Prod.fst <$> ((TTransform (m := AddWriterT ℕ m) pke).decrypt (pk, sk) c).run =
      (TTransform (m := m) pke).decrypt (pk, sk) c := by
  cases hdec : pke.decrypt sk c with
  | none =>
      simp [TTransform, TTransform.decrypt, hdec]
  | some msg =>
      simp [TTransform, TTransform.decrypt, hdec, QueryRuntime.withAddCost_impl, AddWriterT.addTell]

/-- Cost projection of unit-cost-instrumented T-transform decryption. The transform incurs no
oracle cost if deterministic decryption fails immediately, and exactly one query otherwise. -/
theorem snd_map_decrypt_run_withAddCost
    (runtime : QueryRuntime (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    [DecidableEq M] [DecidableEq C] [SampleableType R]
    (pk : PK) (sk : SK) (c : C) :
    letI : HasQuery (M →ₒ R) m := runtime.toHasQuery
    letI : HasQuery (M →ₒ R) (AddWriterT ℕ m) :=
      (runtime.withAddCost fun _ ↦ 1).toHasQuery
    Prod.snd <$> ((TTransform (m := AddWriterT ℕ m) pke).decrypt (pk, sk) c).run =
      match pke.decrypt sk c with
      | none => pure (Multiplicative.ofAdd 0)
      | some _ => (fun _ ↦ Multiplicative.ofAdd 1) <$>
          (TTransform (m := m) pke).decrypt (pk, sk) c := by
  cases hdec : pke.decrypt sk c with
  | none =>
      simp [TTransform, TTransform.decrypt, hdec]
  | some msg =>
      simp [TTransform, TTransform.decrypt, hdec, QueryRuntime.withAddCost_impl, AddWriterT.addTell]

end costAccounting

namespace TTransform

/-- Runtime bundle for the T-transform random-oracle world. -/
noncomputable def runtime
    [DecidableEq M] [SampleableType R] :
    ProbCompRuntime (OracleComp (TTransform.oracleSpec M R)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := TTransform.queryImpl (M := M) (R := R))
    (∅ : QueryCache M R)
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- Structural query bound for T-transform OW-PCVA adversaries: uniform-sampling queries are
unrestricted, while `qH`, `qP`, and `qV` bound the hash, plaintext-checking, and validity
oracles respectively. -/
def OW_PCVA_Adversary.MakesAtMostQueries
    {M PK SK R C : Type} [DecidableEq M] [DecidableEq C] [SampleableType R]
    {pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C}
    (adversary : OW_PCVA_Adversary
      (TTransform (m := OracleComp (TTransform.oracleSpec M R)) pke)) (qH qP qV : ℕ) : Prop :=
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
    (adversary : OW_PCVA_Adversary
      (TTransform (m := OracleComp (TTransform.oracleSpec M R)) pke))
    (correctnessBound gamma epsMsg : ℝ)
    (qH qP qV : ℕ) :
    adversary.MakesAtMostQueries qH qP qV →
    ∃ cpaAdv₁ cpaAdv₂ : (pke.toAsymmEncAlg ProbCompRuntime.probComp).IND_CPA_adversary,
      (OW_PCVA_Advantage
        (encAlg := TTransform (m := OracleComp (TTransform.oracleSpec M R)) pke)
        (runtime (M := M) (R := R)) adversary).toReal ≤
        2 * ((pke.toAsymmEncAlg ProbCompRuntime.probComp).IND_CPA_advantage cpaAdv₁).toReal +
        2 * ((pke.toAsymmEncAlg ProbCompRuntime.probComp).IND_CPA_advantage cpaAdv₂).toReal +
        correctnessBound +
        (qV : ℝ) * gamma +
        2 * ((qH + qP + 1 : ℕ) : ℝ) * epsMsg := by
  sorry

end TTransform
