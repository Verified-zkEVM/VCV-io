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
    [DecidableEq C]
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

variable [DecidableEq C]

variable {m : Type → Type u} [Monad m]
  {n : Type → Type v} [Monad n]
  [MonadLiftT ProbComp m] [MonadLiftT ProbComp n]
  [HasQuery (M →ₒ R) m] [HasQuery (M →ₒ R) n]

/-- The T-transform is natural in any oracle-semantics morphism that preserves both the
plaintext-to-coins query capability and the distinguished lift of `ProbComp`. -/
theorem map_construction
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
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

variable [DecidableEq C]

variable {m : Type → Type u} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]

/-- Running unit-cost-instrumented T-transform encryption preserves the ciphertext output. -/
private lemma encrypt_outputs_formula_withUnitCost
    (runtime : QueryRuntime (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (msg : M) :
    AddWriterT.outputs
        (HasQuery.withUnitCost
          (fun [HasQuery (M →ₒ R) (AddWriterT ℕ m)] =>
            (TTransform (m := AddWriterT ℕ m) pke).encrypt pk msg)
          runtime) =
      HasQuery.inRuntime
        (fun [HasQuery (M →ₒ R) m] =>
          (TTransform (m := m) pke).encrypt pk msg)
        runtime := by
  simp [HasQuery.inRuntime, HasQuery.withUnitCost, AddWriterT.outputs, TTransform,
    QueryRuntime.withUnitCost_impl, AddWriterT.addTell]

private lemma encrypt_costs_formula_withUnitCost
    (runtime : QueryRuntime (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (msg : M) :
    AddWriterT.costs
        (HasQuery.withUnitCost
          (fun [HasQuery (M →ₒ R) (AddWriterT ℕ m)] =>
            (TTransform (m := AddWriterT ℕ m) pke).encrypt pk msg)
          runtime) =
      (fun _ ↦ 1) <$>
        HasQuery.inRuntime
          (fun [HasQuery (M →ₒ R) m] =>
            (TTransform (m := m) pke).encrypt pk msg)
          runtime := by
  simp [HasQuery.inRuntime, HasQuery.withUnitCost, AddWriterT.costs, TTransform,
    QueryRuntime.withUnitCost_impl, AddWriterT.addTell]

/-- T-transform encryption makes exactly one hash-oracle query under unit-cost instrumentation. -/
theorem encrypt_usesExactlyOneQuery
    (runtime : QueryRuntime (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (msg : M) :
    Queries[ (TTransform pke).encrypt pk msg in runtime ] = 1 := by
  change Cost[
    HasQuery.withUnitCost
      (fun [HasQuery (M →ₒ R) (AddWriterT ℕ m)] =>
        (TTransform (m := AddWriterT ℕ m) pke).encrypt pk msg)
      runtime
  ] = 1
  rw [AddWriterT.hasCost_iff]
  rw [encrypt_outputs_formula_withUnitCost
    (runtime := runtime) (pke := pke) (pk := pk) (msg := msg)]
  exact encrypt_costs_formula_withUnitCost
    (runtime := runtime) (pke := pke) (pk := pk) (msg := msg)

/-- Running unit-cost-instrumented T-transform decryption preserves the decryption result. -/
private lemma decrypt_outputs_formula_withUnitCost
    (runtime : QueryRuntime (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (sk : SK) (c : C) :
    AddWriterT.outputs
        (HasQuery.withUnitCost
          (fun [HasQuery (M →ₒ R) (AddWriterT ℕ m)] =>
            (TTransform (m := AddWriterT ℕ m) pke).decrypt (pk, sk) c)
          runtime) =
      HasQuery.inRuntime
        (fun [HasQuery (M →ₒ R) m] =>
          (TTransform (m := m) pke).decrypt (pk, sk) c)
        runtime := by
  cases hdec : pke.decrypt sk c with
  | none =>
      simp [HasQuery.inRuntime, HasQuery.withUnitCost, AddWriterT.outputs, TTransform,
        TTransform.decrypt, hdec]
  | some msg =>
      simp [HasQuery.inRuntime, HasQuery.withUnitCost, AddWriterT.outputs, TTransform,
        TTransform.decrypt, hdec,
        QueryRuntime.withUnitCost_impl, AddWriterT.addTell]

private lemma decrypt_costs_formula_withUnitCost
    (runtime : QueryRuntime (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (sk : SK) (c : C) :
    AddWriterT.costs
        (HasQuery.withUnitCost
          (fun [HasQuery (M →ₒ R) (AddWriterT ℕ m)] =>
            (TTransform (m := AddWriterT ℕ m) pke).decrypt (pk, sk) c)
          runtime) =
      match pke.decrypt sk c with
      | none => pure 0
      | some _ => (fun _ ↦ 1) <$>
          HasQuery.inRuntime
            (fun [HasQuery (M →ₒ R) m] =>
              (TTransform (m := m) pke).decrypt (pk, sk) c)
            runtime := by
  cases hdec : pke.decrypt sk c with
  | none =>
      simp [HasQuery.withUnitCost, AddWriterT.costs, TTransform,
        TTransform.decrypt, hdec]
  | some msg =>
      simp [HasQuery.inRuntime, HasQuery.withUnitCost, AddWriterT.costs, TTransform,
        TTransform.decrypt, hdec,
        QueryRuntime.withUnitCost_impl, AddWriterT.addTell]

/-- If deterministic decryption fails immediately, the T-transform makes no hash-oracle
queries. -/
theorem decrypt_usesNoQueries_of_decrypt_eq_none
    (runtime : QueryRuntime (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (sk : SK) (c : C)
    (hdec : pke.decrypt sk c = none) :
    Queries[ (TTransform pke).decrypt (pk, sk) c in runtime ] = 0 := by
  change AddWriterT.costs
      (HasQuery.withUnitCost
        (fun [HasQuery (M →ₒ R) (AddWriterT ℕ m)] =>
          (TTransform (m := AddWriterT ℕ m) pke).decrypt (pk, sk) c)
        runtime) =
    (fun _ ↦ 0) <$>
      AddWriterT.outputs
        (HasQuery.withUnitCost
          (fun [HasQuery (M →ₒ R) (AddWriterT ℕ m)] =>
            (TTransform (m := AddWriterT ℕ m) pke).decrypt (pk, sk) c)
          runtime)
  have h_outputs := decrypt_outputs_formula_withUnitCost
    (runtime := runtime) (pke := pke) (pk := pk) (sk := sk) (c := c)
  have h_decrypt :
      HasQuery.inRuntime
        (fun [HasQuery (M →ₒ R) m] =>
          (TTransform (m := m) pke).decrypt (pk, sk) c)
        runtime = pure none := by
    simp [HasQuery.inRuntime, TTransform, TTransform.decrypt, hdec]
  rw [h_outputs, h_decrypt]
  simpa [hdec] using decrypt_costs_formula_withUnitCost
    (runtime := runtime) (pke := pke) (pk := pk) (sk := sk) (c := c)

/-- If deterministic decryption returns a message, the T-transform makes exactly one
hash-oracle query to re-derive the coins. -/
theorem decrypt_usesExactlyOneQuery_of_decrypt_eq_some
    (runtime : QueryRuntime (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (sk : SK) (c : C) {msg : M}
    (hdec : pke.decrypt sk c = some msg) :
    Queries[ (TTransform pke).decrypt (pk, sk) c in runtime ] = 1 := by
  change AddWriterT.costs
      (HasQuery.withUnitCost
        (fun [HasQuery (M →ₒ R) (AddWriterT ℕ m)] =>
          (TTransform (m := AddWriterT ℕ m) pke).decrypt (pk, sk) c)
        runtime) =
    (fun _ ↦ 1) <$>
      AddWriterT.outputs
        (HasQuery.withUnitCost
          (fun [HasQuery (M →ₒ R) (AddWriterT ℕ m)] =>
            (TTransform (m := AddWriterT ℕ m) pke).decrypt (pk, sk) c)
          runtime)
  have h_outputs := decrypt_outputs_formula_withUnitCost
    (runtime := runtime) (pke := pke) (pk := pk) (sk := sk) (c := c)
  rw [h_outputs]
  simpa [hdec] using decrypt_costs_formula_withUnitCost
    (runtime := runtime) (pke := pke) (pk := pk) (sk := sk) (c := c)

/-- T-transform decryption makes at most one hash-oracle query under unit-cost instrumentation. -/
theorem decrypt_usesAtMostOneQuery
    (runtime : QueryRuntime (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (sk : SK) (c : C) :
    Queries[ (TTransform pke).decrypt (pk, sk) c in runtime ] ≤ 1 := by
  by_cases hdec : pke.decrypt sk c = none
  · exact HasQuery.usesAtMostQueries_of_usesExactlyQueries
      (oa := fun [HasQuery (M →ₒ R) (AddWriterT ℕ m)] =>
        (TTransform (m := AddWriterT ℕ m) pke).decrypt (pk, sk) c)
      (runtime := runtime)
      (decrypt_usesNoQueries_of_decrypt_eq_none
        (runtime := runtime) (pke := pke) (pk := pk) (sk := sk) (c := c) hdec)
      (Nat.zero_le 1)
  · rcases Option.ne_none_iff_exists'.mp hdec with ⟨msg, hsome⟩
    exact HasQuery.usesAtMostQueries_of_usesExactlyQueries
      (oa := fun [HasQuery (M →ₒ R) (AddWriterT ℕ m)] =>
        (TTransform (m := AddWriterT ℕ m) pke).decrypt (pk, sk) c)
      (runtime := runtime)
      (decrypt_usesExactlyOneQuery_of_decrypt_eq_some
        (runtime := runtime) (pke := pke) (pk := pk) (sk := sk) (c := c) hsome)
      le_rfl

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
