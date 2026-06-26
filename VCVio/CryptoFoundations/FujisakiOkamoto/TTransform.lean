/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA.Oracle
import VCVio.CryptoFoundations.FujisakiOkamoto.Defs
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.HasQuery.Morphism
import VCVio.OracleComp.QueryTracking.QueryCost
import VCVio.OracleComp.QueryTracking.RandomOracle.Basic
import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics

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
  encrypt pk msg := do
    let r ← HasQuery.query (spec := (M →ₒ R)) msg
    return pke.encrypt pk msg r
  decrypt | (pk, sk), c => TTransform.decrypt pke pk sk c

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
      · simp [AsymmEncAlg.map, TTransform, hLift keygen]
      · funext pk msg
        simp [AsymmEncAlg.map, TTransform]
      · funext x c
        cases hdec : decrypt x.2 c <;>
          simp [AsymmEncAlg.map, TTransform, TTransform.decrypt, hdec]

end naturality

section costAccounting

variable [DecidableEq C]

variable {m : Type → Type u} [Monad m] [LawfulMonad m]
  [MonadLiftT ProbComp m]

/-- T-transform encryption incurs exactly the weighted cost assigned to the single coins-oracle
query on `msg`. -/
theorem encrypt_usesExactQueryCost {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (msg : M) (costFn : M → ω) :
    QueryCost[ (TTransform pke).encrypt pk msg in runtime by costFn ] = costFn msg := by
  simp [HasQuery.UsesCostExactly, HasQuery.Program.withAddCost, TTransform]

/-- T-transform encryption has expected weighted query cost equal to the weight of querying
`msg`. -/
theorem encrypt_expectedQueryCost_eq {ω : Type} [AddMonoid ω] [Preorder ω]
    [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (runtime : QueryImpl (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (msg : M) (costFn : M → ω) (val : ω → ENNReal) (hval : Monotone val) :
    ExpectedQueryCost[
      (TTransform pke).encrypt pk msg in runtime by costFn via val
    ] = val (costFn msg) :=
  HasQuery.expectedQueryCost_eq_of_usesCostExactly
    (encrypt_usesExactQueryCost runtime pke pk msg costFn) hval

/-- T-transform encryption makes exactly one hash-oracle query under unit-cost instrumentation. -/
theorem encrypt_usesExactlyOneQuery
    (runtime : QueryImpl (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (msg : M) :
    Queries[ (TTransform pke).encrypt pk msg in runtime ] = 1 := by
  simpa [HasQuery.UsesExactlyQueries] using
    encrypt_usesExactQueryCost (ω := ℕ) runtime pke pk msg fun _ => 1

/-- If deterministic decryption fails immediately, the T-transform incurs zero weighted
query cost. -/
theorem decrypt_usesZeroQueryCost_of_decrypt_eq_none {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (sk : SK) (c : C) (costFn : M → ω)
    (hdec : pke.decrypt sk c = none) :
    QueryCost[ (TTransform pke).decrypt (pk, sk) c in runtime by costFn ] = 0 := by
  simp [HasQuery.UsesCostExactly, HasQuery.Program.withAddCost, TTransform,
    TTransform.decrypt, hdec]

/-- If deterministic decryption fails immediately, the T-transform has expected weighted query
cost `0`. -/
theorem decrypt_expectedQueryCost_eq_zero_of_decrypt_eq_none {ω : Type}
    [AddMonoid ω] [Preorder ω] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (runtime : QueryImpl (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (sk : SK) (c : C) (costFn : M → ω)
    (val : ω → ENNReal) (hval : Monotone val)
    (hdec : pke.decrypt sk c = none) :
    ExpectedQueryCost[
      (TTransform pke).decrypt (pk, sk) c in runtime by costFn via val
    ] = val 0 :=
  HasQuery.expectedQueryCost_eq_of_usesCostExactly
    (decrypt_usesZeroQueryCost_of_decrypt_eq_none runtime pke pk sk c costFn hdec) hval

/-- If deterministic decryption returns a message, the T-transform incurs exactly the weighted
cost of querying that message to re-derive the coins. -/
theorem decrypt_usesExactQueryCost_of_decrypt_eq_some {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (sk : SK) (c : C) (costFn : M → ω) {msg : M}
    (hdec : pke.decrypt sk c = some msg) :
    QueryCost[ (TTransform pke).decrypt (pk, sk) c in runtime by costFn ] = costFn msg := by
  simp [HasQuery.UsesCostExactly, HasQuery.Program.withAddCost, TTransform,
    TTransform.decrypt, hdec]

/-- If deterministic decryption returns a message, the T-transform has expected weighted query
cost equal to the weight of querying that message. -/
theorem decrypt_expectedQueryCost_eq_of_decrypt_eq_some {ω : Type}
    [AddMonoid ω] [Preorder ω] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (runtime : QueryImpl (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (sk : SK) (c : C) (costFn : M → ω)
    (val : ω → ENNReal) (hval : Monotone val) {msg : M}
    (hdec : pke.decrypt sk c = some msg) :
    ExpectedQueryCost[
      (TTransform pke).decrypt (pk, sk) c in runtime by costFn via val
    ] = val (costFn msg) :=
  HasQuery.expectedQueryCost_eq_of_usesCostExactly
    (decrypt_usesExactQueryCost_of_decrypt_eq_some runtime pke pk sk c costFn hdec) hval

/-- If deterministic decryption fails immediately, the T-transform makes no hash-oracle
queries. -/
theorem decrypt_usesNoQueries_of_decrypt_eq_none
    (runtime : QueryImpl (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (sk : SK) (c : C)
    (hdec : pke.decrypt sk c = none) :
    Queries[ (TTransform pke).decrypt (pk, sk) c in runtime ] = 0 := by
  simpa [HasQuery.UsesExactlyQueries] using
    decrypt_usesZeroQueryCost_of_decrypt_eq_none (ω := ℕ) runtime pke pk sk c (fun _ => 1) hdec

/-- If deterministic decryption returns a message, the T-transform makes exactly one
hash-oracle query to re-derive the coins. -/
theorem decrypt_usesExactlyOneQuery_of_decrypt_eq_some
    (runtime : QueryImpl (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (sk : SK) (c : C) {msg : M}
    (hdec : pke.decrypt sk c = some msg) :
    Queries[ (TTransform pke).decrypt (pk, sk) c in runtime ] = 1 := by
  simpa [HasQuery.UsesExactlyQueries] using
    decrypt_usesExactQueryCost_of_decrypt_eq_some (ω := ℕ) runtime pke pk sk c (fun _ => 1) hdec

/-- T-transform decryption makes at most one hash-oracle query under unit-cost instrumentation. -/
theorem decrypt_usesAtMostOneQuery [MonadLiftT m SetM] [LawfulMonadLiftT m SetM]
    (runtime : QueryImpl (M →ₒ R) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (pk : PK) (sk : SK) (c : C) :
    Queries[ (TTransform pke).decrypt (pk, sk) c in runtime ] ≤ 1 := by
  cases hdec : pke.decrypt sk c with
  | none =>
      exact HasQuery.usesAtMostQueries_of_usesExactlyQueries
        (decrypt_usesNoQueries_of_decrypt_eq_none runtime pke pk sk c hdec) (Nat.zero_le 1)
  | some msg =>
      exact HasQuery.usesAtMostQueries_of_usesExactlyQueries
        (decrypt_usesExactlyOneQuery_of_decrypt_eq_some runtime pke pk sk c hdec) le_rfl

end costAccounting

namespace TTransform

/-- Runtime bundle for the T-transform random-oracle world. -/
noncomputable def runtime
    [DecidableEq M] [SampleableType R] :
    ProbCompRuntime (OracleComp (TTransform.oracleSpec M R)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle TTransform.queryImpl ∅
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- Structural query bound for T-transform OW-PCVA adversaries: uniform-sampling queries are
unrestricted, while `qH`, `qP`, and `qV` bound the hash, plaintext-checking, and validity
oracles respectively.

Defined as the conjunction of three predicate-targeted query bounds `IsQueryBoundP`, one per
counted oracle. Because the three index predicates are pairwise disjoint, this conjunction is
equivalent to a single-vector `IsQueryBound` over the combined per-oracle budget. -/
def OW_PCVA_Adversary.MakesAtMostQueries
    {M PK SK R C : Type} [DecidableEq M] [DecidableEq C] [SampleableType R]
    {pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C}
    (adversary : OW_PCVA_Adversary
      (TTransform (m := OracleComp (TTransform.oracleSpec M R)) pke)) (qH qP qV : ℕ) : Prop :=
  ∀ pk cStar,
    (adversary pk cStar).IsQueryBoundP (· matches .inl (.inr _)) qH ∧
    (adversary pk cStar).IsQueryBoundP (· matches .inr (.inl _)) qP ∧
    (adversary pk cStar).IsQueryBoundP (· matches .inr (.inr _)) qV

/-- The T-transform OW-PCVA security statement.

**WARNING: this is a placeholder statement, not the final theorem.** The current shape is
unsound as written: `correctnessBound`, `gamma`, and `epsMsg` are unconstrained `ℝ`
parameters, so the right-hand side can be driven arbitrarily negative while the left-hand
side is a probability and hence nonnegative. In the final HHK-style statement these slack
terms must be constrained (typically `correctnessBound` is the underlying PKE's
`δ`-correctness error, `gamma` is the `γ`-spreadness bound on ciphertexts, and `epsMsg` is
the message-distribution collision/min-entropy term, all of which are provably nonnegative
quantities derived from `pke`).

The proof is intentionally deferred. The oracle surface and query-budget parameters
(`qH`, `qP`, `qV`) now match the HHK OW-PCVA game, but the bound itself still needs to be
tightened before this can be a meaningful security claim. -/
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
