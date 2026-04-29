/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/
import VCVio.CryptoFoundations.FujisakiOkamoto.TTransform
import VCVio.CryptoFoundations.KeyEncapMech
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.Coercions.Add
import VCVio.OracleComp.SimSemantics.BundledSemantics

/-!
# Fujisaki-Okamoto U Transform

This file defines the U-transform family on top of the T-transform oracle world.
-/


universe u v

open OracleComp OracleSpec ENNReal

namespace FujisakiOkamoto

/-- A reusable FO hash world packages the public hash-oracle interface together with the
variant-specific ways of deriving encryption coins and shared keys. -/
structure Variant {ι : Type} (hashOracleSpec : OracleSpec ι) (M PK C R K : Type) where
  QueryCache : Type
  initCache : QueryCache
  queryImpl : QueryImpl hashOracleSpec (StateT QueryCache ProbComp)
  deriveCoins : {m : Type → Type v} → [Monad m] → [MonadLiftT ProbComp m] →
    [HasQuery hashOracleSpec m] → PK → M → m R
  deriveKey : {m : Type → Type v} → [Monad m] → [MonadLiftT ProbComp m] →
    [HasQuery hashOracleSpec m] → PK → M → C → m K

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

/-- Bundled subprobabilistic semantics for an FO hash world, obtained by hiding the
variant-specific cache after running the public-randomness-plus-hash simulation. -/
noncomputable def spmfSemantics {ι : Type} {hashOracleSpec : OracleSpec ι}
    {M PK C R K : Type} (variant : Variant hashOracleSpec M PK C R K) :
    SPMFSemantics (OracleComp (unifSpec + hashOracleSpec)) :=
  SPMFSemantics.withStateOracle variant.queryImpl variant.initCache

/-- Full public-randomness runtime for an FO hash world. -/
noncomputable def runtime {ι : Type} {hashOracleSpec : OracleSpec ι}
    {M PK C R K : Type} (variant : Variant hashOracleSpec M PK C R K) :
    ProbCompRuntime (OracleComp (unifSpec + hashOracleSpec)) where
  toSPMFSemantics := spmfSemantics variant
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- Generic FO construction parameterized by a hash world and a rejection policy. -/
def scheme
    {ι : Type} {hashOracleSpec : OracleSpec ι} {M PK SK R C K : Type}
    {m : Type → Type v} [Monad m] [MonadLiftT ProbComp m]
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (variant : Variant hashOracleSpec M PK C R K)
    (policy : RejectionPolicy K C)
    [SampleableType M] [DecidableEq C] [HasQuery hashOracleSpec m] :
    KEMScheme m
      K PK ((PK × SK) × policy.FallbackState) C where
  keygen := do
    let (pk, sk) ← monadLift pke.keygen
    let fb ← monadLift policy.keygen
    return (pk, ((pk, sk), fb))
  encaps := fun pk => do
    let msg ← monadLift ($ᵗ M : ProbComp M)
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
      let r ← ($ᵗ R : ProbComp R)
      set (st.1.cacheQuery msg r, st.2)
      return r

/-- Lazy random oracle for key derivation, threaded through the combined U-transform state. -/
def keyOracleImpl {M R KD K : Type} [DecidableEq KD] [SampleableType K] :
    QueryImpl (KD →ₒ K) (StateT (QueryCache M R KD K) ProbComp) := fun kd => do
  let st ← get
  match st.2 kd with
  | some k => return k
  | none =>
      let k ← ($ᵗ K : ProbComp K)
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
    FujisakiOkamoto.Variant (hashOracleSpec M R KD K) M PK C R K where
  QueryCache := QueryCache M R KD K
  initCache := (∅, ∅)
  queryImpl := queryImpl (M := M) (R := R) (KD := KD) (K := K)
  deriveCoins := fun {m} [Monad m] [MonadLiftT ProbComp m]
      [HasQuery (hashOracleSpec M R KD K) m] _pk msg =>
    HasQuery.query (spec := hashOracleSpec M R KD K) (m := m) (Sum.inl msg)
  deriveKey := fun {m} [Monad m] [MonadLiftT ProbComp m]
      [HasQuery (hashOracleSpec M R KD K) m] _pk msg c =>
    HasQuery.query (spec := hashOracleSpec M R KD K) (m := m) (Sum.inr (kdInput msg c))

end UTransform

open UTransform

variable {M PK SK R C KD K KPRF : Type}

/-- The generic two-RO U-transform family. The argument `kdInput` chooses whether the shared key
is derived from `m`, `(m, c)`, or some other encoding of the recovered plaintext and ciphertext. -/
def UTransform
    {m : Type → Type v} [Monad m] [MonadLiftT ProbComp m]
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    [DecidableEq M] [DecidableEq C] [DecidableEq KD]
    [SampleableType M] [SampleableType R] [SampleableType K]
    [HasQuery (UTransform.hashOracleSpec M R KD K) m] :
    KEMScheme m
      K PK ((PK × SK) × policy.FallbackState) C :=
  FujisakiOkamoto.scheme (m := m) pke
    (UTransform.variant (PK := PK) (kdInput := kdInput) (M := M) (C := C) (R := R) (KD := KD)
      (K := K))
    policy

namespace UTransform

section costAccounting

variable [DecidableEq M] [DecidableEq C] [DecidableEq KD]
  [SampleableType M] [SampleableType R] [SampleableType K]

variable {m : Type → Type v} [Monad m] [LawfulMonad m] [MonadLiftT ProbComp m]

/-- If each of the two U-transform oracle families is assigned a constant weight, encapsulation
incurs exactly the sum of those family weights. -/
theorem encaps_usesExactFamilyWeightedCost {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    (pk : PK) (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω)
    (wCoins wKey : ω)
    (hCoins : ∀ msg, costFn (Sum.inl msg) = wCoins)
    (hKeys : ∀ kd, costFn (Sum.inr kd) = wKey) :
    QueryCost[
      (UTransform pke kdInput policy).encaps pk in runtime by costFn
    ] = wCoins + wKey := by
  rw [HasQuery.UsesCostExactly]
  change Cost[
    ((monadLift ((monadLift ($ᵗ M : ProbComp M) : m M)) : AddWriterT ω m M) >>= fun msg => do
      let r ← (runtime.withAddCost costFn) (Sum.inl msg)
      let c := pke.encrypt pk msg r
      let k ← (runtime.withAddCost costFn) (Sum.inr (kdInput msg c))
      pure (c, k))
  ] = wCoins + wKey
  rw [AddWriterT.hasCost_iff]
  simp [QueryImpl.withAddCost_apply, AddWriterT.outputs, AddWriterT.costs, hCoins, hKeys]

/-- Under per-family upper bounds on the two U-transform oracle families, encapsulation incurs
weighted query cost at most the sum of those bounds. -/
theorem encaps_usesWeightedQueryCostAtMost {ω : Type}
    [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] [HasEvalSet m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    (pk : PK) (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω)
    (wCoins wKey : ω)
    (hCoins : ∀ msg, costFn (Sum.inl msg) ≤ wCoins)
    (hKeys : ∀ kd, costFn (Sum.inr kd) ≤ wKey) :
    QueryCost[ (UTransform pke kdInput policy).encaps pk in runtime by costFn ] ≤
      wCoins + wKey := by
  rw [HasQuery.UsesCostAtMost]
  let f : M → AddWriterT ω m (C × K) := fun msg =>
    ((runtime.withAddCost costFn) (Sum.inl msg)) >>= fun r =>
      ((runtime.withAddCost costFn) (Sum.inr (kdInput msg (pke.encrypt pk msg r)))) >>=
        fun k => pure (pke.encrypt pk msg r, k)
  change AddWriterT.PathwiseCostAtMost
    (((monadLift ((monadLift ($ᵗ M : ProbComp M) : m M)) : AddWriterT ω m M) >>= f))
    (wCoins + wKey)
  have hbind :
      AddWriterT.PathwiseCostAtMost
        (((monadLift ((monadLift ($ᵗ M : ProbComp M) : m M)) : AddWriterT ω m M) >>= f))
        (0 + (wCoins + wKey)) := by
    refine AddWriterT.pathwiseCostAtMost_bind (f := f) (w₁ := 0) (w₂ := wCoins + wKey)
      (AddWriterT.pathwiseCostAtMost_monadLift (m := m) ((monadLift ($ᵗ M : ProbComp M)) : m M))
      ?_
    intro msg
    refine AddWriterT.pathwiseCostAtMost_bind (w₁ := wCoins) (w₂ := wKey) ?_ ?_
    · change AddWriterT.PathwiseCostAtMost
          ((runtime.withAddCost costFn) (Sum.inl msg)) wCoins
      exact HasQuery.usesCostAtMost_query_of_le
        (runtime := runtime) (costFn := costFn) (t := Sum.inl msg) (b := wCoins) (hCoins msg)
    · intro r
      let c := pke.encrypt pk msg r
      have hk :
          AddWriterT.PathwiseCostAtMost
            ((((runtime.withAddCost costFn) (Sum.inr (kdInput msg c))) >>= fun k =>
              pure (c, k)))
            (wKey + 0) := by
        refine AddWriterT.pathwiseCostAtMost_bind (w₁ := wKey) (w₂ := 0) ?_ ?_
        · exact HasQuery.usesCostAtMost_query_of_le
            (runtime := runtime) (costFn := costFn)
            (t := Sum.inr (kdInput msg c)) (b := wKey) (hKeys (kdInput msg c))
        · intro k
          simpa [c] using AddWriterT.pathwiseCostAtMost_pure (m := m) ((c, k) : C × K)
      simpa [add_zero] using hk
  simpa [zero_add] using hbind

/-- Unit-cost specialization: U-transform encapsulation always makes exactly two oracle queries,
one to derive coins and one to derive the shared key. -/
theorem encaps_usesExactlyTwoQueries
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    (pk : PK) :
    Queries[ (UTransform pke kdInput policy).encaps pk in runtime ] = 2 := by
  simpa [HasQuery.UsesExactlyQueries] using
    (encaps_usesExactFamilyWeightedCost
      (ω := ℕ) (runtime := runtime) (pke := pke) (kdInput := kdInput) (policy := policy)
      (pk := pk) (costFn := fun _ ↦ 1) (wCoins := 1) (wKey := 1)
      (hCoins := fun _ ↦ rfl) (hKeys := fun _ ↦ rfl))

/-- Expected weighted query cost of U-transform encapsulation under constant per-family weights. -/
theorem encaps_expectedQueryCost_eq_of_constantOracleWeights {ω : Type}
    [AddMonoid ω] [Preorder ω] [HasEvalPMF m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    (pk : PK) (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω)
    (wCoins wKey : ω) (val : ω → ENNReal) (hval : Monotone val)
    (hCoins : ∀ msg, costFn (Sum.inl msg) = wCoins)
    (hKeys : ∀ kd, costFn (Sum.inr kd) = wKey) :
    ExpectedQueryCost[
      (UTransform pke kdInput policy).encaps pk in runtime by costFn via val
    ] = val (wCoins + wKey) :=
  HasQuery.expectedQueryCost_eq_of_usesCostExactly
    (encaps_usesExactFamilyWeightedCost
      (runtime := runtime) (pke := pke) (kdInput := kdInput) (policy := policy) (pk := pk)
      (costFn := costFn) (wCoins := wCoins) (wKey := wKey) hCoins hKeys)
    hval

/-- Expected weighted query cost of U-transform encapsulation is bounded by the sum of the
per-family bounds. -/
theorem encaps_expectedQueryCost_le {ω : Type}
    [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] [HasEvalPMF m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    (pk : PK) (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω)
    (wCoins wKey : ω) (val : ω → ENNReal) (hval : Monotone val)
    (hCoins : ∀ msg, costFn (Sum.inl msg) ≤ wCoins)
    (hKeys : ∀ kd, costFn (Sum.inr kd) ≤ wKey) :
    ExpectedQueryCost[
      (UTransform pke kdInput policy).encaps pk in runtime by costFn via val
    ] ≤ val (wCoins + wKey) :=
  HasQuery.expectedQueryCost_le_of_usesCostAtMost
    (encaps_usesWeightedQueryCostAtMost
      (runtime := runtime) (pke := pke) (kdInput := kdInput) (policy := policy) (pk := pk)
      (costFn := costFn) (wCoins := wCoins) (wKey := wKey) hCoins hKeys)
    hval

/-- Expected query count of U-transform encapsulation is exactly `2`. -/
theorem encaps_expectedQueries_eq_two [HasEvalPMF m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    (pk : PK) :
    ExpectedQueries[ (UTransform pke kdInput policy).encaps pk in runtime ] = 2 :=
  HasQuery.expectedQueries_eq_of_usesExactlyQueries
    (encaps_usesExactlyTwoQueries
      (runtime := runtime) (pke := pke) (kdInput := kdInput) (policy := policy) (pk := pk))

/-- If deterministic decryption fails immediately, U-transform decapsulation incurs zero weighted
query cost. -/
theorem decaps_usesZeroQueryCost_of_decrypt_eq_none {ω : Type} [AddMonoid ω]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    (pk : PK) (sk : SK) (fb : policy.FallbackState) (c : C)
    (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω)
    (hdec : pke.decrypt sk c = none) :
    QueryCost[
      (UTransform pke kdInput policy).decaps ((pk, sk), fb) c in runtime by costFn
    ] = 0 := by
  rw [HasQuery.UsesCostExactly]
  change Cost[
    (match pke.decrypt sk c with
    | none => pure (policy.onReject fb c)
    | some msg => do
        let r ← (runtime.withAddCost costFn) (Sum.inl msg)
        if pke.encrypt pk msg r = c then
          let k ← (runtime.withAddCost costFn) (Sum.inr (kdInput msg c))
          pure (some k)
        else
          pure (policy.onReject fb c) : AddWriterT ω m (Option K))
  ] = 0
  rw [AddWriterT.hasCost_iff]
  simp [hdec, AddWriterT.outputs, AddWriterT.costs]

/-- Under per-family upper bounds on the two U-transform oracle families, decapsulation incurs
weighted query cost at most the sum of those bounds. -/
theorem decaps_usesWeightedQueryCostAtMost {ω : Type}
    [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω]
    [HasEvalSet m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    (pk : PK) (sk : SK) (fb : policy.FallbackState) (c : C)
    (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω)
    (wCoins wKey : ω)
    (hCoins : ∀ msg, costFn (Sum.inl msg) ≤ wCoins)
    (hKeys : ∀ kd, costFn (Sum.inr kd) ≤ wKey) :
    QueryCost[
      (UTransform pke kdInput policy).decaps ((pk, sk), fb) c in runtime by costFn
    ] ≤ wCoins + wKey := by
  rw [HasQuery.UsesCostAtMost]
  cases hdec : pke.decrypt sk c with
  | none =>
      exact HasQuery.usesCostAtMost_of_usesCostExactly
        (decaps_usesZeroQueryCost_of_decrypt_eq_none
          (runtime := runtime) (pke := pke) (kdInput := kdInput) (policy := policy)
          (pk := pk) (sk := sk) (fb := fb) (c := c) (costFn := costFn) hdec)
        (by simp)
  | some msg =>
    let variant : FujisakiOkamoto.Variant (UTransform.hashOracleSpec M R KD K) M PK C R K :=
      UTransform.variant (PK := PK) (M := M) (C := C) (R := R) (KD := KD) (K := K) kdInput
    letI := (runtime.withAddCost costFn).toHasQuery
    suffices hbranch :
        AddWriterT.PathwiseCostAtMost
          (((variant.deriveCoins (m := AddWriterT ω m) pk msg) >>= fun r =>
            if pke.encrypt pk msg r = c then
              some <$> (variant.deriveKey (m := AddWriterT ω m) pk msg c)
            else pure (policy.onReject fb c)))
          (wCoins + wKey) by
      simpa [HasQuery.Program.withAddCost, UTransform, FujisakiOkamoto.scheme, hdec] using hbranch
    refine AddWriterT.pathwiseCostAtMost_bind (w₁ := wCoins) (w₂ := wKey) ?_ ?_
    · change AddWriterT.PathwiseCostAtMost
          (HasQuery.query
            (spec := UTransform.hashOracleSpec M R KD K) (m := AddWriterT ω m) (Sum.inl msg))
          wCoins
      exact HasQuery.usesCostAtMost_query_of_le
        (runtime := runtime) (costFn := costFn) (t := Sum.inl msg) (b := wCoins) (hCoins msg)
    · intro r
      by_cases henc : pke.encrypt pk msg r = c
      · suffices hsucc :
            AddWriterT.PathwiseCostAtMost
              (some <$> (variant.deriveKey (m := AddWriterT ω m) pk msg c))
              wKey by
          simpa [henc] using hsucc
        change AddWriterT.PathwiseCostAtMost
          (some <$>
            (HasQuery.query
              (spec := UTransform.hashOracleSpec M R KD K) (m := AddWriterT ω m)
              (Sum.inr (kdInput msg c))))
          wKey
        exact AddWriterT.pathwiseCostAtMost_map some
          (HasQuery.usesCostAtMost_query_of_le
            (runtime := runtime) (costFn := costFn)
            (t := Sum.inr (kdInput msg c)) (b := wKey) (hKeys (kdInput msg c)))
      · simpa [henc] using
          AddWriterT.pathwiseCostAtMost_mono
            (AddWriterT.pathwiseCostAtMost_pure (m := m) (policy.onReject fb c : Option K))
            (by exact zero_le wKey)

/-- If deterministic decryption fails immediately, decapsulation has expected weighted query cost
`0`. -/
theorem decaps_expectedQueryCost_eq_zero_of_decrypt_eq_none {ω : Type}
    [AddMonoid ω] [Preorder ω] [HasEvalPMF m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    (pk : PK) (sk : SK) (fb : policy.FallbackState) (c : C)
    (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω)
    (val : ω → ENNReal) (hval : Monotone val)
    (hdec : pke.decrypt sk c = none) :
    ExpectedQueryCost[
      (UTransform pke kdInput policy).decaps ((pk, sk), fb) c in runtime by costFn via val
    ] = val 0 :=
  HasQuery.expectedQueryCost_eq_of_usesCostExactly
    (decaps_usesZeroQueryCost_of_decrypt_eq_none
      (runtime := runtime) (pke := pke) (kdInput := kdInput) (policy := policy)
      (pk := pk) (sk := sk) (fb := fb) (c := c) (costFn := costFn) hdec)
    hval

/-- Expected weighted query cost of U-transform decapsulation is bounded by the sum of the
per-family bounds. -/
theorem decaps_expectedQueryCost_le {ω : Type}
    [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] [CanonicallyOrderedAdd ω]
    [HasEvalPMF m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    (pk : PK) (sk : SK) (fb : policy.FallbackState) (c : C)
    (costFn : (UTransform.hashOracleSpec M R KD K).Domain → ω)
    (wCoins wKey : ω) (val : ω → ENNReal) (hval : Monotone val)
    (hCoins : ∀ msg, costFn (Sum.inl msg) ≤ wCoins)
    (hKeys : ∀ kd, costFn (Sum.inr kd) ≤ wKey) :
    ExpectedQueryCost[
      (UTransform pke kdInput policy).decaps ((pk, sk), fb) c in runtime by costFn via val
    ] ≤ val (wCoins + wKey) :=
  HasQuery.expectedQueryCost_le_of_usesCostAtMost
    (decaps_usesWeightedQueryCostAtMost
      (runtime := runtime) (pke := pke) (kdInput := kdInput) (policy := policy)
      (pk := pk) (sk := sk) (fb := fb) (c := c) (costFn := costFn)
      (wCoins := wCoins) (wKey := wKey) hCoins hKeys)
    hval

/-- Unit-cost specialization: U-transform decapsulation makes at most two oracle queries. -/
theorem decaps_usesAtMostTwoQueries [HasEvalSet m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    (pk : PK) (sk : SK) (fb : policy.FallbackState) (c : C) :
    Queries[ (UTransform pke kdInput policy).decaps ((pk, sk), fb) c in runtime ] ≤ 2 := by
  simpa [HasQuery.UsesAtMostQueries] using
    (decaps_usesWeightedQueryCostAtMost
      (ω := ℕ) (runtime := runtime) (pke := pke) (kdInput := kdInput) (policy := policy)
      (pk := pk) (sk := sk) (fb := fb) (c := c) (costFn := fun _ ↦ 1) (wCoins := 1) (wKey := 1)
      (hCoins := fun _ ↦ le_rfl) (hKeys := fun _ ↦ le_rfl))

/-- Expected query count of U-transform decapsulation is at most `2`. -/
theorem decaps_expectedQueries_le_two [HasEvalPMF m]
    (runtime : QueryImpl (UTransform.hashOracleSpec M R KD K) m)
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (kdInput : M → C → KD)
    (policy : FujisakiOkamoto.RejectionPolicy K C)
    (pk : PK) (sk : SK) (fb : policy.FallbackState) (c : C) :
    ExpectedQueries[ (UTransform pke kdInput policy).decaps ((pk, sk), fb) c in runtime ] ≤ 2 :=
  HasQuery.expectedQueries_le_of_usesAtMostQueries
    (decaps_usesAtMostTwoQueries
      (runtime := runtime) (pke := pke) (kdInput := kdInput) (policy := policy)
      (pk := pk) (sk := sk) (fb := fb) (c := c))

end costAccounting

/-- Runtime bundle for the two-RO U-transform oracle world. -/
noncomputable def runtime
    {M R KD K : Type}
    [DecidableEq M] [DecidableEq KD] [SampleableType R] [SampleableType K] :
    ProbCompRuntime (OracleComp (oracleSpec M R KD K)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := queryImpl (M := M) (R := R) (KD := KD) (K := K))
    ((∅, ∅) : QueryCache M R KD K)
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- The generic U-transform CCA bound.

**WARNING: this is a placeholder statement, not the final theorem.** The current shape is
unsound as written: `correctnessBound₁` and `correctnessBound₂` are unconstrained `ℝ`
parameters, so the right-hand side can be made arbitrarily negative while the left-hand side
is a probability and hence nonnegative. In the final statement these slack terms must be
constrained (for example, derived from a correctness/`δ`-correctness assumption on `pke`,
quantified as nonnegative reals, or replaced by a concrete expression in `pke`'s correctness
error and the adversary's query budget).

The proof is intentionally deferred. The reduction artifacts (`prfAdv`, `owAdv`) are
existentially quantified rather than passed in as unrelated inputs, but the bound itself
still needs to be tightened before this can be a meaningful security claim. -/
theorem IND_CCA_bound
    {M PK SK R C KD K KPRF : Type}
    [DecidableEq M] [DecidableEq C] [DecidableEq KD]
    [SampleableType M] [SampleableType R] [SampleableType K]
    (pke : AsymmEncAlg.ExplicitCoins ProbComp M PK SK R C)
    (prf : PRFScheme KPRF C K)
    (kdInput : M → C → KD)
    (adversary : (UTransform (m := OracleComp (UTransform.oracleSpec M R KD K))
      pke kdInput (FujisakiOkamoto.implicitRejection prf)).IND_CCA_Adversary)
    (correctnessBound₁ correctnessBound₂ : ℝ) :
    ∃ prfAdv : PRFScheme.PRFAdversary C K,
      ∃ owAdv : OW_PCVA_Adversary (TTransform pke),
        (UTransform (m := OracleComp (UTransform.oracleSpec M R KD K))
          pke kdInput (FujisakiOkamoto.implicitRejection prf)).IND_CCA_Advantage
            (runtime (M := M) (R := R) (KD := KD) (K := K)) adversary ≤
          PRFScheme.prfAdvantage prf prfAdv +
          correctnessBound₁ +
          correctnessBound₂ +
          (OW_PCVA_Advantage (encAlg := TTransform pke) (TTransform.runtime (M := M)
            (R := R)) owAdv).toReal := by
  sorry

end UTransform
