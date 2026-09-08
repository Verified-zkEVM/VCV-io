/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.Scheme
public import VCVio.CryptoFoundations.SignatureAlg
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
public import VCVio.OracleComp.SimSemantics.StateT.BundledSemantics

/-!
# SLH-DSA in the public-hash random-oracle model

This file lifts the explicit-evidence `d = 1` compatibility programs of `HashSig.SLHDSA.Scheme`
into one external signature algorithm; the canonical scheme path for every validated depth is
`HashSig.SLHDSA.GeneralScheme`.
Fresh seeds and the signing randomizer are lifted from `ProbComp`; `H_msg` and every tweakable
hash remain explicit `HasQuery (publicHashSpec core)` calls. The random-oracle
specialization uses one lazy cache for the complete experiment. Consequently key generation,
the adversary, every signing-oracle call, and final verification all see the same public-hash
table.

The model intentionally excludes the secret operations `PRF` and `PRF_msg`, which remain pure
fields of `CorePrimitives`. Thus this is a public-hash ROM formalization, not a claim that every
named SLH-DSA operation is an independent raw-hash oracle.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SLHDSA

variable {p : Params}
variable (hd : p.d = 1)

/-! ### External algorithms over the depth-one compatibility surface -/

/-- External key generation: sample the three FIPS 205 seeds, then run the `d = 1`
compatibility internal explicit-query program. -/
def slhKeygenM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [MonadLiftT ProbComp m] [HasQuery (publicHashSpec core) m]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [SampleableType core.PkSeed] : m (PublicKeyCore core × SecretKeyCore core) := do
  let skSeed ← (monadLift ($ᵗ core.SkSeed) : m core.SkSeed)
  let skPrf ← (monadLift ($ᵗ core.SkPrf) : m core.SkPrf)
  let pkSeed ← (monadLift ($ᵗ core.PkSeed) : m core.PkSeed)
  slhKeygenInternalM hd core skSeed skPrf pkSeed

/-- External hedged signing for the empty-context API: sample `addrnd`, encode the external
message, then run the `d = 1` compatibility internal explicit-query signer. -/
def slhSignM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [MonadLiftT ProbComp m] [HasQuery (publicHashSpec core) m]
    [SampleableType core.Y] (sk : SecretKeyCore core) (msg : List Byte) :
    m (SignatureCore p core) := do
  let addrnd ← (monadLift ($ᵗ core.Y) : m core.Y)
  slhSignInternalM hd core (emptyContextMessage msg) sk addrnd

/-- External empty-context verification via the `d = 1` compatibility internal explicit-query
verifier. -/
def slhVerifyM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
    (pk : PublicKeyCore core) (msg : List Byte) (sig : SignatureCore p core) : m Bool :=
  slhVerifyInternalM hd core (emptyContextMessage msg) sig pk

/-- The oracle-parametric signature scheme over the explicit-evidence `d = 1` compatibility
surface. Its algorithms are generic over the public-randomness lift and the public-hash
query capability. The unrestricted `Params` carrier does not yet encode `d = 1` as a type-level
invariant; the canonical arbitrary-depth internal scheme is `HashSig.SLHDSA.GeneralScheme`. -/
def slhdsaAlg (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [MonadLiftT ProbComp m] [HasQuery (publicHashSpec core) m]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [SampleableType core.PkSeed] [SampleableType core.Y] [DecidableEq core.Y] :
    SignatureAlg m (List Byte) (PublicKeyCore core) (SecretKeyCore core)
      (SignatureCore p core) where
  keygen := slhKeygenM hd core
  sign _pk sk msg := slhSignM hd core sk msg
  verify pk msg sig := slhVerifyM hd core pk msg sig

/-! ### Deterministic public-hash specialization -/

/-- The concrete-function scheme is definitionally the oracle-parametric scheme above
interpreted by preserving uniform sampling and answering every public-hash query with `prims`.
There is no second implementation and therefore no scheme-equivalence theorem to maintain. -/
def slhdsaConcreteAlg (prims : Primitives p)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y] :
    SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core) (SecretKeyCore prims.core)
      (SignatureCore p prims.core) :=
  SignatureAlg.map (simulateQ' (unifFwdAnswerImpl (PublicHash.impl prims)))
    (slhdsaAlg (m := OracleComp (unifSpec + publicHashSpec prims.core)) hd prims.core)

private theorem slhdsaConcreteAlg_components (prims : Primitives p)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y] :
    slhdsaConcreteAlg hd prims =
      ({ keygen := do
            let skSeed ← $ᵗ prims.SkSeed
            let skPrf ← $ᵗ prims.SkPrf
            let pkSeed ← $ᵗ prims.PkSeed
            pure (slhKeygenInternal hd prims skSeed skPrf pkSeed)
         sign := fun _pk sk msg => do
            let addrnd ← $ᵗ prims.Y
            pure (slhSignInternal hd prims (emptyContextMessage msg) sk addrnd)
         verify := fun pk msg sig =>
            pure (slhVerifyInternal hd prims (emptyContextMessage msg) sig pk) } :
        SignatureAlg ProbComp (List Byte) (PublicKeyCore prims.core)
          (SecretKeyCore prims.core) (SignatureCore p prims.core)) := by
  let _ : HasQuery (publicHashSpec prims.core) ProbComp :=
    ⟨fun q => liftM (PublicHash.impl prims q)⟩
  let F : HasQuery.QueryHom (publicHashSpec prims.core)
      (OracleComp (unifSpec + publicHashSpec prims.core)) ProbComp :=
    { toMonadHom := simulateQ' (unifFwdAnswerImpl (PublicHash.impl prims))
      map_query' := fun q => by
        simpa [unifFwdAnswerImpl] using
          (QueryImpl.simulateQ_add_liftM_query_right
            (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp))
            ((PublicHash.impl prims).liftTarget ProbComp) q) }
  have hLift : HasQuery.PreservesProbCompLift F.toMonadHom := by
    intro α oa
    change simulateQ (unifFwdAnswerImpl (PublicHash.impl prims))
      (liftM oa : OracleComp (unifSpec + publicHashSpec prims.core) α) = oa
    rw [unifFwdAnswerImpl, QueryImpl.simulateQ_add_liftM_left,
      HasQuery.toQueryImpl_eq_id', simulateQ_id']
  have hMap :
      SignatureAlg.map F.toMonadHom
          (slhdsaAlg (m := OracleComp (unifSpec + publicHashSpec prims.core)) hd prims.core) =
        slhdsaAlg (m := ProbComp) hd prims.core := by
    apply SignatureAlg.ext
    · simp [slhdsaAlg, slhKeygenM, hLift ($ᵗ prims.SkSeed), hLift ($ᵗ prims.SkPrf),
        hLift ($ᵗ prims.PkSeed), slhKeygenInternalM_natural hd prims.core F]
    · funext pk sk msg
      simp [slhdsaAlg, slhSignM, hLift ($ᵗ prims.Y),
        slhSignInternalM_natural hd prims.core F]
    · funext pk msg sig
      exact slhVerifyInternalM_natural hd prims.core F (emptyContextMessage msg) sig pk
  change SignatureAlg.map F.toMonadHom
      (slhdsaAlg (m := OracleComp (unifSpec + publicHashSpec prims.core)) hd prims.core) = _
  rw [hMap]
  have hImpl :
      (HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp)) =
        (PublicHash.impl prims).liftTarget ProbComp := by
    funext q
    rfl
  have hKeygen : ∀ skSeed skPrf pkSeed,
      simulateQ (HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp))
          (slhKeygenInternalM hd prims.core skSeed skPrf pkSeed :
            OracleComp (publicHashSpec prims.core) _) =
        pure (slhKeygenInternal hd prims skSeed skPrf pkSeed) := by
    intro skSeed skPrf pkSeed
    rw [hImpl, simulateQ_liftTarget]
    rfl
  have hSign : ∀ msg sk addrnd,
      simulateQ (HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp))
          (slhSignInternalM hd prims.core msg sk addrnd :
            OracleComp (publicHashSpec prims.core) _) =
        pure (slhSignInternal hd prims msg sk addrnd) := by
    intro msg sk addrnd
    rw [hImpl, simulateQ_liftTarget]
    rfl
  have hVerify : ∀ msg sig pk,
      simulateQ (HasQuery.toQueryImpl (spec := publicHashSpec prims.core) (m := ProbComp))
          (slhVerifyInternalM hd prims.core msg sig pk :
            OracleComp (publicHashSpec prims.core) _) =
        pure (slhVerifyInternal hd prims msg sig pk) := by
    intro msg sig pk
    rw [hImpl, simulateQ_liftTarget]
    rfl
  apply SignatureAlg.ext
  · simp [slhdsaAlg, slhKeygenM, hKeygen,
      ← slhKeygenInternalM_natural hd prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp))]
  · funext pk sk msg
    simp [slhdsaAlg, slhSignM, hSign,
      ← slhSignInternalM_natural hd prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp))]
  · funext pk msg sig
    simp [slhdsaAlg, slhVerifyM, hVerify,
      ← slhVerifyInternalM_natural hd prims.core
        (HasQuery.QueryHom.ofSimulateQ (spec := publicHashSpec prims.core) (m := ProbComp))]

/-- Perfect completeness of the definitional concrete-function specialization. -/
theorem slhdsaConcreteAlg_perfectlyComplete (prims : Primitives p)
    [SampleableType prims.SkSeed] [SampleableType prims.SkPrf]
    [SampleableType prims.PkSeed] [SampleableType prims.Y] [DecidableEq prims.Y] :
    (slhdsaConcreteAlg hd prims).PerfectlyComplete ProbCompRuntime.probComp := by
  intro msg
  set mx : ProbComp Bool := do
    let (pk, sk) ← (slhdsaConcreteAlg hd prims).keygen
    let sig ← (slhdsaConcreteAlg hd prims).sign pk sk msg
    (slhdsaConcreteAlg hd prims).verify pk msg sig with hmx
  have huniq : ∀ y ∈ support mx, y = true := by
    intro y hy
    rw [hmx] at hy
    rw [slhdsaConcreteAlg_components hd prims] at hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨⟨pk, sk⟩, hpksk, hy⟩ := hy
    rw [mem_support_bind_iff] at hy
    obtain ⟨sig, hsig, hy⟩ := hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rw [mem_support_bind_iff] at hpksk
    obtain ⟨skSeed, -, hpksk⟩ := hpksk
    rw [mem_support_bind_iff] at hpksk
    obtain ⟨skPrf, -, hpksk⟩ := hpksk
    rw [mem_support_bind_iff] at hpksk
    obtain ⟨pkSeed, -, hpksk⟩ := hpksk
    simp only [support_pure, Set.mem_singleton_iff] at hpksk
    rw [mem_support_bind_iff] at hsig
    obtain ⟨addrnd, -, hsig⟩ := hsig
    simp only [support_pure, Set.mem_singleton_iff] at hsig
    subst hsig
    have hpk : pk = (slhKeygenInternal hd prims skSeed skPrf pkSeed).1 :=
      congrArg Prod.fst hpksk
    have hsk : sk = (slhKeygenInternal hd prims skSeed skPrf pkSeed).2 :=
      congrArg Prod.snd hpksk
    subst hpk; subst hsk
    exact slhVerifyInternal_slhSignInternal hd prims (emptyContextMessage msg)
      skSeed skPrf pkSeed addrnd
  change Pr[= true | mx] = 1
  exact probOutput_eq_one_of_support_subset_singleton
    (NeverFail.probFailure_eq_zero (mx := mx)) huniq

/-! ### One shared lazy-random-oracle runtime -/

namespace PublicHash

open scoped Classical in
/-- Runtime for the combined fresh-uniform/public-hash world, starting from a supplied public-hash
cache. This is the programming hook for reductions. The cache is installed once around the whole
experiment; it is not reset between scheme components or signing-oracle calls. -/
noncomputable def runtimeWithCache (core : CorePrimitives p)
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.Y] [SampleableType (Bytes p.m)]
    (cache : PublicHash.Cache core) :
    ProbCompRuntime (OracleComp (unifSpec + publicHashSpec core)) where
  toSPMFSemantics := SPMFSemantics.withStateOracle
    (hashImpl := PublicHash.randomOracle core) cache
  toProbCompLift := ProbCompLift.ofMonadLift _

open scoped Classical in
/-- Standard SLH-DSA public-hash ROM runtime, starting from the empty cache. -/
noncomputable def runtime (core : CorePrimitives p)
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.Y] [SampleableType (Bytes p.m)] :
    ProbCompRuntime (OracleComp (unifSpec + publicHashSpec core)) :=
  runtimeWithCache core ∅

end PublicHash

/-! ### End-to-end shared-ROM completeness -/

open scoped Classical in
/-- The depth-one oracle-parametric SLH-DSA scheme is perfectly complete under the runtime that
threads one lazy public-hash random-oracle cache through the entire experiment.

The proof uses the generic mixed-uniform/random-oracle probability-one bridge. It reduces the
lazy oracle to every fixed total hash table and then applies deterministic correctness. -/
theorem slhdsaAlg_perfectlyComplete (core : CorePrimitives p)
    [DecidableEq core.PkSeed] [DecidableEq core.AdrsKey] [DecidableEq core.Y]
    [SampleableType core.SkSeed] [SampleableType core.SkPrf]
    [SampleableType core.PkSeed] [SampleableType core.Y]
    [SampleableType (Bytes p.m)] :
    (slhdsaAlg (m := OracleComp (unifSpec + publicHashSpec core)) hd core).PerfectlyComplete
      (PublicHash.runtime core) := by
  let _ : ∀ q : (publicHashSpec core).Domain,
      SampleableType ((publicHashSpec core).Range q) := fun q => by
    cases q <;> infer_instance
  intro msg
  let alg := slhdsaAlg (m := OracleComp (unifSpec + publicHashSpec core)) hd core
  let oa : OracleComp (unifSpec + publicHashSpec core) Bool := do
    let (pk, sk) ← alg.keygen
    let sig ← alg.sign pk sk msg
    alg.verify pk msg sig
  change Pr[= true | (PublicHash.runtime core).evalSPMF oa] = 1
  unfold PublicHash.runtime PublicHash.runtimeWithCache ProbCompRuntime.evalSPMF
    SPMFSemantics.evalSPMF SemanticsVia.denote SPMFSemantics.withStateOracle
  rw [probOutput_evalSPMF]
  change Pr[= true |
    (simulateQ (unifFwdImpl (publicHashSpec core) + PublicHash.randomOracle core) oa).run' ∅] = 1
  rw [← probEvent_eq_eq_probOutput, StateT.run', probEvent_map]
  apply (OracleComp.probEvent_eq_one_simulateQ_unifFwdImpl_add_randomOracle_run_iff
    (oa := oa) (preexisting_cache := (∅ : PublicHash.Cache core))
    (fun b => b = true)).2
  intro f _hf
  let prims := PublicHash.withPublicHash core f
  have hAlg' : SignatureAlg.map (simulateQ' (unifFwdAnswerImpl f)) alg =
      slhdsaConcreteAlg hd prims := by
    simp [alg, prims, slhdsaConcreteAlg, PublicHash.impl_withPublicHash]
  rw [probEvent_eq_eq_probOutput]
  simp only [oa, simulateQ_bind]
  change Pr[= true | do
    let (pk, sk) ←
      (SignatureAlg.map (simulateQ' (unifFwdAnswerImpl f)) alg).keygen
    let sig ←
      (SignatureAlg.map (simulateQ' (unifFwdAnswerImpl f)) alg).sign pk sk msg
    (SignatureAlg.map (simulateQ' (unifFwdAnswerImpl f)) alg).verify pk msg sig] = 1
  rw [hAlg']
  exact slhdsaConcreteAlg_perfectlyComplete hd prims msg

end SLHDSA
