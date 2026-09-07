/-
Copyright (c) 2026 Oleksandr Vovkotrub. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oleksandr Vovkotrub
-/

module
public import LatticeCrypto.MLDSA.SecurityNMA

/-!
# ML-DSA EUF-NMA security with `ExpandA` a programmed random oracle

The short-model EUF-NMA analysis of `LatticeCrypto.MLDSA.SecurityNMA` states its Module-LWE
assumption over seeds: the public challenge is `ρ` and the matrix is `ExpandA(ρ)` for the fixed
deterministic `prims.expandA`. For a fixed function no bridge from that seed-based problem to the
literature's uniform-matrix Module-LWE exists — a distinguisher receiving `(ρ, Â)` can recompute
`ExpandA(ρ)` and compare — so the uniform-matrix problem can only be reached by *modelling*
`ExpandA` as a random oracle.

This file is that model. `ExpandA` becomes a third oracle `Bytes 32 →ₒ TqMatrix p.k p.l`
alongside uniform sampling and the commitment hash `H`, and it is **shared**: the honest key
generator `keygenShortRO` obtains `Â = ExpandA(ρ)` by querying it, the honest verifier
`verifyRO` re-queries it at `pk.ρ`, and the forger queries it at will. Both reductions
**program** it: they receive a uniform matrix `Â` from their hardness challenger, choose the seed
`ρ` themselves, and answer the forger's `ExpandA` queries lazily from a cache pre-seeded with
`ρ ↦ Â` (`programmedAt`), so that the forger's view is exactly the honest game's.

## Main results

* `romNmaAdvantage_eq_game0`: the ROM EUF-NMA game **is** the real branch of the uniform-matrix
  Module-LWE game `mldsaMatrixMLWE` against `distinguisherBRom` — an exact identity, since a lazy
  oracle whose first query at `ρ` returns a fresh uniform matrix is the same as a cache
  pre-seeded at `ρ` with the challenger's uniform matrix.
* `game1_le_stmsis_rom`: the uniform branch is bounded by the SelfTargetMSIS advantage of
  `extractorCRom` against the uniform-matrix tailored problem `mldsaSTMSISMatrix`.
* `nma_security_rom`: for every ROM forger there are a uniform-matrix MLWE adversary `B` and a
  uniform-matrix SelfTargetMSIS adversary `C` with
  `Adv^{EUF-NMA}_{ROM}(A) ≤ Adv^{MLWE}(B) + Adv^{SelfTargetMSIS}(C)`, with no idealization slack
  and no hypothesis beyond the forger.

## How the oracle model is pinned to the scheme

The identification verifier and the short key generator are the scheme's own algorithms with the
`ExpandA` evaluation abstracted into a parameter: `verifyWithMatrix` is the verifier at an explicit
matrix and `identificationScheme.verify` is it at `ExpandA(pk.ρ)`
(`identificationScheme_verify_eq_verifyWithMatrix`, definitional); `keygenShortWith` is the short
key generator at an explicit expansion function and `keygenShort` is it at `prims.expandA`
(`keygenShort_eq_keygenShortWith`, definitional). Answering the ROM algorithms' `ExpandA` queries
from any fixed table `f` recovers those parametrized algorithms at `f`
(`simulateQ_tableImpl_keygenShortRO`, `simulateQ_tableImpl_verifyRO`); at the scheme's own table
`prims.expandA` they are exactly `keygenShort` and the signature's `verify`
(`simulateQ_tableImpl_expandA_keygenShortRO`, `simulateQ_tableImpl_expandA_verifyRO`). So the ROM
game is the scheme's EUF-NMA game with `prims.expandA` replaced by a lazily sampled random
function, and nothing else changed.

## What is *not* modelled

The forger's `ExpandA` queries are unbounded and the cost of either reduction is not accounted
for; both wait on the cost-model infrastructure. The SelfTargetMSIS leg lands on the *tailored*
verifier relation `mldsaSTMSISMatrix` (uniform matrix, ML-DSA verifier relation), not on the
standard `[I_m | A] · y` normal form; see *Tailored vs. standard SelfTargetMSIS* in
`LatticeCrypto.MLDSA.SecurityNMA`. The CMA-to-NMA engine of `FiatShamirWithAbort` runs its
adversaries over the two-oracle family `unifSpec + H`, so composing this ROM leg under an EUF-CMA
forger with `ExpandA` access needs that engine to forward a third oracle; the seed-model and
short-model CMA compositions in `SecurityNMA` keep their abstract MLWE bridge hypothesis instead.
-/

public section

open OracleComp OracleSpec ENNReal
open LatticeCrypto TransformOps

namespace MLDSA

section VerifyWithMatrix

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps] [DecidableEq prims.High]

/-- The ML-DSA identification verifier at an explicitly supplied public matrix `aHat`
(FIPS 204 Algorithm 8, lines 8–13): check `‖z‖∞ < γ₁ − β`, recover
`w'_Approx = Â·z − c·(t₁·2^d)` from `aHat`, and require `UseHint(h, w'_Approx) = w₁` and hint
weight `≤ ω`. `identificationScheme.verify` is this verifier at `aHat := ExpandA(pk.ρ)`
(`identificationScheme_verify_eq_verifyWithMatrix`); the `ExpandA` random-oracle verifier
`NMA.verifyRO` supplies `aHat` by an oracle query instead. -/
def verifyWithMatrix (aHat : TqMatrix p.k p.l) (pk : PublicKey p prims)
    (w1 : Commitment p prims) (cTilde : CommitHashBytes p) : Response p prims → Bool
  | (z, h) =>
    let c := prims.sampleInBall cTilde
    let wApprox := computeWApprox p prims aHat c z pk.t1
    let w1' := prims.useHintVec h wApprox
    decide (polyVecNorm z < p.gamma1 - p.beta) &&
    decide (w1' = w1) &&
    decide (prims.hintWeight h ≤ p.omega)

/-- The identification verifier evaluates `ExpandA` exactly once, at the public seed: it is
`verifyWithMatrix` at `ExpandA(pk.ρ)`. -/
theorem identificationScheme_verify_eq_verifyWithMatrix (pk : PublicKey p prims)
    (w1 : Commitment p prims) (cTilde : CommitHashBytes p) (zh : Response p prims) :
    (identificationScheme p prims).verify pk w1 cTilde zh =
      verifyWithMatrix p prims (prims.expandA pk.rho) pk w1 cTilde zh := by
  rcases zh with ⟨z, h⟩
  rfl

/-- The short-tagged scheme carries the same verifier (`identificationSchemeShort` re-uses the
operations of `identificationScheme`), so it too is `verifyWithMatrix` at `ExpandA(pk.ρ)`. -/
theorem identificationSchemeShort_verify_eq_verifyWithMatrix (pk : PublicKey p prims)
    (w1 : Commitment p prims) (cTilde : CommitHashBytes p) (zh : Response p prims) :
    (identificationSchemeShort p prims).verify pk w1 cTilde zh =
      verifyWithMatrix p prims (prims.expandA pk.rho) pk w1 cTilde zh :=
  identificationScheme_verify_eq_verifyWithMatrix p prims pk w1 cTilde zh

end VerifyWithMatrix

namespace NMA

variable (p : Params) (prims : Primitives p) [nttOps : NTTRingOps] [DecidableEq prims.High]

section KeyGenWith

/-- The idealized short key generator at an explicit matrix-expansion function `expandA`: sample
`ρ`, the signing key `K`, and the short secrets `(s₁, s₂)` independently — `(s₁, s₂)` uniform on
the `η`-bounded box — and form `t = expandA(ρ) · s₁ + s₂`. `keygenShort` is this generator at
`prims.expandA` (`keygenShort_eq_keygenShortWith`); the `ExpandA` random-oracle generator
`keygenShortRO` obtains the matrix by an oracle query instead. -/
@[expose] noncomputable def keygenShortWith (expandA : Bytes 32 → TqMatrix p.k p.l) :
    ProbComp (PublicKey p prims × SecretKey p) := do
  let key ← $ᵗ (Bytes 32)
  let rho ← $ᵗ (Bytes 32)
  let s1 ← sampleShortVec p.l p.eta
  let s2 ← sampleShortVec p.k p.eta
  let t := expandA rho * s1 + s2
  return keyFromMaterial p prims rho key s1 s2 t

omit [DecidableEq prims.High] in
/-- The short key generator evaluates `ExpandA` exactly once, at the sampled seed: it is
`keygenShortWith` at `prims.expandA`. -/
theorem keygenShort_eq_keygenShortWith :
    keygenShort p prims = keygenShortWith p prims prims.expandA := rfl

end KeyGenWith

section ExpandAOracle

variable {M : Type} [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (CommitHashBytes p)]

/-- The commitment-hash oracle `H : (msg, w₁) ↦ c̃` of the Fiat-Shamir-with-aborts signature. -/
abbrev HashSpec (M : Type) : OracleSpec (M × Commitment p prims) :=
  M × Commitment p prims →ₒ CommitHashBytes p

/-- The `ExpandA` oracle `ρ ↦ Â`. -/
abbrev ExpandASpec : OracleSpec (Bytes 32) := Bytes 32 →ₒ TqMatrix p.k p.l

/-- The oracle family of the `ExpandA` random-oracle model: uniform sampling, the commitment
hash `H`, and `ExpandA`. The nesting `unifSpec + (H + ExpandA)` keeps the two random oracles
together as the right summand. -/
abbrev RomSpec (M : Type) : OracleSpec (ℕ ⊕ ((M × Commitment p prims) ⊕ Bytes 32)) :=
  unifSpec + (HashSpec p prims M + ExpandASpec p)

/-! ### The honest algorithms at the oracle -/

/-- The idealized short key generator with `ExpandA` an oracle: `keygenShortWith` with the
matrix obtained by querying `ExpandA` at the sampled seed `ρ`. -/
noncomputable def keygenShortRO :
    OracleComp (RomSpec p prims M) (PublicKey p prims × SecretKey p) := do
  let key ← (liftM ($ᵗ (Bytes 32)) : OracleComp (RomSpec p prims M) _)
  let rho ← (liftM ($ᵗ (Bytes 32)) : OracleComp (RomSpec p prims M) _)
  let s1 ← (liftM (sampleShortVec p.l p.eta) : OracleComp (RomSpec p prims M) _)
  let s2 ← (liftM (sampleShortVec p.k p.eta) : OracleComp (RomSpec p prims M) _)
  let aHat ← HasQuery.query (spec := ExpandASpec p) rho
  return keyFromMaterial p prims rho key s1 s2 (aHat * s1 + s2)

/-- Fiat-Shamir-with-aborts verification of the ML-DSA signature with `ExpandA` an oracle: an
absent signature is rejected; on `some (w', z)` the challenge `c̃ = H(msg, w')` and the matrix
`Â = ExpandA(pk.ρ)` are both obtained by oracle queries and `verifyWithMatrix` decides. -/
def verifyRO (pk : PublicKey p prims) (msg : M)
    (σ : Option (Commitment p prims × Response p prims)) :
    OracleComp (RomSpec p prims M) Bool :=
  match σ with
  | none => pure false
  | some (w', z) => do
    let c ← HasQuery.query (spec := HashSpec p prims M) (msg, w')
    let aHat ← HasQuery.query (spec := ExpandASpec p) pk.rho
    pure (verifyWithMatrix p prims aHat pk w' c z)

/-- Fiat-Shamir-with-aborts verification at an explicit matrix `aHat`, in the two-oracle world of
the signature: the challenge is queried from `H` and `verifyWithMatrix` decides. At
`aHat := ExpandA(pk.ρ)` this is the signature's own `verify` (`verifyAtMatrix_expandA`); the
reductions use it at the matrix they programmed. -/
def verifyAtMatrix (aHat : TqMatrix p.k p.l) (pk : PublicKey p prims) (msg : M)
    (σ : Option (Commitment p prims × Response p prims)) :
    OracleComp (unifSpec + HashSpec p prims M) Bool :=
  match σ with
  | none => pure false
  | some (w', z) => do
    let c ← HasQuery.query (spec := HashSpec p prims M) (msg, w')
    pure (verifyWithMatrix p prims aHat pk w' c z)

omit [DecidableEq M] [DecidableEq (Commitment p prims)] [SampleableType (CommitHashBytes p)] in
/-- At the honest matrix `ExpandA(pk.ρ)`, `verifyAtMatrix` is the verification algorithm of the
short-model ML-DSA signature `FiatShamirWithAbort (identificationSchemeShort …)`. -/
theorem verifyAtMatrix_expandA
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ) (pk : PublicKey p prims) (msg : M)
    (σ : Option (Commitment p prims × Response p prims)) :
    verifyAtMatrix p prims (prims.expandA pk.rho) pk msg σ =
      (FiatShamirWithAbort (m := OracleComp (unifSpec + HashSpec p prims M))
        (identificationSchemeShort p prims) hr M maxAttempts).verify pk msg σ := by
  rcases σ with _ | ⟨w', z, h⟩ <;> rfl

/-! ### Pinning the oracle algorithms to the scheme

Answering every `ExpandA` query from a fixed table `f` (and forwarding the other two oracles)
turns the oracle algorithms back into the scheme's algorithms at `f`. -/

/-- Answer `ExpandA` queries from the fixed table `f`; forward uniform and `H` queries. -/
def tableImpl (f : Bytes 32 → TqMatrix p.k p.l) :
    QueryImpl (RomSpec p prims M) (OracleComp (unifSpec + HashSpec p prims M)) :=
  QueryImpl.ofLift unifSpec (OracleComp (unifSpec + HashSpec p prims M)) +
    (QueryImpl.ofLift (HashSpec p prims M) (OracleComp (unifSpec + HashSpec p prims M)) +
      (fun rho => (pure (f rho) : OracleComp (unifSpec + HashSpec p prims M) _) :
        QueryImpl (ExpandASpec p) (OracleComp (unifSpec + HashSpec p prims M))))

omit [DecidableEq prims.High] [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (CommitHashBytes p)] in
/-- With `ExpandA` answered by the table `f`, the oracle key generator is the short key
generator at `f`. -/
theorem simulateQ_tableImpl_keygenShortRO (f : Bytes 32 → TqMatrix p.k p.l) :
    simulateQ (tableImpl p prims (M := M) f) (keygenShortRO p prims (M := M)) =
      liftM (keygenShortWith p prims f) := by
  simp [keygenShortRO, keygenShortWith, tableImpl, QueryImpl.simulateQ_add_liftM_left]
  rfl

omit [DecidableEq M] [DecidableEq (Commitment p prims)] [SampleableType (CommitHashBytes p)] in
/-- With `ExpandA` answered by the table `f`, the oracle verifier is verification at the matrix
`f pk.ρ`. -/
theorem simulateQ_tableImpl_verifyRO (f : Bytes 32 → TqMatrix p.k p.l) (pk : PublicKey p prims)
    (msg : M) (σ : Option (Commitment p prims × Response p prims)) :
    simulateQ (tableImpl p prims (M := M) f) (verifyRO p prims pk msg σ) =
      verifyAtMatrix p prims (f pk.rho) pk msg σ := by
  rcases σ with _ | ⟨w', z⟩ <;> simp [verifyRO, verifyAtMatrix, tableImpl]

omit [DecidableEq prims.High] [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (CommitHashBytes p)] in
/-- **The oracle model degenerates to the scheme.** Answering `ExpandA` queries from the
scheme's own `prims.expandA` turns the oracle key generator into `keygenShort`, the key
generator of the short-model security statements. -/
theorem simulateQ_tableImpl_expandA_keygenShortRO :
    simulateQ (tableImpl p prims (M := M) prims.expandA) (keygenShortRO p prims (M := M)) =
      liftM (keygenShort p prims) := by
  rw [simulateQ_tableImpl_keygenShortRO, keygenShort_eq_keygenShortWith]

omit [DecidableEq M] [DecidableEq (Commitment p prims)] [SampleableType (CommitHashBytes p)] in
/-- **The oracle model degenerates to the scheme.** Answering `ExpandA` queries from the
scheme's own `prims.expandA` turns the oracle verifier into the verification algorithm of the
short-model ML-DSA signature. -/
theorem simulateQ_tableImpl_expandA_verifyRO
    (hr : GenerableRelation (PublicKey p prims) (SecretKey p) (validKeyPairShort p prims))
    (maxAttempts : ℕ) (pk : PublicKey p prims) (msg : M)
    (σ : Option (Commitment p prims × Response p prims)) :
    simulateQ (tableImpl p prims (M := M) prims.expandA) (verifyRO p prims pk msg σ) =
      (FiatShamirWithAbort (m := OracleComp (unifSpec + HashSpec p prims M))
        (identificationSchemeShort p prims) hr M maxAttempts).verify pk msg σ := by
  rw [simulateQ_tableImpl_verifyRO, verifyAtMatrix_expandA]

/-! ### The lazy, programmable `ExpandA` simulator -/

/-- Fresh uniform matrices as `ExpandA` answers, in the two-oracle world of the signature. -/
noncomputable def expandALazy :
    QueryImpl (ExpandASpec p) (OracleComp (unifSpec + HashSpec p prims M)) :=
  fun _ => liftM ($ᵗ (TqMatrix p.k p.l))

/-- The `ExpandA` random-oracle simulator: uniform and `H` queries are forwarded to the
two-oracle world of the signature, and `ExpandA` queries are answered lazily — a cached seed is
answered from the cache, a fresh seed receives a fresh uniform matrix that is then cached. The
cache is the simulator's state, so seeding it programs the oracle. -/
noncomputable def expandARoImpl :
    QueryImpl (RomSpec p prims M)
      (StateT (ExpandASpec p).QueryCache (OracleComp (unifSpec + HashSpec p prims M))) :=
  (QueryImpl.ofLift unifSpec (OracleComp (unifSpec + HashSpec p prims M))).liftTarget
      (StateT (ExpandASpec p).QueryCache (OracleComp (unifSpec + HashSpec p prims M))) +
  ((QueryImpl.ofLift (HashSpec p prims M) (OracleComp (unifSpec + HashSpec p prims M))).liftTarget
      (StateT (ExpandASpec p).QueryCache (OracleComp (unifSpec + HashSpec p prims M))) +
    (expandALazy p prims (M := M)).withCaching)

/-- Run a three-oracle computation with `ExpandA` simulated lazily from the cache `c`, discarding
the final cache. The result lives in the two-oracle world of the signature. -/
noncomputable def withExpandACache {α : Type} (c : (ExpandASpec p).QueryCache)
    (mx : OracleComp (RomSpec p prims M) α) : OracleComp (unifSpec + HashSpec p prims M) α :=
  (simulateQ (expandARoImpl p prims (M := M)) mx).run' c

/-- The programmed cache `{ρ ↦ aHat}`: the state of the `ExpandA` simulator after the reduction
has embedded its challenge matrix at the seed it chose. -/
def programmedAt (rho : Bytes 32) (aHat : TqMatrix p.k p.l) : (ExpandASpec p).QueryCache :=
  (∅ : (ExpandASpec p).QueryCache).cacheQuery rho aHat

omit nttOps [SampleableType (CommitHashBytes p)] in
@[simp] lemma programmedAt_self (rho : Bytes 32) (aHat : TqMatrix p.k p.l) :
    programmedAt p rho aHat rho = some aHat :=
  QueryCache.cacheQuery_self (∅ : (ExpandASpec p).QueryCache) rho aHat

/-! #### Running the simulator, one step at a time -/

omit nttOps [DecidableEq prims.High] [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (CommitHashBytes p)] in
/-- A lifted `ProbComp` passes through the simulator untouched, leaving the cache unchanged. -/
lemma expandARoImpl_run_liftM_bind {α β : Type} (oa : ProbComp α)
    (k : α → OracleComp (RomSpec p prims M) β) (c : (ExpandASpec p).QueryCache) :
    (simulateQ (expandARoImpl p prims (M := M)) (liftM oa >>= k)).run c =
      (liftM oa : OracleComp (unifSpec + HashSpec p prims M) α) >>= fun x =>
        (simulateQ (expandARoImpl p prims (M := M)) (k x)).run c := by
  simp only [simulateQ_bind, StateT.run_bind, expandARoImpl, QueryImpl.simulateQ_add_liftM_left,
    simulateQ_liftTarget, OracleComp.liftM_run_StateT, bind_assoc, pure_bind]
  rfl

omit nttOps [DecidableEq prims.High] [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (CommitHashBytes p)] in
/-- An `H` query is forwarded, leaving the cache unchanged. -/
lemma expandARoImpl_run_queryHash_bind {β : Type} (q : M × Commitment p prims)
    (k : CommitHashBytes p → OracleComp (RomSpec p prims M) β) (c : (ExpandASpec p).QueryCache) :
    (simulateQ (expandARoImpl p prims (M := M))
      (HasQuery.query (spec := HashSpec p prims M) q >>= k)).run c =
      HasQuery.query (spec := HashSpec p prims M) q >>= fun u =>
        (simulateQ (expandARoImpl p prims (M := M)) (k u)).run c := by
  simp [simulateQ_bind, StateT.run_bind, expandARoImpl]

omit nttOps [DecidableEq prims.High] [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (CommitHashBytes p)] in
/-- An `ExpandA` query at a cached seed is answered from the cache. -/
lemma expandARoImpl_run_queryExpandA_bind_some {β : Type} (rho : Bytes 32)
    (k : TqMatrix p.k p.l → OracleComp (RomSpec p prims M) β) {c : (ExpandASpec p).QueryCache}
    {aHat : TqMatrix p.k p.l} (hc : c rho = some aHat) :
    (simulateQ (expandARoImpl p prims (M := M))
      (HasQuery.query (spec := ExpandASpec p) rho >>= k)).run c =
      (simulateQ (expandARoImpl p prims (M := M)) (k aHat)).run c := by
  simp [simulateQ_bind, StateT.run_bind, expandARoImpl, hc]

omit nttOps [DecidableEq prims.High] [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (CommitHashBytes p)] in
/-- An `ExpandA` query at a fresh seed receives a fresh uniform matrix, which is cached. -/
lemma expandARoImpl_run_queryExpandA_bind_none {β : Type} (rho : Bytes 32)
    (k : TqMatrix p.k p.l → OracleComp (RomSpec p prims M) β) {c : (ExpandASpec p).QueryCache}
    (hc : c rho = none) :
    (simulateQ (expandARoImpl p prims (M := M))
      (HasQuery.query (spec := ExpandASpec p) rho >>= k)).run c =
      (liftM ($ᵗ (TqMatrix p.k p.l)) : OracleComp (unifSpec + HashSpec p prims M) _) >>=
        fun aHat => (simulateQ (expandARoImpl p prims (M := M)) (k aHat)).run
          (c.cacheQuery rho aHat) := by
  simp [simulateQ_bind, StateT.run_bind, expandARoImpl, expandALazy, hc]

omit nttOps [DecidableEq prims.High] [DecidableEq M] [DecidableEq (Commitment p prims)]
  [SampleableType (CommitHashBytes p)] in
/-- The simulator's cache only grows: every reachable final cache extends the initial one. -/
lemma le_of_mem_support_expandARoImpl_run {α : Type} (mx : OracleComp (RomSpec p prims M) α)
    (c : (ExpandASpec p).QueryCache) :
    ∀ z ∈ support ((simulateQ (expandARoImpl p prims (M := M)) mx).run c), c ≤ z.2 := by
  induction mx using OracleComp.inductionOn generalizing c with
  | pure a =>
    intro z hz
    simp_all
  | query_bind t oa ih =>
    intro z hz
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind] at hz
    rcases (mem_support_bind_iff _ _ _).1 hz with ⟨us, hus, hzcont⟩
    refine le_trans ?_ (ih us.1 us.2 z hzcont)
    rcases t with n | q | rho
    · simp only [expandARoImpl, QueryImpl.add_apply_inl, QueryImpl.liftTarget_apply,
        QueryImpl.ofLift_apply, OracleComp.liftM_run_StateT, support_bind, support_pure,
        Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hus
      obtain ⟨_, -, rfl⟩ := hus
      exact le_rfl
    · simp only [expandARoImpl, QueryImpl.add_apply_inr, QueryImpl.add_apply_inl,
        QueryImpl.liftTarget_apply, QueryImpl.ofLift_apply, OracleComp.liftM_run_StateT,
        support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff, exists_prop] at hus
      obtain ⟨_, -, rfl⟩ := hus
      exact le_rfl
    · exact QueryImpl.withCaching_cache_le (expandALazy p prims (M := M)) rho c us hus

omit [DecidableEq M] [DecidableEq (Commitment p prims)] [SampleableType (CommitHashBytes p)] in
/-- Under a cache that already holds `pk.ρ ↦ aHat`, the oracle verifier is verification at
`aHat`: its `ExpandA` query is answered from the cache. -/
lemma withExpandACache_verifyRO_of_cached (pk : PublicKey p prims) (msg : M)
    (σ : Option (Commitment p prims × Response p prims)) {c : (ExpandASpec p).QueryCache}
    {aHat : TqMatrix p.k p.l} (hc : c pk.rho = some aHat) :
    withExpandACache p prims c (verifyRO p prims pk msg σ) =
      verifyAtMatrix p prims aHat pk msg σ := by
  rcases σ with _ | ⟨w', z⟩
  · simp [withExpandACache, verifyRO, verifyAtMatrix]
  · simp only [withExpandACache, verifyRO, verifyAtMatrix, StateT.run'_eq,
      expandARoImpl_run_queryHash_bind, expandARoImpl_run_queryExpandA_bind_some p prims _ _ hc,
      simulateQ_pure, StateT.run_pure, map_bind, map_pure]

/-! ### The random-oracle EUF-NMA game -/

/-- The EUF-NMA game of the short-model ML-DSA signature in the `ExpandA` random-oracle model,
over a forging strategy `main` with access to all three oracles: generate a key through
`keygenShortRO`, run `main` on the public key, verify the returned forgery through `verifyRO`.
`ExpandA` is simulated lazily from the empty cache and shared by all three phases; `H` and
uniform sampling are then observed through the signature's own runtime (`simulateToProbComp`).
The game outputs the validity bit. -/
noncomputable def romNmaGame
    (main : PublicKey p prims → OracleComp (RomSpec p prims M)
      (M × Option (Commitment p prims × Response p prims))) : ProbComp Bool :=
  simulateToProbComp p prims (M := M) (withExpandACache p prims ∅ (do
    let (pk, _) ← keygenShortRO p prims (M := M)
    let (msg, σ) ← main pk
    verifyRO p prims pk msg σ))

/-- The EUF-NMA advantage in the `ExpandA` random-oracle model: the `true`-probability of
`romNmaGame`. -/
noncomputable def romNmaAdvantage
    (main : PublicKey p prims → OracleComp (RomSpec p prims M)
      (M × Option (Commitment p prims × Response p prims))) : ℝ≥0∞ :=
  Pr[= true | romNmaGame p prims main]

/-! ### The reductions -/

/-- **The uniform-matrix MLWE distinguisher.** Given a challenge `(Â, t)` from
`mldsaMatrixMLWE` (real `Â·s₁ + s₂` versus uniform `t`), `B` samples the seed `ρ` itself, forms
the public key `pk = (ρ, Power2Round(t).1)`, runs the forger with `ExpandA` simulated from the
programmed cache `{ρ ↦ Â}` — so the forger sees `ExpandA(ρ) = Â` and fresh uniform matrices
elsewhere, exactly as in the honest game — verifies the forgery at the matrix `Â` through the
signature's runtime, and outputs the validity bit. -/
noncomputable def distinguisherBRom
    (main : PublicKey p prims → OracleComp (RomSpec p prims M)
      (M × Option (Commitment p prims × Response p prims))) :
    LearningWithErrors.Adversary (mldsaMatrixMLWE p) :=
  fun (challenge : TqMatrix p.k p.l × RqVec p.k) => do
    let rho ← $ᵗ (Bytes 32)
    let pk : PublicKey p prims := ⟨rho, (prims.power2RoundVec challenge.2).1⟩
    simulateToProbComp p prims (M := M) (do
      let (msg, σ) ← withExpandACache p prims (programmedAt p rho challenge.1) (main pk)
      verifyAtMatrix p prims challenge.1 pk msg σ)

/-- **The uniform-matrix tailored SelfTargetMSIS problem.** The parameters are a uniform matrix
`Â` and a public key `pk = (ρ, Power2Round(t).1)` with uniform `ρ` and uniform `t` — the
uniform-`t` key of the short model with the matrix supplied independently of the seed, as the
`ExpandA` random-oracle model prescribes. Validity is the ML-DSA verifier relation at the
challenge matrix: recover `w' = UseHint(h, Â·z − SampleInBall(c̃)·(t₁·2^d))`, bind it to the
commitment component of the hashed preimage (the self-target binding), and run
`verifyWithMatrix` at `Â`. At `Â = ExpandA(pk.ρ)` this validity predicate is that of the
seed-based `mldsaSTMSISShort` (`mldsaSTMSISShort_isValid_expandA_eq_matrix`). Like
`mldsaSTMSISShort` it is the tailored verifier relation, not the standard SelfTargetMSIS normal
form. -/
noncomputable def mldsaSTMSISMatrix (M : Type) :
    SelfTargetMSIS.Problem (TqMatrix p.k p.l) (Response p prims) (PublicKey p prims)
      (M × Commitment p prims) (CommitHashBytes p) where
  sampleParams := do
    let aHat ← $ᵗ (TqMatrix p.k p.l)
    let t ← $ᵗ (RqVec p.k)
    let rho ← $ᵗ (Bytes 32)
    return (aHat, ⟨rho, (prims.power2RoundVec t).1⟩)
  isValid := fun aHat pk hashInput cTilde (z, h) =>
    let w' := prims.useHintVec h (computeWApprox p prims aHat (prims.sampleInBall cTilde) z pk.t1)
    decide (hashInput.2 = w') && verifyWithMatrix p prims aHat pk w' cTilde (z, h)

omit [DecidableEq M] [SampleableType (CommitHashBytes p)] in
/-- At the honest matrix `ExpandA(pk.ρ)`, the seed-based tailored problem and the uniform-matrix
tailored problem accept the same solutions. -/
theorem mldsaSTMSISShort_isValid_expandA_eq_matrix (pk : PublicKey p prims)
    (hashInput : M × Commitment p prims) (cTilde : CommitHashBytes p) (zh : Response p prims) :
    (mldsaSTMSISShort p prims M).isValid (prims.expandA pk.rho) pk hashInput cTilde zh =
      (mldsaSTMSISMatrix p prims M).isValid (prims.expandA pk.rho) pk hashInput cTilde zh := by
  rcases zh with ⟨z, h⟩
  rfl

/-- **The uniform-matrix SelfTargetMSIS extractor.** On parameters `(Â, pk)` it runs the forger
with `ExpandA` simulated from the programmed cache `{pk.ρ ↦ Â}`, forwarding `H` queries to the
experiment's random oracle, and performs the forger-to-preimage extraction of `extractorC`: on a
forgery `(msg, some (w', (z, h)))` it forces the `H(msg, w')` query and outputs the preimage
`(msg, w')` with the response `(z, h)`. -/
noncomputable def extractorCRom [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (main : PublicKey p prims → OracleComp (RomSpec p prims M)
      (M × Option (Commitment p prims × Response p prims))) :
    SelfTargetMSIS.Adversary (mldsaSTMSISMatrix p prims M) :=
  ⟨fun params => (extractorC p prims (fun pk =>
    withExpandACache p prims (programmedAt p pk.rho params.1) (main pk))).run params⟩

/-! ### The hops -/

omit nttOps [DecidableEq prims.High] in
/-- Pushing a lifted `ProbComp` out of the signature's runtime. -/
lemma simulateToProbComp_liftM_bind {α β : Type} (oa : ProbComp α)
    (k : α → OracleComp (unifSpec + HashSpec p prims M) β) :
    simulateToProbComp p prims (M := M) (liftM oa >>= k) =
      oa >>= fun x => simulateToProbComp p prims (M := M) (k x) := by
  simp only [simulateToProbComp, roImpl, simulateQ_bind]
  exact roSim.run'_liftM_bind _ oa _ ∅

/-- **Verification reads the programmed matrix.** Once the forger has run from the programmed
cache `{pk.ρ ↦ aHat}`, the oracle verifier's `ExpandA` query is answered by `aHat` — the cache
only grows — so verifying through the shared oracle is verifying at `aHat`. -/
lemma probOutput_verifyRO_eq_verifyAtMatrix
    (main : PublicKey p prims → OracleComp (RomSpec p prims M)
      (M × Option (Commitment p prims × Response p prims)))
    (pk : PublicKey p prims) (aHat : TqMatrix p.k p.l) :
    Pr[= true | simulateToProbComp p prims (M := M) (withExpandACache p prims
        (programmedAt p pk.rho aHat) (do
          let (msg, σ) ← main pk
          verifyRO p prims pk msg σ))] =
      Pr[= true | simulateToProbComp p prims (M := M) (do
          let (msg, σ) ← withExpandACache p prims (programmedAt p pk.rho aHat) (main pk)
          verifyAtMatrix p prims aHat pk msg σ)] := by
  -- Both sides bind over the forger's run from the programmed cache; compare per reachable
  -- forgery-and-cache pair.
  have hsplit : withExpandACache p prims (programmedAt p pk.rho aHat) (do
        let (msg, σ) ← main pk
        verifyRO p prims pk msg σ) =
      (simulateQ (expandARoImpl p prims (M := M)) (main pk)).run (programmedAt p pk.rho aHat) >>=
        fun z => withExpandACache p prims z.2 (verifyRO p prims pk z.1.1 z.1.2) := by
    simp only [withExpandACache, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  have hsplit' : (do
        let (msg, σ) ← withExpandACache p prims (programmedAt p pk.rho aHat) (main pk)
        verifyAtMatrix p prims aHat pk msg σ) =
      (simulateQ (expandARoImpl p prims (M := M)) (main pk)).run (programmedAt p pk.rho aHat) >>=
        fun z => verifyAtMatrix p prims aHat pk z.1.1 z.1.2 := by
    simp only [withExpandACache, StateT.run'_eq, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_def]
  rw [hsplit, hsplit']
  simp only [simulateToProbComp, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  refine probOutput_bind_congr fun w hw => ?_
  have hw1 : w.1 ∈ support ((simulateQ (expandARoImpl p prims (M := M)) (main pk)).run
      (programmedAt p pk.rho aHat)) := by
    refine support_simulateQ_run'_subset (n := ProbComp) (roImpl p prims (M := M)) _
      (∅ : (M × Commitment p prims →ₒ CommitHashBytes p).QueryCache) ?_
    rw [StateT.run'_eq, support_map]
    exact ⟨w, hw, rfl⟩
  have hc : w.1.2 pk.rho = some aHat :=
    le_of_mem_support_expandARoImpl_run p prims (main pk) _ w.1 hw1
      (programmedAt_self p pk.rho aHat)
  rw [withExpandACache_verifyRO_of_cached p prims pk w.1.1.1 w.1.1.2 hc]

/-- **The ROM game is the real MLWE branch.** The `ExpandA` random-oracle EUF-NMA game equals
the real branch of the uniform-matrix Module-LWE game against `distinguisherBRom`, exactly: the
honest key generator's first `ExpandA` query at the fresh seed `ρ` draws a uniform matrix and
caches it, which is the programmed cache `{ρ ↦ Â}` at the challenger's uniform `Â`; the key
`t = Â·s₁ + s₂` is the real MLWE sample; and verification through the shared oracle is
verification at `Â` (`probOutput_verifyRO_eq_verifyAtMatrix`). -/
theorem romNmaAdvantage_eq_game0
    (main : PublicKey p prims → OracleComp (RomSpec p prims M)
      (M × Option (Commitment p prims × Response p prims))) :
    romNmaAdvantage p prims main =
      Pr[= true | LearningWithErrors.game0 (mldsaMatrixMLWE p)
        (distinguisherBRom p prims main)] := by
  -- The honest key generation under the simulator: four samplers pass through, and the single
  -- `ExpandA` query at the fresh seed draws the matrix and programs the cache at `ρ`.
  have hkey : ∀ K : PublicKey p prims × SecretKey p → OracleComp (RomSpec p prims M) Bool,
      withExpandACache p prims ∅ (keygenShortRO p prims (M := M) >>= K) = (do
        let key ← (liftM ($ᵗ (Bytes 32)) : OracleComp (unifSpec + HashSpec p prims M) _)
        let rho ← (liftM ($ᵗ (Bytes 32)) : OracleComp (unifSpec + HashSpec p prims M) _)
        let s1 ← (liftM (sampleShortVec p.l p.eta) : OracleComp (unifSpec + HashSpec p prims M) _)
        let s2 ← (liftM (sampleShortVec p.k p.eta) : OracleComp (unifSpec + HashSpec p prims M) _)
        let aHat ← (liftM ($ᵗ (TqMatrix p.k p.l)) : OracleComp (unifSpec + HashSpec p prims M) _)
        withExpandACache p prims (programmedAt p rho aHat)
          (K (keyFromMaterial p prims rho key s1 s2 (aHat * s1 + s2)))) := by
    intro K
    simp only [withExpandACache, keygenShortRO, bind_assoc, StateT.run'_eq,
      expandARoImpl_run_liftM_bind, map_bind, programmedAt]
    simp only [expandARoImpl_run_queryExpandA_bind_none p prims _ _ (QueryCache.empty_apply _),
      pure_bind, map_bind]
  rw [romNmaAdvantage, romNmaGame, hkey]
  simp only [simulateToProbComp_liftM_bind, LearningWithErrors.game0, LearningWithErrors.distr,
    mldsaMatrixMLWE, distinguisherBRom, bind_assoc, pure_bind, keyFromMaterial]
  -- Strip the unused signing-key draw, then align the draw orders: `ρ` moves inward past
  -- `s₁`, `s₂`, `Â` on the game side and `Â` moves inward past `s₁`, `s₂` on the MLWE side.
  rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
  rw [probOutput_bind_bind_swap ($ᵗ (Bytes 32)) (sampleShortVec p.l p.eta),
    probOutput_bind_bind_swap ($ᵗ (TqMatrix p.k p.l)) (sampleShortVec p.l p.eta)]
  refine probOutput_bind_congr' _ true fun s1 => ?_
  rw [probOutput_bind_bind_swap ($ᵗ (Bytes 32)) (sampleShortVec p.k p.eta),
    probOutput_bind_bind_swap ($ᵗ (TqMatrix p.k p.l)) (sampleShortVec p.k p.eta)]
  refine probOutput_bind_congr' _ true fun s2 => ?_
  rw [probOutput_bind_bind_swap ($ᵗ (Bytes 32)) ($ᵗ (TqMatrix p.k p.l))]
  refine probOutput_bind_congr' _ true fun aHat => ?_
  refine probOutput_bind_congr' _ true fun rho => ?_
  exact probOutput_verifyRO_eq_verifyAtMatrix p prims main
    ⟨rho, (prims.power2RoundVec (aHat * s1 + s2)).1⟩ aHat

/-- **Per-key STMSIS read-back comparison at an explicit matrix.** For a fixed public key `pk`
and matrix `aHat`, the forge-and-verify tail at `aHat` (run through `simulateToProbComp`) accepts
no more often than the SelfTargetMSIS experiment tail of `extractorC` at the parameters
`(aHat, pk)` with `mldsaSTMSISMatrix` validity. Both tails simulate `main pk` against the same
random oracle from the empty cache; an aborting forgery contributes weight `0`; on
`some (w', (z, h))` both branches issue the same `H(msg, w')` query, whose cached answer the
STMSIS experiment reads back before `isValid` recovers the commitment, binds it to the preimage
component `w'`, and runs the identical verifier at `aHat`. -/
private theorem stmsis_tail_le_matrix
    [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (aHat : TqMatrix p.k p.l)
    (main : PublicKey p prims →
      OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p))
        (M × Option (Commitment p prims × Response p prims)))
    (pk : PublicKey p prims) :
    Pr[= true | simulateToProbComp p prims (M := M) (do
        let (msg, σ) ← main pk
        verifyAtMatrix p prims aHat pk msg σ)] ≤
      Pr[= true | do
        let ((hashInput, response), cache) ←
          (simulateQ (roImpl p prims (M := M))
            ((extractorC p prims main).run (aHat, pk))).run ∅
        match cache hashInput with
        | some hashOutput =>
            pure ((mldsaSTMSISMatrix p prims M).isValid aHat pk hashInput hashOutput response)
        | none => pure false] := by
  classical
  -- Decompose both tails over the shared simulation of `main pk` from the empty cache.
  unfold simulateToProbComp extractorC
  simp only [bind_pure_comp, simulateQ_bind, StateT.run_bind, StateT.run'_eq, map_bind,
    bind_assoc]
  refine probOutput_bind_mono fun a _ => ?_
  obtain ⟨⟨msg, σ⟩, cache0⟩ := a
  cases σ with
  | none =>
    -- Aborting forgery: the verify tail is deterministically `false`, so it has weight `0`.
    simp only [verifyAtMatrix, simulateQ_pure, StateT.run_pure, map_pure, probOutput_pure]
    simp
  | some wzh =>
    obtain ⟨w', z, h⟩ := wzh
    -- Both branches issue the same `H(msg, w')` query on `cache0`; compare per random answer.
    simp only [verifyAtMatrix, simulateQ_map, StateT.run_map, bind_pure_comp]
    simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc]
    refine probOutput_bind_mono fun cc hcc => ?_
    simp only [pure_bind]
    -- The query simulation caches its answer: `cc.2 (msg, w') = some cc.1`.
    have hquery : simulateQ (roImpl p prims (M := M)) (query (msg, w') :
          OracleComp (unifSpec + (M × Commitment p prims →ₒ CommitHashBytes p)) _) =
        (randomOracle : QueryImpl (M × Commitment p prims →ₒ CommitHashBytes p) _) (msg, w') :=
      roSim.simulateQ_liftM_spec_query _ _
    rw [hquery] at hcc
    have hcache : cc.2 (msg, w') = some cc.1 := by
      cases hc0 : cache0 (msg, w') with
      | some u =>
        rw [randomOracle, QueryImpl.withCaching_run_some _ hc0, support_pure,
          Set.mem_singleton_iff] at hcc
        subst hcc; exact hc0
      | none =>
        rw [randomOracle, QueryImpl.withCaching_run_none _ hc0, support_map] at hcc
        obtain ⟨u, _, hu⟩ := hcc
        subst hu
        exact QueryCache.cacheQuery_self _ (msg, w') u
    rw [hcache]
    -- An accepted forgery is a valid solution: the verifier's middle conjunct identifies the
    -- recomputed commitment with `w'`, which is the commitment component of the preimage.
    rw [probOutput_pure, probOutput_pure]
    by_cases hverify : verifyWithMatrix p prims aHat pk w' cc.1 (z, h) = true
    · have hvalid :
          (mldsaSTMSISMatrix p prims M).isValid aHat pk (msg, w') cc.1 (z, h) = true := by
        simp only [mldsaSTMSISMatrix, verifyWithMatrix] at hverify ⊢
        revert hverify
        grind
      rw [if_pos hverify.symm, if_pos hvalid.symm]
    · simp only [Bool.not_eq_true] at hverify
      rw [hverify]
      simp

/-- **The uniform MLWE branch is bounded by SelfTargetMSIS.** The uniform branch of the
uniform-matrix Module-LWE game against `distinguisherBRom` — a uniform matrix, a uniform `t`, a
self-chosen seed — is the parameter distribution of `mldsaSTMSISMatrix`, and per parameter the
forge-and-verify tail at the challenge matrix accepts no more often than the extractor's
read-back tail (`stmsis_tail_le_matrix`). -/
theorem game1_le_stmsis_rom [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (main : PublicKey p prims → OracleComp (RomSpec p prims M)
      (M × Option (Commitment p prims × Response p prims))) :
    Pr[= true | LearningWithErrors.game1 (mldsaMatrixMLWE p) (distinguisherBRom p prims main)] ≤
      SelfTargetMSIS.advantage (extractorCRom p prims main) := by
  classical
  rw [SelfTargetMSIS.advantage, SelfTargetMSIS.experiment]
  simp only [LearningWithErrors.game1, LearningWithErrors.uniformDistr, mldsaMatrixMLWE,
    distinguisherBRom, extractorCRom, mldsaSTMSISMatrix, bind_assoc, pure_bind]
  refine probOutput_bind_mono fun aHat _ => ?_
  refine probOutput_bind_mono fun t _ => ?_
  refine probOutput_bind_mono fun rho _ => ?_
  convert stmsis_tail_le_matrix p prims aHat
    (fun pk => withExpandACache p prims (programmedAt p pk.rho aHat) (main pk))
    ⟨rho, (prims.power2RoundVec t).1⟩ using 2
  rw [roImpl, unifFwdImpl]
  refine bind_congr fun x => ?_
  obtain ⟨⟨hashInput, response⟩, cache⟩ := x
  dsimp only
  cases cache hashInput <;> rfl

/-- **EUF-NMA security of short-model ML-DSA with `ExpandA` a programmed random oracle.**

For every forging strategy `main` with access to uniform sampling, the commitment hash `H`, and
the `ExpandA` oracle, there are a uniform-matrix Module-LWE adversary `B` (`distinguisherBRom`)
and a uniform-matrix tailored SelfTargetMSIS adversary `C` (`extractorCRom`) with

  `Adv^{EUF-NMA}_{ROM}(main) ≤ Adv^{MLWE}(B) + Adv^{SelfTargetMSIS}(C)`.

Both reductions program the `ExpandA` oracle at a self-chosen seed with the matrix received from
their challenger and simulate it lazily elsewhere; the forger's view is the honest game's. The
ROM game is exactly the real MLWE branch (`romNmaAdvantage_eq_game0`), the real branch is at
most the uniform branch plus the MLWE advantage, and the uniform branch is bounded by the
SelfTargetMSIS advantage (`game1_le_stmsis_rom`). There is no idealization slack and no
hypothesis beyond the forger; the hardness problems are the literature's uniform-matrix MLWE and
the tailored ML-DSA verifier relation at a uniform matrix. -/
theorem nma_security_rom [Inhabited (Commitment p prims)] [Inhabited (Response p prims)]
    (main : PublicKey p prims → OracleComp (RomSpec p prims M)
      (M × Option (Commitment p prims × Response p prims))) :
    ∃ (mlweReduction : LearningWithErrors.Adversary (mldsaMatrixMLWE p))
      (stmsisReduction : SelfTargetMSIS.Adversary (mldsaSTMSISMatrix p prims M)),
      romNmaAdvantage p prims main ≤
        ENNReal.ofReal (LearningWithErrors.advantage (mldsaMatrixMLWE p) mlweReduction) +
        SelfTargetMSIS.advantage stmsisReduction := by
  refine ⟨distinguisherBRom p prims main, extractorCRom p prims main, ?_⟩
  rw [romNmaAdvantage_eq_game0, advantage_eq_game_boolDistAdvantage]
  refine le_trans (ProbComp.probOutput_true_le_add_ofReal_boolDistAdvantage _
    (LearningWithErrors.game1 (mldsaMatrixMLWE p) (distinguisherBRom p prims main))) ?_
  rw [add_comm]
  exact add_le_add le_rfl (game1_le_stmsis_rom p prims main)

end ExpandAOracle

end NMA

end MLDSA
