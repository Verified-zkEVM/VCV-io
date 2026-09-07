/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Alexander Hicks
-/

module
public import HashSig.SLHDSA.GeneralSchemeQueryBound
public import HashSig.SLHDSA.Security.ReachableTargets
public import VCVio.OracleComp.QueryTracking.LoggingOracle

/-!
# Connecting SLH-DSA construction traces to reachable target ledgers

The construction-level public-hash syntax records the encoded address used by every `F`, `H`,
and `T_l` call.  This file packages the union of the six structural address ledgers and gives a
pathwise predicate saying that every public-hash query made by a free `OracleComp` program uses an
address from that union.  The predicate is structural: it quantifies over every possible oracle
answer and is therefore stronger than a statement about one deterministic execution.

`H_msg` has no address and is admitted separately.  Membership is deliberately stated after
`CorePrimitives.adrsToKey`: compressed SHA-2 encodings need not be globally injective.  The
distinct-target games can add the restricted injectivity hypotheses from `ReachableTargets`.

The programs certified here are the WOTS+ ones: `chainM`, `wotsPkGenM`, `wotsSignM`, and
`wotsPkFromSigM` at any reachable `LayerPosition`, each paired with its existing total query
budget.  The FORS, XMSS, hypertree, and scheme programs are not covered here and are left to the
next slice.  The logged-execution theorem then applies to any pathwise-certified program
interpreted through `QueryImpl.withLogging` over an arbitrary deterministic handler
`QueryImpl (publicHashSpec core) Id`, and in particular through the canonical `PublicHash.impl` of
a primitive bundle.

## References

- NIST FIPS 205, §4.1 (the tweakable-hash roles `F`, `H`, `T_l`, and `H_msg`), Algorithms 5--8
  (WOTS+ chain, public-key generation, signing, and public-key recovery)
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.Security

/-- All structural addresses that can be used by the public tweakable-hash collection. -/
def constructionAddresses (vp : ValidatedParams) : List Adrs :=
  forsLeafAddresses vp ++ forsTreeAddresses vp ++ forsRootAddresses vp ++
    wotsStepAddresses vp ++ wotsPkAddresses vp ++ xmssNodeAddresses vp

/-- The union ledger is duplicate-free: each role ledger is, and the roles are pairwise disjoint. -/
theorem constructionAddresses_nodup (vp : ValidatedParams) : (constructionAddresses vp).Nodup :=
  nodup_structuralLedgers_append vp

/-- The encoded image of the complete structural construction-address ledger. -/
def encodedConstructionAddresses (vp : ValidatedParams)
    (core : CorePrimitives vp.params) : List core.AdrsKey :=
  (constructionAddresses vp).map core.adrsToKey

/-- Over a primitive bundle's core, the encoded union ledger is `encodeTargets` of the union. -/
theorem encodedConstructionAddresses_core {vp : ValidatedParams} (prims : Primitives vp.params) :
    encodedConstructionAddresses vp prims.core =
      encodeTargets prims (constructionAddresses vp) := by
  simp only [encodedConstructionAddresses, encodeTargets]

/-- A public-hash query is construction-reachable when its encoded tweak occurs in the structural
ledger. `H_msg` carries no tweak and is always accepted by this address predicate. -/
def ConstructionQueryReachable (vp : ValidatedParams)
    (core : CorePrimitives vp.params) : (publicHashSpec core).Domain → Prop
  | .thash _ adrsKey _ => adrsKey ∈ encodedConstructionAddresses vp core
  | .hmsg _ _ _ _ => True

/-- Every syntactically reachable path through `program` uses only construction-ledger tweaks.
The unit budget does not count queries; it turns `IsQueryBound` into a pathwise query predicate. -/
def QueriesWithinConstructionTargets {vp : ValidatedParams}
    (core : CorePrimitives vp.params) {α : Type}
    (program : OracleComp (publicHashSpec core) α) : Prop :=
  program.IsQueryBound () (fun q _ => ConstructionQueryReachable vp core q) (fun _ _ => ())

@[simp]
theorem queriesWithinConstructionTargets_pure {vp : ValidatedParams}
    (core : CorePrimitives vp.params) {α : Type} (x : α) :
    QueriesWithinConstructionTargets core
      (pure x : OracleComp (publicHashSpec core) α) := by
  trivial

/-- Pathwise target provenance composes through monadic sequencing. -/
theorem QueriesWithinConstructionTargets.bind {vp : ValidatedParams}
    {core : CorePrimitives vp.params} {α β : Type}
    {program : OracleComp (publicHashSpec core) α}
    {continuation : α → OracleComp (publicHashSpec core) β}
    (hprogram : QueriesWithinConstructionTargets core program)
    (hcontinuation : ∀ x, QueriesWithinConstructionTargets core (continuation x)) :
    QueriesWithinConstructionTargets core (program >>= continuation) := by
  exact OracleComp.isQueryBound_bind (fun _ _ => ())
    (fun _ _ _ _ h => ⟨h, h⟩) (fun _ _ _ _ _ => ⟨rfl, rfl⟩)
    hprogram hcontinuation

/-- A single public-hash query is within the construction ledger exactly when its query input is. -/
@[simp]
theorem queriesWithinConstructionTargets_query_iff {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (q : (publicHashSpec core).Domain) :
    QueriesWithinConstructionTargets core
        (liftM ((publicHashSpec core).query q) :
          OracleComp (publicHashSpec core) ((publicHashSpec core).Range q)) ↔
      ConstructionQueryReachable vp core q := by
  simp [QueriesWithinConstructionTargets]

/-- Any structural address in the union ledger has a reachable encoded tweak. -/
theorem constructionQueryReachable_thash_of_mem {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (pkSeed : core.PkSeed) (adrs : Adrs)
    (xs : List core.Y) (hadrs : adrs ∈ constructionAddresses vp) :
    ConstructionQueryReachable vp core
      (.thash pkSeed (core.adrsToKey adrs) xs) := by
  simp only [ConstructionQueryReachable, encodedConstructionAddresses, List.mem_map]
  exact ⟨adrs, hadrs, rfl⟩

/-! ## Explicit query and WOTS trace bridges -/

/-- An explicit `F` call at any address in the structural union is pathwise certified. -/
theorem publicHash_f_queriesWithinConstructionTargets_of_mem {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (pkSeed : core.PkSeed) (adrs : Adrs) (x : core.Y)
    (hadrs : adrs ∈ constructionAddresses vp) :
    QueriesWithinConstructionTargets core
      (PublicHash.f core pkSeed adrs x : OracleComp (publicHashSpec core) core.Y) := by
  apply (queriesWithinConstructionTargets_query_iff core _).2
  exact constructionQueryReachable_thash_of_mem core pkSeed adrs [x] hadrs

/-- An explicit `H` call at any address in the structural union is pathwise certified. -/
theorem publicHash_h_queriesWithinConstructionTargets_of_mem {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (pkSeed : core.PkSeed) (adrs : Adrs)
    (left right : core.Y) (hadrs : adrs ∈ constructionAddresses vp) :
    QueriesWithinConstructionTargets core
      (PublicHash.h core pkSeed adrs left right :
        OracleComp (publicHashSpec core) core.Y) := by
  apply (queriesWithinConstructionTargets_query_iff core _).2
  exact constructionQueryReachable_thash_of_mem core pkSeed adrs [left, right] hadrs

/-- An explicit `T_l` call at any address in the structural union is pathwise certified. -/
theorem publicHash_tl_queriesWithinConstructionTargets_of_mem {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (pkSeed : core.PkSeed) (adrs : Adrs)
    (xs : List core.Y) (hadrs : adrs ∈ constructionAddresses vp) :
    QueriesWithinConstructionTargets core
      (PublicHash.tl core pkSeed adrs xs : OracleComp (publicHashSpec core) core.Y) := by
  apply (queriesWithinConstructionTargets_query_iff core _).2
  exact constructionQueryReachable_thash_of_mem core pkSeed adrs xs hadrs

/-- One typed WOTS chain step is an actual `F` query at an address in the WOTS-step ledger. -/
theorem publicHash_f_wotsStep_queriesWithinConstructionTargets {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (pkSeed : core.PkSeed) (pos : LayerPosition vp)
    (chain : Fin vp.params.len) (step : Fin (vp.params.w - 1)) (x : core.Y) :
    QueriesWithinConstructionTargets core
      (PublicHash.f core pkSeed (wotsStepAdrs (pos, chain) step) x :
        OracleComp (publicHashSpec core) core.Y) := by
  apply publicHash_f_queriesWithinConstructionTargets_of_mem core pkSeed _ x
  simp [constructionAddresses, mem_wotsStepAddresses]

/-- A typed WOTS public-key compression is an actual `T_l` query at an address in its ledger. -/
theorem publicHash_tl_wotsPk_queriesWithinConstructionTargets {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (pkSeed : core.PkSeed) (pos : LayerPosition vp)
    (xs : List core.Y) :
    QueriesWithinConstructionTargets core
      (PublicHash.tl core pkSeed (wotsPkAdrs (wotsInstanceAdrs pos)) xs :
        OracleComp (publicHashSpec core) core.Y) := by
  apply publicHash_tl_queriesWithinConstructionTargets_of_mem core pkSeed _ xs
  simp [constructionAddresses, mem_wotsPkAddresses]

/-- A WOTS chain whose interval stays in `[0, w - 1)` issues only queries in the complete
all-layer WOTS-step ledger. -/
theorem chainM_queriesWithinConstructionTargets {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (pkSeed : core.PkSeed) (pos : LayerPosition vp)
    (chain : Fin vp.params.len) (x : core.Y) (i s : ℕ) (hinterval : i + s ≤ vp.params.w - 1) :
    QueriesWithinConstructionTargets core
      (chainM core pkSeed (wotsChainAdrs (wotsInstanceAdrs pos) chain.val) x i s :
        OracleComp (publicHashSpec core) core.Y) := by
  induction s with
  | zero => trivial
  | succ s ih =>
      change QueriesWithinConstructionTargets core
        (chainM core pkSeed (wotsChainAdrs (wotsInstanceAdrs pos) chain.val) x i s >>= fun y =>
          PublicHash.f core pkSeed
            ((wotsChainAdrs (wotsInstanceAdrs pos) chain.val).setHashAddress (i + s)) y)
      apply QueriesWithinConstructionTargets.bind (ih (by omega))
      intro y
      have hstep : i + s < vp.params.w - 1 := by omega
      simpa [wotsStepAdrs] using
        publicHash_f_wotsStep_queriesWithinConstructionTargets core pkSeed pos chain
          ⟨i + s, hstep⟩ y

private theorem queriesWithinConstructionTargets_ofFnM {vp : ValidatedParams}
    (core : CorePrimitives vp.params) {Y : Type} {k : ℕ}
    (program : Fin k → OracleComp (publicHashSpec core) Y)
    (hprogram : ∀ i, QueriesWithinConstructionTargets core (program i)) :
    QueriesWithinConstructionTargets core (Vector.ofFnM program) := by
  induction k with
  | zero =>
      rw [Vector.ofFnM_zero]
      trivial
  | succ k ih =>
      rw [Vector.ofFnM_succ]
      apply QueriesWithinConstructionTargets.bind
        (ih (fun i => program i.castSucc) (fun i => hprogram i.castSucc))
      intro xs
      apply QueriesWithinConstructionTargets.bind (hprogram (Fin.last k))
      intro x
      trivial

/-- Actual WOTS public-key generation at a typed arbitrary-depth position stays inside the
WOTS-step and WOTS-compression ledgers. -/
theorem wotsPkGenM_queriesWithinConstructionTargets {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
      (wotsPkGenM core skSeed pkSeed (wotsInstanceAdrs pos) :
        OracleComp (publicHashSpec core) core.Y) := by
  apply QueriesWithinConstructionTargets.bind
    (queriesWithinConstructionTargets_ofFnM core
      (fun chain : Fin vp.params.len =>
        chainM core pkSeed (wotsChainAdrs (wotsInstanceAdrs pos) chain.val)
          (core.PRF pkSeed skSeed (wotsSkAdrs (wotsInstanceAdrs pos) chain.val))
          0 (vp.params.w - 1))
      (fun chain => chainM_queriesWithinConstructionTargets core pkSeed pos chain _ 0
        (vp.params.w - 1) (by omega)))
  intro tops
  exact publicHash_tl_wotsPk_queriesWithinConstructionTargets core pkSeed pos tops.toList

/-- Actual WOTS signing at a typed arbitrary-depth position stays inside the WOTS-step ledger. -/
theorem wotsSignM_queriesWithinConstructionTargets {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (msg : core.Y) (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
      (wotsSignM core msg skSeed pkSeed (wotsInstanceAdrs pos) :
        OracleComp (publicHashSpec core) (WotsSig vp.params core)) := by
  exact queriesWithinConstructionTargets_ofFnM core _ fun chain =>
    chainM_queriesWithinConstructionTargets core pkSeed pos chain _ 0
      (chainStepsCore core msg chain.val) (by
        simpa using chainStepsCore_le core msg chain.val)

/-- Actual WOTS recovery at a typed arbitrary-depth position stays inside the WOTS-step and
WOTS-compression ledgers. -/
theorem wotsPkFromSigM_queriesWithinConstructionTargets {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (sig : WotsSig vp.params core) (msg : core.Y)
    (pkSeed : core.PkSeed) (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
      (wotsPkFromSigM core sig msg pkSeed (wotsInstanceAdrs pos) :
        OracleComp (publicHashSpec core) core.Y) := by
  apply QueriesWithinConstructionTargets.bind
    (queriesWithinConstructionTargets_ofFnM core
      (fun chain : Fin vp.params.len =>
        chainM core pkSeed (wotsChainAdrs (wotsInstanceAdrs pos) chain.val) sig[chain.val]
          (chainStepsCore core msg chain.val)
          (vp.params.w - 1 - chainStepsCore core msg chain.val))
      (fun chain => chainM_queriesWithinConstructionTargets core pkSeed pos chain _
        (chainStepsCore core msg chain.val)
        (vp.params.w - 1 - chainStepsCore core msg chain.val) (by
          rw [Nat.add_sub_of_le]
          exact chainStepsCore_le core msg chain.val)))
  intro tops
  exact publicHash_tl_wotsPk_queriesWithinConstructionTargets core pkSeed pos tops.toList

/-! The following paired contracts keep address provenance and the existing pathwise query budgets
together, so later game reductions cannot silently use one without the other. -/

theorem wotsPkGenM_traceContract {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
        (wotsPkGenM core skSeed pkSeed (wotsInstanceAdrs pos) :
          OracleComp (publicHashSpec core) core.Y) ∧
      IsTotalQueryBound
        (wotsPkGenM core skSeed pkSeed (wotsInstanceAdrs pos) :
          OracleComp (publicHashSpec core) core.Y)
        (vp.params.len * (vp.params.w - 1) + 1) := by
  exact ⟨wotsPkGenM_queriesWithinConstructionTargets core skSeed pkSeed pos,
    wotsPkGenM_isTotalQueryBound core skSeed pkSeed (wotsInstanceAdrs pos)⟩

theorem wotsSignM_traceContract {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (msg : core.Y) (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
        (wotsSignM core msg skSeed pkSeed (wotsInstanceAdrs pos) :
          OracleComp (publicHashSpec core) (WotsSig vp.params core)) ∧
      IsTotalQueryBound
        (wotsSignM core msg skSeed pkSeed (wotsInstanceAdrs pos) :
          OracleComp (publicHashSpec core) (WotsSig vp.params core))
        (∑ i : Fin vp.params.len, chainStepsCore core msg i.val) := by
  exact ⟨wotsSignM_queriesWithinConstructionTargets core msg skSeed pkSeed pos,
    wotsSignM_isTotalQueryBound core msg skSeed pkSeed (wotsInstanceAdrs pos)⟩

theorem wotsPkFromSigM_traceContract {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (sig : WotsSig vp.params core) (msg : core.Y)
    (pkSeed : core.PkSeed) (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
        (wotsPkFromSigM core sig msg pkSeed (wotsInstanceAdrs pos) :
          OracleComp (publicHashSpec core) core.Y) ∧
      IsTotalQueryBound
        (wotsPkFromSigM core sig msg pkSeed (wotsInstanceAdrs pos) :
          OracleComp (publicHashSpec core) core.Y)
        ((∑ i : Fin vp.params.len,
          (vp.params.w - 1 - chainStepsCore core msg i.val)) + 1) := by
  exact ⟨wotsPkFromSigM_queriesWithinConstructionTargets core sig msg pkSeed pos,
    wotsPkFromSigM_isTotalQueryBound core sig msg pkSeed (wotsInstanceAdrs pos)⟩

/-- One explicit `H_msg` call is always within the address-only construction predicate. -/
theorem publicHash_hmsg_queriesWithinConstructionTargets {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (r : core.Y) (pkSeed : core.PkSeed)
    (pkRoot : core.Y) (msg : List Byte) :
    QueriesWithinConstructionTargets core
      (PublicHash.hmsg core r pkSeed pkRoot msg :
        OracleComp (publicHashSpec core) (Bytes vp.params.m)) := by
  simp [QueriesWithinConstructionTargets, PublicHash.hmsg, ConstructionQueryReachable]

/-! ## Logged execution consequence -/

/-- A deterministic logged interpretation of a pathwise-certified program contains only encoded
tweaks from the construction ledger.  This is the execution-level bridge: the conclusion talks
about the concrete `QueryLog` returned by `withLogging`, while the premise remains independent of
the answer function. -/
theorem mem_logged_query_isConstructionReachable {vp : ValidatedParams}
    (core : CorePrimitives vp.params) {α : Type}
    (answer : QueryImpl (publicHashSpec core) Id)
    (program : OracleComp (publicHashSpec core) α)
    (hprogram : QueriesWithinConstructionTargets core program) :
    ∀ entry ∈ (simulateQ answer.withLogging program).run.run.2,
      ConstructionQueryReachable vp core entry.1 := by
  induction program using OracleComp.inductionOn with
  | pure x =>
      change ∀ entry ∈ ([] : QueryLog (publicHashSpec core)),
        ConstructionQueryReachable vp core entry.1
      simp
  | query_bind q continuation ih =>
      unfold QueriesWithinConstructionTargets at hprogram
      rw [OracleComp.isQueryBound_query_bind_iff] at hprogram
      rw [simulateQ_query_bind]
      simp only [OracleQuery.input_query, monadLift_self,
        WriterT.run_bind', QueryImpl.run_withLogging_apply]
      simp only [Id.run_bind, Id.run_map, Prod.map_snd, List.mem_append]
      simp only [Id.run_pure, List.mem_singleton]
      intro entry hentry
      rcases hentry with hentry | hentry
      · subst entry
        exact hprogram.1
      · apply ih (answer q).run
        · show QueriesWithinConstructionTargets core (continuation (answer q).run)
          exact hprogram.2 (answer q).run
        · exact hentry

/-- The logged-execution bridge at the canonical deterministic interpretation of a primitive
bundle: every `thash` entry (an `F`, `H`, or `T_l` call) the log records carries a tweak from the
bundle's encoded union ledger, stated through `encodeTargets` so it composes with
`EncodedTargetLedgerConditions`. -/
theorem mem_logged_query_impl_isConstructionReachable {vp : ValidatedParams}
    (prims : Primitives vp.params) {α : Type}
    (program : OracleComp (publicHashSpec prims.core) α)
    (hprogram : QueriesWithinConstructionTargets prims.core program) :
    ∀ entry ∈ (simulateQ (PublicHash.impl prims).withLogging program).run.run.2,
      match entry.1 with
      | .thash _ adrsKey _ => adrsKey ∈ encodeTargets prims (constructionAddresses vp)
      | .hmsg _ _ _ _ => True := by
  intro entry hentry
  have h := mem_logged_query_isConstructionReachable prims.core (PublicHash.impl prims)
    program hprogram entry hentry
  rcases entry with ⟨q, _⟩
  cases q with
  | thash pkSeed adrsKey xs =>
      simpa [ConstructionQueryReachable, encodedConstructionAddresses_core] using h
  | hmsg _ _ _ _ => trivial

end SLHDSA.Security
