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

`H_msg` carries no address, so `ConstructionQueryReachable` accepts every `.hmsg` query
unconditionally; only `.thash` queries are constrained.  Membership is deliberately stated after
`CorePrimitives.adrsToKey`: compressed SHA-2 encodings need not be globally injective.  A game that
needs distinct encoded targets can refine the trace to the relevant role and use the corresponding
field of `EncodedTargetLedgerConditions`, or separately establish cross-role encoded disjointness.
That record proves encoded distinctness
per role; it does not by itself prove cross-role encoded disjointness or duplicate-freedom of this
encoded union.

The programs certified here are the WOTS+ ones: `chainM` over any step interval inside
`[0, w - 1)`, and `wotsPkGenM`, `wotsSignM`, and `wotsPkFromSigM` at any reachable
`LayerPosition`, the latter three each paired with their total query bounds.  The FORS, XMSS,
hypertree, and scheme programs are not certified by this module.  The logged-execution theorem
applies to any pathwise-certified program interpreted through `QueryImpl.withLogging` over an
arbitrary deterministic handler `QueryImpl (publicHashSpec core) Id`, and in particular through the
canonical `PublicHash.impl` of a primitive bundle.  It is the SLH-DSA instance of
`OracleComp.holds_of_mem_run_simulateQ_withLogging`, whose `support`-based companion
`OracleComp.holds_of_mem_log_of_mem_support_run_simulateQ` covers `loggingOracle`; a stateful
probabilistic handler such as `PublicHash.randomOracle` needs its own bridge, which this module
does not provide.

The definitions are opaque to importers.  What a downstream slice uses are the public equations:
`mem_constructionAddresses_iff` and `constructionAddresses_length` for the union ledger,
`mem_encodedConstructionAddresses_iff` and `encodeTargets_constructionAddresses` for its encoded
image, `constructionQueryReachable_thash_iff` and `constructionQueryReachable_hmsg` for the query
predicate, the structural laws `QueriesWithinConstructionTargets.pure`, `.bind`, `.query_iff`,
and `.ofFnM` for assembling the predicate along a program, and
`queriesWithinConstructionTargets_iff_isQueryBound` to reach the generic `IsQueryBound` laws (for
example `isQueryBound_map_iff`) from the wrapper.

The union is a complete structural ledger, not the partial, source-shaped WOTS+ target selection
used by the undetectability reduction.  These provenance theorems neither execute the ledger's
unqueried addresses nor establish a game equivalence; a later reduction must connect its actual
partial selection to the relevant ledger entries.

## References

- NIST FIPS 205, §4.1 (the tweakable-hash roles `F`, `H`, `T_l`, and `H_msg`), Algorithms 5--8
  (WOTS+ chain, public-key generation, signing, and public-key recovery)
-/

public section

open OracleComp OracleSpec

namespace SLHDSA.Security

/-- The union of the six structural address ledgers, in the order FORS leaves, FORS internal nodes,
FORS roots, WOTS+ hash steps, WOTS+ public-key compressions, XMSS internal nodes.

Two of the eight role ledgers are deliberately absent: every address the selection-dependent
WOTS+ ledgers `selectedWotsAddresses` and `optionalWotsAddresses` list is already a
`wotsStepAddresses` entry (`selectedWotsAddresses_subset`, `optionalWotsAddresses_subset`), so
nothing is lost.  No secret-key
derivation address (`wotsSkAdrs`, `forsSkAdrs`, type codes `WOTS_PRF` and `FORS_PRF`) is listed,
because `CorePrimitives.PRF` and `PRFmsg` are pure fields of the primitives and never
`publicHashSpec` queries. -/
def constructionAddresses (vp : ValidatedParams) : List Adrs :=
  forsLeafAddresses vp ++ forsTreeAddresses vp ++ forsRootAddresses vp ++
    wotsStepAddresses vp ++ wotsPkAddresses vp ++ xmssNodeAddresses vp

/-- The union ledger is duplicate-free: each role ledger is, and the roles are pairwise disjoint. -/
theorem constructionAddresses_nodup (vp : ValidatedParams) : (constructionAddresses vp).Nodup :=
  nodup_structuralLedgers_append vp

/-- An address is in the union ledger exactly when it is in one of the six role ledgers. -/
theorem mem_constructionAddresses_iff {vp : ValidatedParams} (adrs : Adrs) :
    adrs ∈ constructionAddresses vp ↔
      adrs ∈ forsLeafAddresses vp ∨ adrs ∈ forsTreeAddresses vp ∨
        adrs ∈ forsRootAddresses vp ∨ adrs ∈ wotsStepAddresses vp ∨
          adrs ∈ wotsPkAddresses vp ∨ adrs ∈ xmssNodeAddresses vp := by
  simp [constructionAddresses]

/-- The union ledger has the summed length of its six components: the five exact role counts and
the `wotsInstanceCount * len * (w - 1)` executed WOTS+ steps. -/
theorem constructionAddresses_length (vp : ValidatedParams) :
    (constructionAddresses vp).length =
      targetCount vp.params .forsF + targetCount vp.params .forsH + targetCount vp.params .forsTl +
        wotsInstanceCount vp.params * vp.params.len * (vp.params.w - 1) +
        targetCount vp.params .wotsTl + targetCount vp.params .xmssH := by
  simp only [constructionAddresses, List.length_append, forsLeafAddresses_length,
    forsTreeAddresses_length, forsRootAddresses_length, wotsStepAddresses_length,
    wotsPkAddresses_length, xmssNodeAddresses_length]

/-- The encoded image of the complete structural construction-address ledger. -/
def encodedConstructionAddresses (vp : ValidatedParams)
    (core : CorePrimitives vp.params) : List core.AdrsKey :=
  (constructionAddresses vp).map core.adrsToKey

/-- Over a primitive bundle's core, the encoded union ledger is `encodeTargets` of the union. -/
theorem encodedConstructionAddresses_core {vp : ValidatedParams} (prims : Primitives vp.params) :
    encodedConstructionAddresses vp prims.core =
      encodeTargets prims (constructionAddresses vp) := by
  simp only [encodedConstructionAddresses, encodeTargets]

/-- An encoded tweak is in the encoded union ledger exactly when it is the encoding of a listed
structural address. -/
theorem mem_encodedConstructionAddresses_iff {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (adrsKey : core.AdrsKey) :
    adrsKey ∈ encodedConstructionAddresses vp core ↔
      ∃ adrs ∈ constructionAddresses vp, core.adrsToKey adrs = adrsKey := by
  simp [encodedConstructionAddresses]

/-- The encoded union ledger is the concatenation of the six encoded role ledgers, in the order of
`constructionAddresses`.  This is the equation through which a statement about the union composes
with the per-role fields of `EncodedTargetLedgerConditions`. -/
theorem encodeTargets_constructionAddresses {vp : ValidatedParams} (prims : Primitives vp.params) :
    encodeTargets prims (constructionAddresses vp) =
      encodeTargets prims (forsLeafAddresses vp) ++ encodeTargets prims (forsTreeAddresses vp) ++
        encodeTargets prims (forsRootAddresses vp) ++ encodeTargets prims (wotsStepAddresses vp) ++
        encodeTargets prims (wotsPkAddresses vp) ++ encodeTargets prims (xmssNodeAddresses vp) := by
  simp only [constructionAddresses, encodeTargets, List.map_append]

/-- A public-hash query is construction-reachable when its encoded tweak occurs in the structural
ledger. `H_msg` carries no tweak and is always accepted by this address predicate. -/
def ConstructionQueryReachable (vp : ValidatedParams)
    (core : CorePrimitives vp.params) : (publicHashSpec core).Domain → Prop
  | .thash _ adrsKey _ => adrsKey ∈ encodedConstructionAddresses vp core
  | .hmsg _ _ _ _ => True

/-- A `thash` query is construction-reachable exactly when its tweak is in the encoded union
ledger. -/
theorem constructionQueryReachable_thash_iff {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (pkSeed : core.PkSeed) (adrsKey : core.AdrsKey)
    (xs : List core.Y) :
    ConstructionQueryReachable vp core (.thash pkSeed adrsKey xs) ↔
      adrsKey ∈ encodedConstructionAddresses vp core :=
  Iff.rfl

/-- Every `hmsg` query is construction-reachable: it carries no address. -/
@[simp]
theorem constructionQueryReachable_hmsg {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (r : core.Y) (pkSeed : core.PkSeed) (pkRoot : core.Y)
    (msg : List Byte) :
    ConstructionQueryReachable vp core (.hmsg r pkSeed pkRoot msg) :=
  trivial

/-- Every syntactically reachable path through `program` uses only construction-ledger tweaks.
This is the predicate-only query bound `AllQueriesSatisfy`: it counts no queries and constrains
only which public-hash inputs the program can reach. -/
def QueriesWithinConstructionTargets {vp : ValidatedParams}
    (core : CorePrimitives vp.params) {α : Type}
    (program : OracleComp (publicHashSpec core) α) : Prop :=
  program.AllQueriesSatisfy (ConstructionQueryReachable vp core)

/-- The wrapper is the predicate-only `IsQueryBound`; this is the equation an importer uses to
reach the generic query-bound laws (`isQueryBound_map_iff`, `isQueryBound_iff_of_map_eq`, and the
`allQueriesSatisfy_*` family, which `allQueriesSatisfy_def` connects to this form). -/
theorem queriesWithinConstructionTargets_iff_isQueryBound {vp : ValidatedParams}
    (core : CorePrimitives vp.params) {α : Type}
    (program : OracleComp (publicHashSpec core) α) :
    QueriesWithinConstructionTargets core program ↔
      program.IsQueryBound () (fun q _ => ConstructionQueryReachable vp core q) (fun _ _ => ()) :=
  allQueriesSatisfy_def program _

@[simp]
theorem QueriesWithinConstructionTargets.pure {vp : ValidatedParams}
    (core : CorePrimitives vp.params) {α : Type} (x : α) :
    QueriesWithinConstructionTargets core
      (pure x : OracleComp (publicHashSpec core) α) :=
  allQueriesSatisfy_pure x _

/-- Pathwise target provenance composes through monadic sequencing. -/
theorem QueriesWithinConstructionTargets.bind {vp : ValidatedParams}
    {core : CorePrimitives vp.params} {α β : Type}
    {program : OracleComp (publicHashSpec core) α}
    {continuation : α → OracleComp (publicHashSpec core) β}
    (hprogram : QueriesWithinConstructionTargets core program)
    (hcontinuation : ∀ x, QueriesWithinConstructionTargets core (continuation x)) :
    QueriesWithinConstructionTargets core (program >>= continuation) :=
  allQueriesSatisfy_bind hprogram hcontinuation

/-- A single public-hash query is within the construction ledger exactly when its query input is. -/
@[simp]
theorem QueriesWithinConstructionTargets.query_iff {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (q : (publicHashSpec core).Domain) :
    QueriesWithinConstructionTargets core
        (liftM ((publicHashSpec core).query q) :
          OracleComp (publicHashSpec core) ((publicHashSpec core).Range q)) ↔
      ConstructionQueryReachable vp core q :=
  allQueriesSatisfy_query_iff q _

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
  apply (QueriesWithinConstructionTargets.query_iff core _).2
  exact constructionQueryReachable_thash_of_mem core pkSeed adrs [x] hadrs

/-- An explicit `H` call at any address in the structural union is pathwise certified. -/
theorem publicHash_h_queriesWithinConstructionTargets_of_mem {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (pkSeed : core.PkSeed) (adrs : Adrs)
    (left right : core.Y) (hadrs : adrs ∈ constructionAddresses vp) :
    QueriesWithinConstructionTargets core
      (PublicHash.h core pkSeed adrs left right :
        OracleComp (publicHashSpec core) core.Y) := by
  apply (QueriesWithinConstructionTargets.query_iff core _).2
  exact constructionQueryReachable_thash_of_mem core pkSeed adrs [left, right] hadrs

/-- An explicit `T_l` call at any address in the structural union is pathwise certified. -/
theorem publicHash_tl_queriesWithinConstructionTargets_of_mem {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (pkSeed : core.PkSeed) (adrs : Adrs)
    (xs : List core.Y) (hadrs : adrs ∈ constructionAddresses vp) :
    QueriesWithinConstructionTargets core
      (PublicHash.tl core pkSeed adrs xs : OracleComp (publicHashSpec core) core.Y) := by
  apply (QueriesWithinConstructionTargets.query_iff core _).2
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

/-- A WOTS+ chain whose interval stays in `[0, w - 1)` uses only union-ledger tweaks.  Each query
is routed through `mem_wotsStepAddresses`, so the addresses are WOTS-step addresses, but the
predicate itself records only membership in the union. -/
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

/-- Pathwise target provenance passes through `Vector.ofFnM` when every component has it. -/
theorem QueriesWithinConstructionTargets.ofFnM {vp : ValidatedParams}
    (core : CorePrimitives vp.params) {Y : Type} {k : ℕ}
    (program : Fin k → OracleComp (publicHashSpec core) Y)
    (hprogram : ∀ i, QueriesWithinConstructionTargets core (program i)) :
    QueriesWithinConstructionTargets core (Vector.ofFnM program) :=
  allQueriesSatisfy_ofFnM program hprogram

/-- WOTS+ public-key generation at a reachable position uses only union-ledger tweaks.  Its queries
are routed through `mem_wotsStepAddresses` and `mem_wotsPkAddresses`; the predicate records only
union membership, not the role of each query. -/
theorem wotsPkGenM_queriesWithinConstructionTargets {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (skSeed : core.SkSeed) (pkSeed : core.PkSeed)
    (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
      (wotsPkGenM core skSeed pkSeed (wotsInstanceAdrs pos) :
        OracleComp (publicHashSpec core) core.Y) := by
  apply QueriesWithinConstructionTargets.bind
    (QueriesWithinConstructionTargets.ofFnM core
      (fun chain : Fin vp.params.len =>
        chainM core pkSeed (wotsChainAdrs (wotsInstanceAdrs pos) chain.val)
          (core.PRF pkSeed skSeed (wotsSkAdrs (wotsInstanceAdrs pos) chain.val))
          0 (vp.params.w - 1))
      (fun chain => chainM_queriesWithinConstructionTargets core pkSeed pos chain _ 0
        (vp.params.w - 1) (by omega)))
  intro tops
  exact publicHash_tl_wotsPk_queriesWithinConstructionTargets core pkSeed pos tops.toList

/-- WOTS+ signing at a reachable position uses only union-ledger tweaks.  Its queries are routed
through `mem_wotsStepAddresses`; the predicate records only union membership. -/
theorem wotsSignM_queriesWithinConstructionTargets {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (msg : core.Y) (skSeed : core.SkSeed)
    (pkSeed : core.PkSeed) (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
      (wotsSignM core msg skSeed pkSeed (wotsInstanceAdrs pos) :
        OracleComp (publicHashSpec core) (WotsSig vp.params core)) := by
  exact QueriesWithinConstructionTargets.ofFnM core _ fun chain =>
    chainM_queriesWithinConstructionTargets core pkSeed pos chain _ 0
      (chainStepsCore core msg chain.val) (by
        simpa using chainStepsCore_le core msg chain.val)

/-- WOTS+ public-key recovery at a reachable position uses only union-ledger tweaks.  Its queries
are routed through `mem_wotsStepAddresses` and `mem_wotsPkAddresses`; the predicate records only
union membership. -/
theorem wotsPkFromSigM_queriesWithinConstructionTargets {vp : ValidatedParams}
    (core : CorePrimitives vp.params) (sig : WotsSig vp.params core) (msg : core.Y)
    (pkSeed : core.PkSeed) (pos : LayerPosition vp) :
    QueriesWithinConstructionTargets core
      (wotsPkFromSigM core sig msg pkSeed (wotsInstanceAdrs pos) :
        OracleComp (publicHashSpec core) core.Y) := by
  apply QueriesWithinConstructionTargets.bind
    (QueriesWithinConstructionTargets.ofFnM core
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

/-! The following contracts pair address provenance with the total query bound of the same program,
kept together for downstream use. -/

/-- WOTS+ public-key generation at a reachable position queries only union-ledger tweaks and makes
at most `len * (w - 1) + 1` queries. -/
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

/-- WOTS+ signing at a reachable position queries only union-ledger tweaks and makes at most
`∑ i, chainStepsCore core msg i` queries. -/
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

/-- WOTS+ public-key recovery at a reachable position queries only union-ledger tweaks and makes at
most `(∑ i, (w - 1 - chainStepsCore core msg i)) + 1` queries. -/
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
the answer function.  It is `OracleComp.holds_of_mem_run_simulateQ_withLogging` at the
construction predicate. -/
theorem constructionQueryReachable_of_mem_run_withLogging {vp : ValidatedParams}
    (core : CorePrimitives vp.params) {α : Type}
    (answer : QueryImpl (publicHashSpec core) Id)
    (program : OracleComp (publicHashSpec core) α)
    (hprogram : QueriesWithinConstructionTargets core program) :
    ∀ entry ∈ (simulateQ answer.withLogging program).run.run.2,
      ConstructionQueryReachable vp core entry.1 :=
  holds_of_mem_run_simulateQ_withLogging (P := ConstructionQueryReachable vp core) answer
    hprogram

/-- The logged-execution bridge at the canonical deterministic interpretation of a primitive
bundle: every `thash` entry (an `F`, `H`, or `T_l` call) the log records carries a tweak from
`encodeTargets prims (constructionAddresses vp)`.  `encodeTargets_constructionAddresses` splits
that list into the six encoded role ledgers whose distinctness `EncodedTargetLedgerConditions`
states; the bridge itself does not identify a query's role or prove encoded duplicate-freedom
across roles.  The conclusion is stated as an equation hypothesis on the entry rather than a
`match`, so a consumer applies it to a `thash` entry directly. -/
theorem constructionQueryReachable_of_mem_run_withLogging_impl {vp : ValidatedParams}
    (prims : Primitives vp.params) {α : Type}
    (program : OracleComp (publicHashSpec prims.core) α)
    (hprogram : QueriesWithinConstructionTargets prims.core program) :
    ∀ entry ∈ (simulateQ (PublicHash.impl prims).withLogging program).run.run.2,
      ∀ (pkSeed : prims.core.PkSeed) (adrsKey : prims.core.AdrsKey) (xs : List prims.core.Y),
        entry.1 = .thash pkSeed adrsKey xs →
          adrsKey ∈ encodeTargets prims (constructionAddresses vp) := by
  intro entry hentry pkSeed adrsKey xs hquery
  have h := constructionQueryReachable_of_mem_run_withLogging prims.core (PublicHash.impl prims)
    program hprogram entry hentry
  rw [hquery, constructionQueryReachable_thash_iff, encodedConstructionAddresses_core] at h
  exact h

end SLHDSA.Security
