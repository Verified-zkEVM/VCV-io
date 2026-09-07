/-
Copyright (c) 2026 Matthias Meijers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Meijers
-/

module
public import VCVio.CryptoFoundations.TweakableHash

/-!
# The collection oracle for the single-function, distinct-tweak, multi-target games

A reduction attacking one member of a tweakable-hash family must still evaluate members of that
family to simulate the rest of the structure — SLH-DSA's `F`, `H` and `T_ℓ` share one public seed
and one address space — and cannot do so once the seed is withheld from it. This oracle is that
access.

Which members it covers is fixed at instantiation, not here. `TweakableHashCollection.cons` puts the
attacked member in the collection, so this oracle also evaluates it at tweaks that are not targets;
that case is HK22's `Th_m ∈ Th_λ`, and a reduction against SLH-DSA needs it, since only a handful of
the addresses at which `F` runs are targets.

The collection is a parameter of each problem rather than a second game beside it. The stand-alone
notion is the instance at the empty collection (`TweakableHashCollection.empty`), where the query
type is uninhabited — pinned by `isEmpty_domain_collectionSpec_empty`; the games' `standalone`
constructors package that instantiation.

Module names in this directory follow from that. Their base name identifies the *property* rather
than distinguishing its stand-alone and collection-indexed instances: since the latter subsumes the
former, there is no separate collection module and no `…C` suffix, unlike the EasyCrypt development
this family is transcribed from. Where both validity presentations exist, the `FinalValidity` suffix
marks the sticky monitor (`TweakableHash.SourceFinalValidity`); an unsuffixed name denotes the
rejection-on-arrival game defined here.

The target/challenge tweaks must be distinct from each other and from every tweak submitted to the
collection oracle. This API enforces that discipline in the oracles: the collection oracle rejects
any tweak already in the challenge history, and each game's challenge oracle rejects a tweak already
in its own or the collection oracle's history. This follows DKKW's rejection-on-arrival presentation
and extends it across the collection boundary. BDHMS instead records every query and checks its
`VQS_t` predicate only in the final winning condition; that is a distinct adaptive experiment, not a
definitional presentation of this one, rendered by `TweakableHash.SourceFinalValidity`. The two
presentations have distinct adversary types, so neither admits the other's adversaries directly.
`TweakableHash.ToFinalValidity` instead supplies, per game, an explicit conversion sending an
adversary here to one against the corresponding source-final-validity game at exactly the same
advantage; `TweakableHash.SM_DT_TCR_advantage_toSourceFinalValidity` is the SM-DT-TCR member.

## References

- Hülsing and Kudinov, *Recovering the Tight Security Proof of SPHINCS+*,
  [ePrint 2022/346](https://eprint.iacr.org/2022/346), Def. 7 and Thm. 3.
- Barbosa, Dupressoir, Hülsing, Meijers and Strub, *A Tight Security Proof for SPHINCS+, Formally
  Verified*, [ePrint 2024/910](https://eprint.iacr.org/2024/910), Fig. 5 and Fig. 7.
-/

@[expose] public section

namespace TweakableHash

open OracleComp OracleSpec

variable {ι PkSeed Tweak Y Q : Type}

/-! ## The tweak discipline

Both oracles test a queried tweak against the two histories, and the predicates below are that test.
`Q` is the type of one recorded challenge query and `tweakOf` reads its tweak, so neither predicate
— nor `collectionOracle`, which uses the first of them — fixes the rest of a query's shape. SM-TCR
records `Tweak × M` and SM-PRE records `Tweak × M'`, both at `tweakOf := Prod.fst`; a game whose
history is tweaks alone takes `Q := Tweak` and `tweakOf := id`. -/

/-- The tweak `t` is reserved by the challenge oracle: it already occurs in the challenge history.
This is what `collectionOracle` rejects on. -/
def TweakReserved (tweakOf : Q → Tweak) (qsChal : List Q) (t : Tweak) : Prop :=
  ∃ e ∈ qsChal, tweakOf e = t

instance [DecidableEq Tweak] (tweakOf : Q → Tweak) (qsChal : List Q) (t : Tweak) :
    Decidable (TweakReserved tweakOf qsChal t) :=
  inferInstanceAs (Decidable (∃ e ∈ qsChal, tweakOf e = t))

/-- `t` is fresh for both histories: unreserved by the challenge oracle, and unspent on the
collection oracle. This is what each game's challenge oracle requires of a query, beyond its own
target cap. -/
def TweakFresh (tweakOf : Q → Tweak) (qsChal : List Q) (twsColl : List Tweak) (t : Tweak) : Prop :=
  ¬ TweakReserved tweakOf qsChal t ∧ t ∉ twsColl

instance [DecidableEq Tweak] (tweakOf : Q → Tweak) (qsChal : List Q) (twsColl : List Tweak)
    (t : Tweak) : Decidable (TweakFresh tweakOf qsChal twsColl t) :=
  inferInstanceAs (Decidable (¬ TweakReserved tweakOf qsChal t ∧ t ∉ twsColl))

/-- Freshness in the challenge history, in the elementwise form a caller holding a history of known
entries will have. -/
theorem not_tweakReserved_iff (tweakOf : Q → Tweak) (qsChal : List Q) (t : Tweak) :
    ¬ TweakReserved tweakOf qsChal t ↔ ∀ e ∈ qsChal, tweakOf e ≠ t := by
  simp [TweakReserved]

/-! ## The oracle -/

/-- The collection oracle's signature: a query names a member `i`, a tweak, and a message of *that
member's* type, and the response is `Option Y`, with `none` the rejection of a tweak reserved by the
challenge oracle. -/
abbrev collectionSpec (thColl : TweakableHashCollection ι PkSeed Tweak Y) :
    OracleSpec ((i : ι) × Tweak × thColl.Msg i) :=
  _ →ₒ Option Y

/-- The collection oracle at a public seed, over the two-part game state
`(challenge history, collection tweaks)`.

A query is rejected with `none` exactly when its tweak is reserved by the challenge oracle; the
state is then untouched. Otherwise the answer is the queried member evaluated at the game's seed,
and the tweak is appended to the collection tweak list. Repeated collection tweaks are accepted.

The challenge history is a list of `Q`, read only through `tweakOf`, so a game records whatever its
winning condition needs — `Tweak × M` for SM-TCR, `Tweak × M'` for SM-PRE, `Tweak` alone for a game
that needs no payload — and this oracle is unchanged by the choice. -/
def collectionOracle [DecidableEq Tweak] (tweakOf : Q → Tweak)
    (thColl : TweakableHashCollection ι PkSeed Tweak Y) (pk : PkSeed) :
    QueryImpl (collectionSpec thColl) (StateT (List Q × List Tweak) ProbComp) :=
  fun q => do
    let (qsChal, twsColl) ← get
    if TweakReserved tweakOf qsChal q.2.1 then
      return none
    else
      set (qsChal, twsColl ++ [q.2.1])
      return some (thColl.eval q.1 pk q.2.1 q.2.2)

/-- At the empty collection (`ι := Empty`) the oracle's query type is uninhabited, so a game
instantiated there cannot issue a collection query at all. This is what makes the stand-alone notion
recovered rather than merely approximated, so it is pinned rather than asserted. -/
theorem isEmpty_domain_collectionSpec_empty :
    IsEmpty (collectionSpec (TweakableHashCollection.empty PkSeed Tweak Y)).Domain :=
  ⟨fun q => q.1.elim⟩

/-! ## Basic properties and conventions -/

variable [DecidableEq Tweak] (tweakOf : Q → Tweak)
  {thColl : TweakableHashCollection ι PkSeed Tweak Y} {pk : PkSeed} {qsChal : List Q}
  {twsColl : List Tweak}

/-- A collection query whose tweak the challenge oracle has not reserved is answered with that
member's hash, and its tweak is appended to the end of the collection tweak list. -/
theorem collectionOracle_run_of_fresh (q : ((i : ι) × Tweak × thColl.Msg i))
    (hnew : ¬ TweakReserved tweakOf qsChal q.2.1) :
    (collectionOracle tweakOf thColl pk q).run (qsChal, twsColl) =
      pure (some (thColl.eval q.1 pk q.2.1 q.2.2), (qsChal, twsColl ++ [q.2.1])) := by
  simp [collectionOracle, hnew]

/-- A collection query at a tweak the challenge oracle has already issued is rejected, and the state
is unchanged. This is one half of the disjointness of the two tweak sets; the other half is each
game's challenge oracle rejecting a tweak already in the collection list. -/
theorem collectionOracle_run_of_challenge_clash (q : ((i : ι) × Tweak × thColl.Msg i))
    (hres : TweakReserved tweakOf qsChal q.2.1) :
    (collectionOracle tweakOf thColl pk q).run (qsChal, twsColl) =
      pure (none, (qsChal, twsColl)) := by
  simp [collectionOracle, hres]

/-- Repeating a collection tweak is **accepted**: querying the same tweak twice in a row is answered
both times, and both occurrences are appended. Only disjointness from the target tweaks is required,
not distinctness among the collection tweaks themselves, and a reduction may legitimately evaluate
one address more than once.

Stated over two consecutive queries rather than one, because the single-query statement is a
corollary of `collectionOracle_run_of_fresh` and so would still hold if the oracle grew a
self-distinctness check. This form fails outright if it does, and it fixes the append order at the
same time. -/
theorem collectionOracle_run_of_repeated_tweak (q : ((i : ι) × Tweak × thColl.Msg i))
    (hnew : ¬ TweakReserved tweakOf qsChal q.2.1) :
    ((collectionOracle tweakOf thColl pk q).run (qsChal, twsColl) >>= fun r =>
        (collectionOracle tweakOf thColl pk q).run r.2) =
      pure (some (thColl.eval q.1 pk q.2.1 q.2.2), (qsChal, twsColl ++ [q.2.1, q.2.1])) := by
  simp [collectionOracle, hnew]

end TweakableHash
