/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.HmsgWitnesses
public import HashSig.SLHDSA.Security.SchemeWitnesses
public import VCVio.CryptoFoundations.SignatureAlg

/-!
# The deterministic strong-unforgeability residual

`VCVio.CryptoFoundations.SignatureAlg` splits strong unforgeability into ordinary existential
unforgeability plus one extra event: a valid signature, not itself returned by the signing oracle,
on a message that *was* sent to it.  That split is a probability identity, and it is generic.  This
module is the SLH-DSA-specific deterministic remainder: what a signing log, a message and a
signature that the log does not contain as a pair yield about the `H_msg` input the signature names.

Everything here is deterministic.  No probability, adversary, advantage, game hop or `ProbComp`
appears, and no experiment is run.  Two library predicates on a log do appear —
`SignatureAlg.signingLogContains` and `QueryLog.wasQueried` — because both are decidable functions
of a list; what does not appear is anything that samples the key pair or bounds a probability.

## What the split leaves for SLH-DSA to do, and where it actually sits

The scheme dispatch of `HashSig.SLHDSA.Security.SchemeWitnesses` reads no log: `findWitness_isSome`
takes `[DecidableEq prims.Y]`, the byte laws, a secret seed, a public seed, a message, a signature
and a target, and the single hypothesis that the signature verifies.  So a forged signature routes
into a witness family whether or not its message was queried, and the strong-unforgeability split
buys the dispatch nothing.

What does read a log is the `H_msg` bridge of `HashSig.SLHDSA.Security.HmsgWitnesses`.  Its
dichotomy `itsr_wins_or_uncovered` needs the forged *pair* to be absent from the target transcript,
and the transcript a reduction records is this log's `(randomizer, message)` projection,
`logQueries`.  Under existential unforgeability that hypothesis is free: an unqueried message
contributes no entry at all, which is `notMem_embedTargets_of_not_wasQueried`.  Under strong
unforgeability it is not free, and supplying it is the whole SLH-DSA-specific residual.

`itsrFresh_or_sameRandomizer` is that residual.  It takes only the strong-unforgeability freshness
condition itself — the log does not contain this exact `(message, signature)` pair — and returns one
of two things: either the forged randomizer occurs in no logged signature at that message, and then
the pair is fresh at the embedded transcript and the bridge applies unchanged; or some logged
signature at that message carries the *same* randomizer, differs from the forged one, produces the
same `H_msg` digest split against the same public key, and differs from it in its FORS half or in
its hypertree half.

Note where the case split is taken.  It is not the queried/unqueried split of the library identity:
the dichotomy holds under pair freshness alone, and the unqueried case is the special case in which
the second branch is empty.  What the library's split does say about the second branch is that it
lives entirely inside the same-message event — a logged signature at `msg` makes `msg` queried,
which is `wasQueried_eq_true_of_mem_loggedSignatures`.

## What the second branch is worth, stated as theorems rather than as a caveat

On the second branch the `H_msg` bridge is not merely unproved, it is unavailable.  The forged pair
*is* one of the embedded targets (`mem_embedTargets_of_mem_loggedRandomizers`), so the winning
condition fails on its freshness conjunct (`not_wins_of_mem_loggedRandomizers`); and the candidate's
own selected indices are all covered by that same target, so the first-uncovered-index extractor
returns nothing (`findUncoveredIndex_eq_none_of_mem_loggedRandomizers`).  Both alternatives of
`itsr_wins_or_uncovered` are therefore closed off, and no amount of care in a reduction reopens
them.

What a reduction would have to use on that branch is the *pair*: two distinct signatures that split
to one digest, hence one FORS instance and one set of opened leaves, and differ somewhere in their
component vectors.  Three of the four merged families cannot be handed that pair at all, because
they compute their second object from `sk` rather than taking it: `findXmssWitness` recovers the
honest leaf and the honest WOTS+ signature from `sk` and the honest message, `findForsWitness` the
honest FORS material, and `findHypertreeWitness` carries `sk` down the layer walk.  For those, what
already applies to the forged signature alone applies here unchanged and the second signature enters
nowhere.

The WOTS+ family is not of that shape, and it is the one that has to be argued.  `findWotsWitness`
and its per-chain helper `findWotsChainWitness` are the lane's only two searches that take two
`(signature, message)` pairs; the partner is an arbitrary signature, and neither
`findWotsWitness_sound` nor `findWotsWitness_isSome` mentions `sk`.  The chain helper is inert when
the two messages agree — it returns nothing at an index unless the two chain-step counts differ
there — so what decides its reach is whether this branch drives the two messages apart.  Those two
messages are the FORS public keys the two signatures recover, which `verifyInternal` hands to the
hypertree as its layer-0 WOTS+ message; by `schemeParts_eq_of_randomizer_eq` the pair splits to one
digest against one public key, which leaves each of the two keys a function of that signature's FORS
half and of nothing that differs between them.

The branch does not drive them apart.  What it gives is a disjunction, and where only its hypertree
disjunct holds the two FORS halves are equal and the two recovered keys are one key; two FORS halves
that do differ may still recover one key, and the fixture's `forgeryFors` is a pair that does.  So
`findWotsWitness_isSome`'s guard `msg ≠ msg'` is met on the branch's pairs whose recovered keys
differ, and the search returns a witness on those; where the two keys coincide the guard fails and
that theorem says nothing either way.

What places the family out of scope is therefore not the guard but what a returned witness says.
`findWotsWitness_sound` concludes `WotsWitness.Valid … sig' msg'` — validity against the *supplied*
partner — and, as its own docstring records, says nothing about whether that partner was committed
as a game target.  Here the supplied partner is a second adversarial signature, so the witness is a
collision between two adversarial objects rather than an attack on honest committed material, which
is exactly the two-adversarial-signatures argument this lane holds out of scope.  A same-digest
extractor is therefore a further witness module with its own witness type, and it is not in this
pull request.

`HashSig.SLHDSA.Security.HypertreeWitnesses`'s review recorded that a two-adversarial-signatures
argument is out of scope for the existential-unforgeability line; `schemeParts_eq_of_randomizer_eq`
and `components_ne_of_ne_of_randomizer_eq` do not reopen it — they say what such an argument would
be handed, and prove no extraction from it.

## There is no strong unforgeability in the EasyCrypt development

This module's source correspondence is that it has none, and the reason is a difference in how the
two developments randomize signing rather than an omission.

Nothing in `FV-SPHINCSPLUS-EC` states a strong-unforgeability property.  Over the eleven `.ec` and
`.eca` files, the case-insensitive tokens `strong` and `unforge` occur zero times, and every
occurrence matching `suf` is the word `suff`.  Every freshness decision in the development is on the
message alone: the twenty assignments to `is_fresh` are `! m' \in qs` (`FORS_ES.ec:3370`, `:3588`,
`SPHINCS_PLUS.ec:1207`, `:1356`), a call to a `fresh` procedure (`FORS_ES.ec:2034`, `:3203`,
`SPHINCS_PLUS.ec:2126`, `:2149`, `:2175`, `:2235`), or a message disequality in the
no-adaptivity games (`FL_SL_XMSS_MT_ES.ec:1879`, `:3225`, `:3453`, `SPHINCS_PLUS.ec:2638`,
`WOTS_TW_ES.ec:2371`, `:2618`, `:3671`, `:3724`, `:3775`, `:3915`); and all three declarations of
a `fresh` procedure take a `msg` (`FORS_ES.ec:1988` in an oracle module type, `:2099-2101`,
`SPHINCS_PLUS.ec:2039-2041`), the two with bodies returning `! m \in qs`.  No signature is compared
anywhere.

Two consequences, and they are different from each other.

**The source needs no randomizer reasoning.**  Its ITSR pair-freshness conjunct
`! (mk', m') \in zip …mks …qs` (`FORS_ES.ec:3214`) is discharged by the surrounding game's own
freshness: that game returns `is_valid /\ is_fresh` with `is_fresh` the message test
(`FORS_ES.ec:3203`, `:3244`), so no winning run has the forged message among the queried ones and no
recorded pair can carry it.  This holds however the message key is produced, and is the step Lean's
strong-unforgeability freshness condition cannot take.

**The source's transcript carries one randomizer per message.**  The message key is
`op mkg : mseed -> msg -> mkey` (`FORS_ES.ec:409`, `SPHINCS_PLUS.ec:409`), a function of the master
seed and the message with no per-signature argument, and the signing oracle before the `MKG` hop
computes `mk <- mkg ms m` (`SPHINCS_PLUS.ec:2020`).  After the hop the oracle memoizes on the
message — `if (m \notin mmap) { mk <$ dmkey; mmap.[m] <- mk } mk <- oget mmap.[m]`
(`SPHINCS_PLUS.ec:2082-2086`, and `FORS_ES.ec:2070-2074` for the M-FORS oracle) — and the hop's
equivalence identifies that map with the generic `PRF` oracle's own memo table,
`O_CMA_SPHINCSPLUSTWFS_NPRF.mmap{1} = O_PRF_Default.m{2}` (`SPHINCS_PLUS.ec:3112`), whose ideal
branch is memoized the same way (`KeyedHashFunctions.eca:1630-1638`).  Signing is deterministic on
both sides of the hop, so re-signing a message returns the identical signature, and the list this
module calls `loggedRandomizers` would be constant at each message.

FIPS 205 Algorithm 19 sets `opt_rand ← addrnd` and then `R ← PRF_msg(SK.prf, opt_rand, M)` (lines 2
and 3), and §9.2 makes that hedged variant the default while offering `opt_rand ← PK.seed` as a
deterministic alternative under which "signing the same message twice will result in the same
signature".  `HashSig.SLHDSA.GeneralScheme.signInternalM` takes `addrnd` as an argument, and
`HashSig.SLHDSA.RandomOracle.slhSignM` samples it and passes it to the depth-one compatibility
signer `HashSig.SLHDSA.slhSignInternalM`, which derives `R` by the same
`core.PRFmsg sk.skPrf addrnd msg`.  So the Lean transcript is the hedged one and
`loggedRandomizers` at one message can hold as many distinct values as there were queries.  The
residual's second branch is what that costs, and it is empty for the deterministic variant, which is
the variant the source's shape matches.

So the correspondence is: no source counterpart, because the source's game never reaches the case,
and its signer could not have populated it as widely if it had.

## What is deliberately not here

No probability, and in particular no use of `strongUnforgeableAdv.advantage_eq_euf_add_sameMessage`,
whose statement carries a runtime-factoring hypothesis and whose two summands are advantages.
Bounding the same-message summand for a specific reduction adversary is the next slice's, and issue
#629 item 2b is the reason it must be that identity rather than the unbounded `SameMessageBinding`
wrapper.  The generic Boolean partition inside that identity's proof is not restated here either: it
is not SLH-DSA-specific and the library already discharges it.

No extraction from the second branch, for the reason given above.  No `SignatureAlg` packaging: the
statements below are over `QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)`, which
needs none, and the only `SignatureAlg` on `main` is at `p.d = 1`.  No equation relating a logged
signature to `signInternal`: that would be an edit to a merged module, and nothing here needs one —
the divergence above is exercised at values in `HashSigTest.SLHDSA.SufResidual` instead.

## Labels

The lane's two labels, applied by the criterion the sibling modules use.

*Transcript transport* — a statement carrying a free signing log, and so about the transcript that
log projects to.  Twenty-three of the twenty-five declarations below are of this kind, which is what
one should expect of a module whose whole subject is what a log does and does not contain:

* `loggedSignatures`, `loggedSignatures_eq`, `mem_loggedSignatures`,
  `signingLogContains_eq_true_iff`, `wasQueried_eq_true_iff`,
  `wasQueried_eq_true_of_mem_loggedSignatures`, `sameMessage_condition_iff`,
  `exists_ne_of_sameMessage`, `loggedSignatures_eq_nil_of_not_wasQueried`;
* `loggedRandomizers`, `loggedRandomizers_eq`, `mem_loggedRandomizers`;
* `logQueries`, `logQueries_eq`, `mem_logQueries_iff`, `notMem_logQueries_of_not_wasQueried`;
* `notMem_embedTargets_of_not_wasQueried`, `notMem_embedTargets_of_notMem_loggedRandomizers`,
  `mem_embedTargets_of_mem_loggedRandomizers`, `not_wins_of_mem_loggedRandomizers`,
  `findUncoveredIndex_eq_none_of_mem_loggedRandomizers`,
  `wins_or_uncovered_of_notMem_loggedRandomizers`;
* `itsrFresh_or_sameRandomizer`.

*Deterministic inclusion* — a statement with no signing log in it.  There are two, and both are
about a pair of signatures rather than about a transcript:

* `schemeParts_eq_of_randomizer_eq`, `components_ne_of_ne_of_randomizer_eq`.

Those twenty-five are the module's whole interface; none is `private` and none carries `@[expose]`.

Nine of them carry `[DecidableEq (GeneralScheme.SignatureCore vp prims.core)]`.  That instance is
not derivable on this branch: neither `SLHDSA.SignatureCore` nor `ForsTreeSigCore` nor `XmssSigCore`
declares or derives one, and `HashSig` contains no instance for any of the three.  It is required by
the library predicates being bridged, `SignatureAlg.signingLogContains` and `QueryLog.wasQueried`,
and it is carried as a hypothesis rather than supplied, because supplying it would mean adding an
instance to a merged module from inside this pull request.

## References

- NIST FIPS 205, §4.1, §9.2 Algorithm 19, §9.3 Algorithm 20
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`FORS_ES.ec`, `SPHINCS_PLUS.ec`, `KeyedHashFunctions.eca`,
  `FL_SL_XMSS_MT_ES.ec`, `WOTS_TW_ES.ec`)
-/

public section

namespace SLHDSA.Security

open OracleSpec Security.CanonicalGames KeyedHash

variable {vp : ValidatedParams} {prims : Primitives vp.params}

/-! ## The log, read at one message -/

/-- The signatures a signing log returned for one message, in query order.

A `QueryLog` entry is a dependent pair of a queried message and the signature returned for it; this
selects the second components of the entries at `msg`.  Repeated queries on one message contribute
one entry each, so this list is as long as the number of times `msg` was signed, and two of its
entries may be equal.

*Transcript transport.* -/
def loggedSignatures (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
    (msg : List Byte) : List (GeneralScheme.SignatureCore vp prims.core) :=
  log.filterMap fun e => if e.1 = msg then some e.2 else none

/-- Unfolding equation for `loggedSignatures`.  The body is not exposed, so this is what a consumer
that needs the `List.filterMap` shape rewrites with.

*Transcript transport.* -/
theorem loggedSignatures_eq
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
    (msg : List Byte) :
    loggedSignatures log msg =
      log.filterMap fun e => if e.1 = msg then some e.2 else none := by rfl

/-- **Membership is exact-entry membership**, in both directions: a signature is listed at `msg`
exactly when the log contains the entry pairing `msg` with it.

The `Iff` is what makes the reading faithful rather than merely sound.  A one-way implication would
also hold of a definition that kept only the first entry at each message, and such a definition
would call a forged randomizer fresh when a later signature at the same message carried it.

*Transcript transport.* -/
theorem mem_loggedSignatures
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)}
    {msg : List Byte} {sig : GeneralScheme.SignatureCore vp prims.core} :
    sig ∈ loggedSignatures log msg ↔ (⟨msg, sig⟩ : (_ : List Byte) × _) ∈ log := by
  rw [loggedSignatures_eq, List.mem_filterMap]
  constructor
  · rintro ⟨⟨t, s⟩, hmem, he⟩
    rcases eq_or_ne t msg with rfl | h
    · simp only [if_pos, Option.some.injEq] at he
      exact he ▸ hmem
    · simp [h] at he
  · exact fun h => ⟨⟨msg, sig⟩, h, by simp⟩

/-- The library's exact-pair predicate, read through this module's list.

`SignatureAlg.signingLogContains` is the predicate the strong-unforgeability experiment negates, so
this is the bridge every statement below crosses.

*Transcript transport.* -/
theorem signingLogContains_eq_true_iff [DecidableEq (GeneralScheme.SignatureCore vp prims.core)]
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) :
    SignatureAlg.signingLogContains log msg sig = true ↔ sig ∈ loggedSignatures log msg := by
  rw [SignatureAlg.signingLogContains]
  simp only [decide_eq_true_eq]
  exact mem_loggedSignatures.symm

/-- The library's message predicate, read through this module's list.

`QueryLog.wasQueried` is the predicate the existential-unforgeability experiment negates and the
one the same-message experiment asserts, so this is the second bridge.

*Transcript transport.* -/
theorem wasQueried_eq_true_iff [DecidableEq (GeneralScheme.SignatureCore vp prims.core)]
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
    (msg : List Byte) :
    log.wasQueried msg = true ↔ loggedSignatures log msg ≠ [] := by
  rw [QueryLog.wasQueried_eq_decide_mem_map_fst]
  simp only [decide_eq_true_eq, ne_eq, List.eq_nil_iff_forall_not_mem]
  constructor
  · intro h hall
    obtain ⟨⟨t, s⟩, hmem, ht⟩ := List.mem_map.mp h
    exact hall s (mem_loggedSignatures.mpr (ht ▸ hmem))
  · intro h
    by_contra hc
    exact h fun sig hsig => hc (List.mem_map.mpr ⟨⟨msg, sig⟩, mem_loggedSignatures.mp hsig, rfl⟩)

/-- A listed signature makes its message a queried one.

This is `SignatureAlg.wasQueried_eq_true_of_signingLogContains_eq_true` in this reading, and it is
what makes the library's queried/unqueried split exhaustive inside the strong-unforgeability
success event: the fourth combination, an unqueried message whose exact pair is nevertheless in the
log, is unreachable.  Through `wasQueried_eq_true_iff` the proof is `List.ne_nil_of_mem`.

*Transcript transport.* -/
theorem wasQueried_eq_true_of_mem_loggedSignatures
    [DecidableEq (GeneralScheme.SignatureCore vp prims.core)]
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)}
    {msg : List Byte} {sig : GeneralScheme.SignatureCore vp prims.core}
    (h : sig ∈ loggedSignatures log msg) : log.wasQueried msg = true :=
  (wasQueried_eq_true_iff log msg).mpr (List.ne_nil_of_mem h)

/-- **The same-message event, at the log alone.**  The left-hand side is the conjunction of the two
log-facing tests the same-message experiment returns; its third conjunct, that the signature
verifies, is not a statement about the log and does not appear.

*Transcript transport.* -/
theorem sameMessage_condition_iff [DecidableEq (GeneralScheme.SignatureCore vp prims.core)]
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
    (msg : List Byte) (sig : GeneralScheme.SignatureCore vp prims.core) :
    (log.wasQueried msg && !SignatureAlg.signingLogContains log msg sig) = true ↔
      loggedSignatures log msg ≠ [] ∧ sig ∉ loggedSignatures log msg := by
  rw [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    wasQueried_eq_true_iff, ← Bool.not_eq_true, ne_eq, signingLogContains_eq_true_iff]

/-- The signature the same-message event names: one the log returned for this message, which is not
the one at hand.

This is the object a rerandomization or signature-binding argument would start from; nothing here
does anything with it beyond exhibiting it.

*Transcript transport.* -/
theorem exists_ne_of_sameMessage [DecidableEq (GeneralScheme.SignatureCore vp prims.core)]
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)}
    {msg : List Byte} {sig : GeneralScheme.SignatureCore vp prims.core}
    (h : (log.wasQueried msg && !SignatureAlg.signingLogContains log msg sig) = true) :
    ∃ sig' ∈ loggedSignatures log msg, sig' ≠ sig := by
  obtain ⟨hne, hnot⟩ := (sameMessage_condition_iff log msg sig).mp h
  obtain ⟨sig', hsig'⟩ := List.exists_mem_of_ne_nil _ hne
  exact ⟨sig', hsig', fun he => hnot (he ▸ hsig')⟩

/-- An unqueried message was signed by nothing.

*Transcript transport.* -/
theorem loggedSignatures_eq_nil_of_not_wasQueried
    [DecidableEq (GeneralScheme.SignatureCore vp prims.core)]
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)} {msg : List Byte}
    (h : log.wasQueried msg = false) : loggedSignatures log msg = [] := by
  by_contra hc
  rw [(wasQueried_eq_true_iff log msg).mpr hc] at h
  exact Bool.noConfusion h

/-! ## The randomizers, and the transcript a reduction records -/

/-- The message randomizers of the signatures the log returned for one message.

Under FIPS 205's hedged signing these need not agree: `PRF_msg` reads a per-signature `opt_rand`, so
two signings of one message can produce two of them.  Under the deterministic variant, and under the
EasyCrypt development's message-keyed signer, they all agree.

*Transcript transport.* -/
def loggedRandomizers (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
    (msg : List Byte) : List prims.Y :=
  (loggedSignatures log msg).map fun sig => sig.randomness

/-- Unfolding equation for `loggedRandomizers`.  The body is not exposed, so this is what a consumer
that needs the `List.map` shape rewrites with.

*Transcript transport.* -/
theorem loggedRandomizers_eq
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core))
    (msg : List Byte) :
    loggedRandomizers log msg = (loggedSignatures log msg).map fun sig => sig.randomness := by rfl

/-- Membership at the randomizer level.  This is `List.mem_map` at that definition, named because
every branch condition below is written with it.

*Transcript transport.* -/
theorem mem_loggedRandomizers
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)}
    {msg : List Byte} {r : prims.Y} :
    r ∈ loggedRandomizers log msg ↔ ∃ sig ∈ loggedSignatures log msg, sig.randomness = r := by
  rw [loggedRandomizers_eq, List.mem_map]

/-- The signing log read as the pair transcript the `H_msg` game records: for each entry, the
randomizer of the signature that was returned and the message that was signed.

This is the whole log, not the part of it at one message; which message an entry carries is what
makes the transcript a record of *pairs*.

*Transcript transport.* -/
def logQueries (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) :
    ITSRTranscript prims.Y (List Byte) :=
  log.map fun e => (e.2.randomness, e.1)

/-- Unfolding equation for `logQueries`.  The body is not exposed, so this is what a consumer that
needs the `List.map` shape rewrites with.

*Transcript transport.* -/
theorem logQueries_eq
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) :
    logQueries log = log.map fun e => (e.2.randomness, e.1) := by rfl

/-- **Pair membership is per-message membership**, in both directions: the transcript contains the
pair `(r, msg)` exactly when some signature the log returned *for `msg`* carries the randomizer `r`.

Both directions are used, and the right-to-left one is what keeps the statements below from being
weakened to a condition on the whole log: a randomizer that occurs only at a different message
leaves this pair absent.

*Transcript transport.* -/
theorem mem_logQueries_iff
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)}
    {msg : List Byte} {r : prims.Y} :
    (r, msg) ∈ logQueries log ↔ r ∈ loggedRandomizers log msg := by
  rw [logQueries_eq, List.mem_map, mem_loggedRandomizers]
  constructor
  · rintro ⟨⟨t, s⟩, hmem, he⟩
    rw [Prod.mk.injEq] at he
    obtain ⟨hr, ht⟩ := he
    exact ⟨s, mem_loggedSignatures.mpr (ht ▸ hmem), hr⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨msg, s⟩, mem_loggedSignatures.mp hs, rfl⟩

/-- An unqueried message leaves every pair at it absent from the transcript, whatever randomizer the
pair carries.

*Transcript transport.* -/
theorem notMem_logQueries_of_not_wasQueried
    [DecidableEq (GeneralScheme.SignatureCore vp prims.core)]
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)} {msg : List Byte}
    (h : log.wasQueried msg = false) (r : prims.Y) : (r, msg) ∉ logQueries log := by
  rw [mem_logQueries_iff, loggedRandomizers_eq, loggedSignatures_eq_nil_of_not_wasQueried h]
  simp

/-! ## What the transcript gives the `H_msg` bridge

Every statement in this section shares one `pk`, and both the embedding and the candidate read
their public seed and published root off it.  That is the discipline
`HashSig.SLHDSA.Security.HmsgWitnesses` records for the widened hashed input: a consumer cannot
embed a transcript at one key pair and test a candidate at another without saying so. -/

/-- **The existential-unforgeability branch, where pair freshness is free.**  An unqueried message
leaves the candidate fresh at the embedded transcript for *every* randomizer, so the `H_msg` bridge
applies with nothing further to prove.

*Transcript transport.* -/
theorem notMem_embedTargets_of_not_wasQueried
    [DecidableEq (GeneralScheme.SignatureCore vp prims.core)] (pk : PublicKeyCore prims.core)
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)} {msg : List Byte}
    (h : log.wasQueried msg = false) (r : prims.Y) :
    (r, (⟨pk.pkSeed, pk.pkRoot, msg⟩ : HmsgITSRInput prims.PkSeed prims.Y)) ∉
      embedTargets prims pk.pkSeed pk.pkRoot (logQueries log) :=
  notMem_embedTargets_of_notMem pk.pkSeed pk.pkRoot (notMem_logQueries_of_not_wasQueried h r)

/-- **The residual's first branch.**  A randomizer that no signature returned for this message
carries leaves the candidate fresh at the embedded transcript, whatever else the log holds.

*Transcript transport.* -/
theorem notMem_embedTargets_of_notMem_loggedRandomizers (pk : PublicKeyCore prims.core)
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)} {msg : List Byte}
    {r : prims.Y} (h : r ∉ loggedRandomizers log msg) :
    (r, (⟨pk.pkSeed, pk.pkRoot, msg⟩ : HmsgITSRInput prims.PkSeed prims.Y)) ∉
      embedTargets prims pk.pkSeed pk.pkRoot (logQueries log) :=
  notMem_embedTargets_of_notMem pk.pkSeed pk.pkRoot fun hm => h (mem_logQueries_iff.mp hm)

/-- **The residual's second branch, at the transcript.**  A randomizer some signature returned for
this message carries makes the candidate one of the embedded targets.

*Transcript transport.* -/
theorem mem_embedTargets_of_mem_loggedRandomizers (pk : PublicKeyCore prims.core)
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)} {msg : List Byte}
    {r : prims.Y} (h : r ∈ loggedRandomizers log msg) :
    (r, (⟨pk.pkSeed, pk.pkRoot, msg⟩ : HmsgITSRInput prims.PkSeed prims.Y)) ∈
      embedTargets prims pk.pkSeed pk.pkRoot (logQueries log) :=
  (mem_embedTargets_iff pk.pkSeed pk.pkRoot (logQueries log) r msg).mpr (mem_logQueries_iff.mpr h)

/-- On the second branch the winning condition fails, and it fails on freshness.

Its other conjunct, coverage, is untouched — the candidate's indices are in fact all covered, by the
target the candidate itself is — so this is not a statement that the pair is far from winning; it is
a statement that the one thing the `H_msg` game asks for beyond coverage is exactly what a repeated
randomizer destroys.

*Transcript transport.* -/
theorem not_wins_of_mem_loggedRandomizers [SampleableType prims.Y] [DecidableEq prims.PkSeed]
    [DecidableEq prims.Y] (pk : PublicKeyCore prims.core)
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)} {msg : List Byte}
    {r : prims.Y} (h : r ∈ loggedRandomizers log msg) :
    ¬ (hmsgItsrProblem prims).Wins (embedTargets prims pk.pkSeed pk.pkRoot (logQueries log))
      (r, ⟨pk.pkSeed, pk.pkRoot, msg⟩) :=
  fun hw => hw.1 (mem_embedTargets_of_mem_loggedRandomizers pk h)

/-- On the second branch the first-uncovered-index extractor returns nothing either.

Together with the previous theorem this closes both alternatives of the `H_msg` bridge's dichotomy
on this branch: there is no win to report and no uncovered FORS leaf to hand the lane's extractor.

*Transcript transport.* -/
theorem findUncoveredIndex_eq_none_of_mem_loggedRandomizers [SampleableType prims.Y]
    (pk : PublicKeyCore prims.core)
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)} {msg : List Byte}
    {r : prims.Y} (h : r ∈ loggedRandomizers log msg) :
    findUncoveredIndex prims (embedTargets prims pk.pkSeed pk.pkRoot (logQueries log))
      (r, ⟨pk.pkSeed, pk.pkRoot, msg⟩) = none := by
  rw [findUncoveredIndex_eq_find?, List.find?_eq_none]
  intro i hi
  simp only [decide_eq_true_eq, not_not, ITSRProblem.targetIndexSet, List.mem_flatMap]
  exact ⟨_, mem_embedTargets_of_mem_loggedRandomizers pk h, hi⟩

/-- On the first branch the `H_msg` bridge's dichotomy applies unchanged.

This is `itsr_wins_or_uncovered` at the embedded transcript, with the freshness hypothesis supplied
by the branch condition.  It is the whole of what the residual buys a reduction.

*Transcript transport.* -/
theorem wins_or_uncovered_of_notMem_loggedRandomizers [SampleableType prims.Y]
    [DecidableEq prims.PkSeed] [DecidableEq prims.Y] (pk : PublicKeyCore prims.core)
    {log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)} {msg : List Byte}
    {r : prims.Y} (h : r ∉ loggedRandomizers log msg) :
    (hmsgItsrProblem prims).Wins (embedTargets prims pk.pkSeed pk.pkRoot (logQueries log))
        (r, ⟨pk.pkSeed, pk.pkRoot, msg⟩) ∨
      ∃ idx, findUncoveredIndex prims (embedTargets prims pk.pkSeed pk.pkRoot (logQueries log))
          (r, ⟨pk.pkSeed, pk.pkRoot, msg⟩) = some idx ∧
        idx ∈ (hmsgItsrProblem prims).indexSet (r, ⟨pk.pkSeed, pk.pkRoot, msg⟩) ∧
        idx ∉ (hmsgItsrProblem prims).targetIndexSet
          (embedTargets prims pk.pkSeed pk.pkRoot (logQueries log)) :=
  itsr_wins_or_uncovered _ _ (notMem_embedTargets_of_notMem_loggedRandomizers pk h)

/-! ## What two signatures with one randomizer share, and where they differ -/

/-- Two signatures with equal randomizers produce one digest split against one public key on one
message, hence one FORS instance address and one FORS message.

The public key is whatever the verifier was handed and the message is the forged one; neither is
constrained, and no signature is required to verify.

*Deterministic inclusion.* -/
theorem schemeParts_eq_of_randomizer_eq (msg : List Byte)
    (sig sig' : GeneralScheme.SignatureCore vp prims.core) (pk : PublicKeyCore prims.core)
    (h : sig.randomness = sig'.randomness) :
    schemeParts vp prims msg sig pk = schemeParts vp prims msg sig' pk := by
  rw [schemeParts_eq, schemeParts_eq, h]

/-- Two distinct signatures with equal randomizers differ in their FORS half or in their hypertree
half.

The disjunction is not exclusive and this says nothing about which half differs; the fixture
exhibits a pair for each.  It is stated submitted-first, as the lane's `tlCollision` and `fPreimage`
distinctness conjuncts are.

*Deterministic inclusion.* -/
theorem components_ne_of_ne_of_randomizer_eq
    {sig sig' : GeneralScheme.SignatureCore vp prims.core} (hne : sig ≠ sig')
    (hr : sig.randomness = sig'.randomness) :
    sig.fors ≠ sig'.fors ∨ sig.hypertree ≠ sig'.hypertree := by
  by_contra hc
  push Not at hc
  obtain ⟨hf, hh⟩ := hc
  exact hne (by cases sig; cases sig'; simp_all)

/-! ## The residual -/

/-- **The deterministic strong-unforgeability residual.**  A message and a signature whose exact
pair the log does not contain either name an `H_msg` input the recorded transcript does not contain
— and then the bridge of `HashSig.SLHDSA.Security.HmsgWitnesses` applies to them unchanged — or come
with a signature the log returned for that same message which carries the same randomizer, differs
from this one, splits to the same digest against the same public key, and differs from it in its
FORS half or in its hypertree half.

The hypothesis is the strong-unforgeability experiment's own freshness condition and nothing else.
In particular the queried/unqueried split of the library's partition identity is not taken here: it
is not needed for the dichotomy, and its unqueried half is the case in which the second branch is
empty, by `notMem_logQueries_of_not_wasQueried`.  What that split does add is that the second branch
occurs only inside the same-message event, by `wasQueried_eq_true_of_mem_loggedSignatures`.

Nothing is claimed about the second branch beyond the four facts listed.  Whether it can be
extracted from at all is a question about a witness family this lane has not built, and
`not_wins_of_mem_loggedRandomizers` and `findUncoveredIndex_eq_none_of_mem_loggedRandomizers` say
that the family it has built cannot be pointed at it.

*Transcript transport.* -/
theorem itsrFresh_or_sameRandomizer [DecidableEq (GeneralScheme.SignatureCore vp prims.core)]
    (log : QueryLog (List Byte →ₒ GeneralScheme.SignatureCore vp prims.core)) (msg : List Byte)
    (sig : GeneralScheme.SignatureCore vp prims.core) (pk : PublicKeyCore prims.core)
    (hfresh : SignatureAlg.signingLogContains log msg sig = false) :
    (sig.randomness, (⟨pk.pkSeed, pk.pkRoot, msg⟩ : HmsgITSRInput prims.PkSeed prims.Y)) ∉
        embedTargets prims pk.pkSeed pk.pkRoot (logQueries log) ∨
      ∃ sig' ∈ loggedSignatures log msg, sig'.randomness = sig.randomness ∧ sig' ≠ sig ∧
        schemeParts vp prims msg sig pk = schemeParts vp prims msg sig' pk ∧
        (sig.fors ≠ sig'.fors ∨ sig.hypertree ≠ sig'.hypertree) := by
  by_cases h : sig.randomness ∈ loggedRandomizers log msg
  · obtain ⟨sig', hmem, hr⟩ := mem_loggedRandomizers.mp h
    have hnot : sig ∉ loggedSignatures log msg := fun hc =>
      Bool.noConfusion (hfresh ▸ (signingLogContains_eq_true_iff log msg sig).mpr hc)
    have hne : sig' ≠ sig := fun he => hnot (he ▸ hmem)
    exact Or.inr ⟨sig', hmem, hr, hne,
      schemeParts_eq_of_randomizer_eq msg sig sig' pk hr.symm,
      components_ne_of_ne_of_randomizer_eq (Ne.symm hne) hr.symm⟩
  · exact Or.inl (notMem_embedTargets_of_notMem_loggedRandomizers pk h)

end SLHDSA.Security
