/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CanonicalGames
public import HashSig.SLHDSA.Security.ReachableTargets
public import HashSig.SLHDSA.WotsInjectivity

/-!
# WOTS+ chain witnesses

Deterministic translations of a WOTS+ public-key match into a concrete witness against one named
WOTS+ component hash: an `F`-preimage or an `F`-collision at an exact `WOTS_HASH` chain-step
address, or a `T_len` second preimage at an exact `WOTS_PK` compression address.  The case
analysis is the Lean counterpart of the `is_chwcoll`/`is_chwpre` split of the EasyCrypt SPHINCS+
development (`WOTS_TW_ES.ec`), with the axiom `two_encodings` replaced by the merged Lean theorem
`chainStepsCore_two_encodings`.

## What is proved, and what is not

Every *deterministic-inclusion* statement below is about signature data: a primitive bundle, a
public seed, a structural address, two messages, and two signatures.  One of them,
`wotsPkFromSig_cases`, additionally names the honest secret seed, because the honest public key
it starts from is the one `wotsPkGen` produces.  The *transcript-transport* statements are about
a role ledger over a `ValidatedParams`; they mention no signature at all.  Nothing here
constructs an adversary, states an advantage, performs a game hop, or claims that any honest
execution queried the honest value a witness attacks.  In particular a witness lemma is **not** a
reduction: that the game's target was committed before the forgery was seen is a
simulation-fidelity obligation of the later program-level slice, not a fact established here.  The
undetectability role has no witness content at all and is deliberately absent — undetectability
pays for a distributional hybrid, not for an extraction.

## Labels

*Deterministic inclusion* — a statement whose only free objects are `prims`, seeds, addresses and
signature data:

* `chain_diverge`, `findChainDivergence`, `findChainDivergence_sound`,
  `findChainDivergence_isSome_of_ne`;
* `chainPair_cases`;
* `wotsPkFromSigTops_cases`, `wotsPkFromSig_cases`;
* `WotsWitness`, `WotsWitness.Valid` and its three unfolding equations
  `WotsWitness.valid_tlCollision`, `WotsWitness.valid_fPreimage`, `WotsWitness.valid_fCollision`;
* `findWotsChainWitness`, `findWotsChainWitness_sound`, `findWotsChainWitness_isSome_of_lt`,
  `findWotsWitness`, `findWotsWitness_sound`, `findWotsWitness_isSome`;
* the three game-shape bridges `wotsWitness_valid_fPreimage_eval`,
  `wotsWitness_valid_fCollision_eval`, `wotsWitness_valid_tlCollision_eval`.

*Transcript transport* — a statement about a role ledger of `HashSig.SLHDSA.Security`:

* `mem_wotsStepAddresses_of_lt`, `wotsPreimageAdrs_mem_wotsStepAddresses`,
  `wotsPreimageAdrs_mem_optionalWotsAddresses`;
* `wotsStepAdrsKey_injective`, `wotsOptionalStepAdrsKey_injective`, `wotsPkAdrsKey_injective`.

The `T_len` witness address is `wotsPkAdrs (wotsInstanceAdrs pos)`, which `mem_wotsPkAddresses`
already lists in the `wotsTl` ledger; that lemma is used directly rather than restated.

The three encoded-distinctness lemmas consume `EncodedTargetLedgerConditions` rather than assuming a
fresh injectivity hypothesis, so a concrete profile discharges them through
`approvedEncodedTargetLedgerConditions`; the SHA-2 zero fallback is therefore never treated as
unreachable.

## The case analysis

Write `msg` for the forged message and `msg'` for the honestly signed one, `sig` and `sig'` for the
corresponding signatures, and `a = chainStepsCore … msg i`, `b = chainStepsCore … msg' i` for the
step counts of chain `i`.  `chainStepsCore_two_encodings` supplies an index with `a < b`, which is
the swapped use `two_encodings m' m` the EasyCrypt proof makes in `nhchwcoll_hchwpre`
(`WOTS_TW_ES.ec:1299`).  At such an index the forged chain must climb from `a` to the honest
digit `b` and beyond; advancing it to `b` either lands on the honest revealed value `sig'[i]` — an
`F`-preimage at hash address `b - 1`, matching `extr_pre` (`WOTS_TW_ES.ec:656`); under an honest
signer the preimage of `sig'[i]` is the step-`(b - 1)` chain value, which the signature does not
reveal, but that is motivation and is not proved here — or it does not, and the two chains, which
share the endpoint at step `w - 1`, must first collide at some step `t` with `b ≤ t < w - 1`,
matching `extr_coll_l` /
`extr_coll_r` (`:628`, `:633`).  One level up, a signature that recovers the honest public key
either recovers different chain ends, giving a `T_len` second preimage at `wotsPkAdrs adrs`
(the `valid_TCRPKCO` branch of `FL_SL_XMSS_MT_ES.ec:3270`), or recovers exactly the honest chain
ends and the chain analysis applies.

## References

- NIST FIPS 205, §5 (Algorithms 5–8)
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`WOTS_TW_ES.ec`, `FL_SL_XMSS_MT_ES.ec`)
-/

public section

namespace SLHDSA.Security

open CanonicalGames

variable {p : Params}

/-! ## Divergence of two chains with a common endpoint

The chain-level core: two chain values started at the same hash index that reach the same value
after `n` steps are either equal or first differ at a step whose `F` images already agree. -/

/-- Two chains from `u` and `v` at hash index `i` that agree after `n` steps either start from the
same value, or there is a step `j < n` at which they still differ while their `F` images at hash
address `i + j` already agree — a collision of `F` at `adrs.setHashAddress (i + j)`.

*Deterministic inclusion.*  The existence statement is the Lean counterpart of `hchwcoll_hcoll`
(`WOTS_TW_ES.ec:1179-1197`); `is_coll` (`:611`) and `find_collidx_l` (`:620`) are the search
operators that locate the step, and it is `findChainDivergence` below that plays their role. -/
theorem chain_diverge (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (u v : prims.Y) (i n : ℕ)
    (hend : chain prims pkSeed adrs u i n = chain prims pkSeed adrs v i n) :
    u = v ∨ ∃ j, j < n ∧
      chain prims pkSeed adrs u i j ≠ chain prims pkSeed adrs v i j ∧
      prims.F pkSeed (adrs.setHashAddress (i + j)) (chain prims pkSeed adrs u i j) =
        prims.F pkSeed (adrs.setHashAddress (i + j)) (chain prims pkSeed adrs v i j) := by
  induction n with
  | zero => exact Or.inl (by simpa using hend)
  | succ n ih =>
      by_cases hn : chain prims pkSeed adrs u i n = chain prims pkSeed adrs v i n
      · rcases ih hn with h | ⟨j, hj, hne, hcoll⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, Nat.lt_succ_of_lt hj, hne, hcoll⟩
      · exact Or.inr ⟨n, Nat.lt_succ_self n, hn, by simpa only [chain_succ] using hend⟩

/-- The first step below `n` at which the two chains from `u` and `v` still differ while their
successors already agree.  Computable, so a reduction can build the witness rather than know one
exists.  The EasyCrypt counterpart `find_collidx_l` (`WOTS_TW_ES.ec:620`) instead searches for the
first step at which the two chains agree and reads the collision off the step before it. -/
def findChainDivergence (prims : Primitives p) [DecidableEq prims.Y] (pkSeed : prims.PkSeed)
    (adrs : Adrs) (u v : prims.Y) (i n : ℕ) : Option ℕ :=
  (List.range n).find? fun j =>
    decide (chain prims pkSeed adrs u i j ≠ chain prims pkSeed adrs v i j ∧
      chain prims pkSeed adrs u i (j + 1) = chain prims pkSeed adrs v i (j + 1))

/-- Whatever `findChainDivergence` returns is a genuine `F`-collision below `n`: the two chain
values at that step differ and their `F` images at the step's hash address agree.

*Deterministic inclusion.*  No endpoint hypothesis is needed: the search itself checks both
conditions, so its output is a collision whether or not the two chains ever converge. -/
theorem findChainDivergence_sound (prims : Primitives p) [DecidableEq prims.Y]
    (pkSeed : prims.PkSeed) (adrs : Adrs) (u v : prims.Y) (i n j : ℕ)
    (hj : findChainDivergence prims pkSeed adrs u v i n = some j) :
    j < n ∧ chain prims pkSeed adrs u i j ≠ chain prims pkSeed adrs v i j ∧
      prims.F pkSeed (adrs.setHashAddress (i + j)) (chain prims pkSeed adrs u i j) =
        prims.F pkSeed (adrs.setHashAddress (i + j)) (chain prims pkSeed adrs v i j) := by
  have hmem := List.mem_of_find?_eq_some hj
  have hsat := List.find?_some hj
  rw [decide_eq_true_eq] at hsat
  refine ⟨List.mem_range.mp hmem, hsat.1, ?_⟩
  simpa only [chain_succ] using hsat.2

/-- The search succeeds whenever the two chains start from different values and reach the same
value after `n` steps: the divergence step exists by `chain_diverge`.

*Deterministic inclusion.* -/
theorem findChainDivergence_isSome_of_ne (prims : Primitives p) [DecidableEq prims.Y]
    (pkSeed : prims.PkSeed) (adrs : Adrs) (u v : prims.Y) (i n : ℕ) (hne : u ≠ v)
    (hend : chain prims pkSeed adrs u i n = chain prims pkSeed adrs v i n) :
    (findChainDivergence prims pkSeed adrs u v i n).isSome := by
  rw [Option.isSome_iff_ne_none]
  intro hnone
  rw [findChainDivergence, List.find?_eq_none] at hnone
  obtain ⟨j, hj, hjne, hjcoll⟩ := (chain_diverge prims pkSeed adrs u v i n hend).resolve_left hne
  exact hnone j (List.mem_range.mpr hj)
    (decide_eq_true ⟨hjne, by simpa only [chain_succ] using hjcoll⟩)

/-! ## One chain pair, two digits

The dichotomy at a single WOTS+ chain: the forged chain starts at the strictly smaller digit `a`,
the honest chain at `b`, and both are iterated to step `w - 1`. -/

/-- **Chain dichotomy.**  If a forged chain value at digit `a` and an honest chain value at the
strictly larger digit `b ≤ w - 1` reach the same step-`(w - 1)` endpoint, then either advancing the
forged value to digit `b` lands exactly on the honest value — exhibiting an `F`-preimage of
`honest` at hash address `b - 1` — or the two chains differ at some step `t` with `b ≤ t < w - 1`
while their `F` images at hash address `t` agree, exhibiting an `F`-collision there.

*Deterministic inclusion.*  This fuses three EasyCrypt steps at one chain.  `nhchwcoll_hchwpre`
(`WOTS_TW_ES.ec:1299`) supplies the split, but carries no endpoint hypothesis and its second
outcome `is_chwcoll` (`:595`) is only the inequality `cf … <> sig[i]`; `hchwcoll_hcoll`
(`:1179-1197`) and `collision_extraction` (`:1249-1291`) are what turn that inequality into a
collision, and the endpoint equality they need is what `hend` carries here.  The outcomes are
`is_chwpre` (`:640`) and the extracted collision, with the extractors `extr_pre` (`:656`) and
`extr_coll_l`/`extr_coll_r` (`:628`, `:633`).  The lemma is exhaustive: the two branches are the
two sides of a decision on whether the advanced forged value equals the honest one. -/
theorem chainPair_cases (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (forged honest : prims.Y) (a b : ℕ) (hab : a < b) (hb : b ≤ p.w - 1)
    (hend : chain prims pkSeed adrs forged a (p.w - 1 - a) =
      chain prims pkSeed adrs honest b (p.w - 1 - b)) :
    prims.F pkSeed (adrs.setHashAddress (b - 1))
        (chain prims pkSeed adrs forged a (b - 1 - a)) = honest ∨
      ∃ t, b ≤ t ∧ t < p.w - 1 ∧
        chain prims pkSeed adrs forged a (t - a) ≠ chain prims pkSeed adrs honest b (t - b) ∧
        prims.F pkSeed (adrs.setHashAddress t) (chain prims pkSeed adrs forged a (t - a)) =
          prims.F pkSeed (adrs.setHashAddress t) (chain prims pkSeed adrs honest b (t - b)) := by
  have hstep : ∀ j : ℕ,
      chain prims pkSeed adrs (chain prims pkSeed adrs forged a (b - a)) b j =
        chain prims pkSeed adrs forged a (b - a + j) := by
    intro j
    have h := chain_compose prims pkSeed adrs forged a (b - a) j
    rwa [show a + (b - a) = b by omega] at h
  have hcomp : chain prims pkSeed adrs (chain prims pkSeed adrs forged a (b - a)) b (p.w - 1 - b) =
      chain prims pkSeed adrs honest b (p.w - 1 - b) := by
    rw [hstep, show b - a + (p.w - 1 - b) = p.w - 1 - a by omega, hend]
  rcases chain_diverge prims pkSeed adrs (chain prims pkSeed adrs forged a (b - a)) honest b
    (p.w - 1 - b) hcomp with heq | ⟨j, hj, hjne, hjcoll⟩
  · refine Or.inl ?_
    rw [show b - a = (b - 1 - a) + 1 by omega, chain_succ,
      show a + (b - 1 - a) = b - 1 by omega] at heq
    exact heq
  · have harith : ∀ q : ℕ, q = b + j → q - a = b - a + j ∧ q - b = j := by omega
    obtain ⟨hleft, hright⟩ := harith (b + j) rfl
    refine Or.inr ⟨b + j, Nat.le_add_right b j, by omega, ?_, ?_⟩ <;>
      rw [hleft, hright, ← hstep j] <;> assumption

/-! ## One WOTS+ instance

`chainStepsCore_two_encodings` supplies the chain index at which the forged encoding's digit is
strictly smaller than the honest one; `chainPair_cases` then splits that chain. -/

/-- **WOTS+ chain-end dichotomy.**  If two signatures on distinct messages recover the same
`len` chain ends at `adrs`, then some chain index `i` has `a < b`, where `a` is the step count of
`msg` and `b` that of `msg'`, and that chain carries either an `F`-preimage of `sig'[i]` at hash
address `b - 1`, or an `F`-collision at some hash address `t` with `b ≤ t < w - 1`.

The witnessing index and the digit inequality come from `chainStepsCore_two_encodings`, the Lean
proof of what `WOTS_TW_ES.ec` assumes as the axiom `two_encodings` (`:572`); the branch is
`chainPair_cases`.

*Deterministic inclusion.* -/
theorem wotsPkFromSigTops_cases (valid : p.Valid) (prims : Primitives p)
    (laws : prims.core.ByteLaws) (sig sig' : WotsSig p prims.core) (msg msg' : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) (hne : msg ≠ msg')
    (htops : wotsPkFromSigTops prims sig msg pk adrs =
      wotsPkFromSigTops prims sig' msg' pk adrs) :
    ∃ i : Fin p.len,
      chainStepsCore prims.core msg i.val < chainStepsCore prims.core msg' i.val ∧
      (prims.F pk ((wotsChainAdrs adrs i.val).setHashAddress
              (chainStepsCore prims.core msg' i.val - 1))
            (chain prims pk (wotsChainAdrs adrs i.val) sig[i.val]
              (chainStepsCore prims.core msg i.val)
              (chainStepsCore prims.core msg' i.val - 1 - chainStepsCore prims.core msg i.val)) =
          sig'[i.val] ∨
        ∃ t, chainStepsCore prims.core msg' i.val ≤ t ∧ t < p.w - 1 ∧
          chain prims pk (wotsChainAdrs adrs i.val) sig[i.val]
              (chainStepsCore prims.core msg i.val) (t - chainStepsCore prims.core msg i.val) ≠
            chain prims pk (wotsChainAdrs adrs i.val) sig'[i.val]
              (chainStepsCore prims.core msg' i.val) (t - chainStepsCore prims.core msg' i.val) ∧
          prims.F pk ((wotsChainAdrs adrs i.val).setHashAddress t)
              (chain prims pk (wotsChainAdrs adrs i.val) sig[i.val]
                (chainStepsCore prims.core msg i.val)
                (t - chainStepsCore prims.core msg i.val)) =
            prims.F pk ((wotsChainAdrs adrs i.val).setHashAddress t)
              (chain prims pk (wotsChainAdrs adrs i.val) sig'[i.val]
                (chainStepsCore prims.core msg' i.val)
                (t - chainStepsCore prims.core msg' i.val))) := by
  obtain ⟨i, hi, hlt⟩ := chainStepsCore_two_encodings (core := prims.core) valid laws hne
  refine ⟨⟨i, hi⟩, hlt, ?_⟩
  have hend : chain prims pk (wotsChainAdrs adrs i) sig[i]
        (chainStepsCore prims.core msg i) (p.w - 1 - chainStepsCore prims.core msg i) =
      chain prims pk (wotsChainAdrs adrs i) sig'[i]
        (chainStepsCore prims.core msg' i) (p.w - 1 - chainStepsCore prims.core msg' i) := by
    have := congrArg (fun v : Vector prims.Y p.len => v[i]) htops
    simpa only [wotsPkFromSigTops_eq_ofFn, Vector.getElem_ofFn] using this
  exact chainPair_cases prims pk (wotsChainAdrs adrs i) sig[i] sig'[i]
    (chainStepsCore prims.core msg i) (chainStepsCore prims.core msg' i) hlt
    (chainStepsCore_le prims.core msg' i) hend

/-- **WOTS+ instance trichotomy.**  A signature on `msg` that recovers `wotsPkGen prims sk pk adrs`
yields, for any second message `msg' ≠ msg`, one of three witnesses: a `T_len` second preimage of
the honest chain ends at `wotsPkAdrs adrs`, an `F`-preimage of the honest signature's chain value
`(wotsSign prims msg' sk pk adrs)[i]`, or an `F`-collision at a chain-step address of chain `i`.

The proof splits on whether the recovered chain ends equal the honest ones.  They do not: the two
`T_len` inputs then differ while their images agree, which is the first disjunct.  They do: the
signature on `msg'` recovers the same chain ends by `wotsPkFromSigTops_wotsSign`, and
`wotsPkFromSigTops_cases` applies.  The three outcomes are the single-instance reading of the
`valid_TCRPKCO`/`valid_WOTSTWES` split of `FL_SL_XMSS_MT_ES.ec:3270`.

*Deterministic inclusion.* -/
theorem wotsPkFromSig_cases (valid : p.Valid) (prims : Primitives p)
    (laws : prims.core.ByteLaws) (sig : WotsSig p prims.core) (msg msg' : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (hne : msg ≠ msg')
    (hpk : wotsPkFromSig prims sig msg pk adrs = wotsPkGen prims sk pk adrs) :
    (wotsPkFromSigTops prims sig msg pk adrs ≠ wotsPkGenTops prims sk pk adrs ∧
        prims.Tl pk (wotsPkAdrs adrs) (wotsPkFromSigTops prims sig msg pk adrs).toList =
          prims.Tl pk (wotsPkAdrs adrs) (wotsPkGenTops prims sk pk adrs).toList) ∨
      ∃ i : Fin p.len,
        chainStepsCore prims.core msg i.val < chainStepsCore prims.core msg' i.val ∧
        (prims.F pk ((wotsChainAdrs adrs i.val).setHashAddress
                (chainStepsCore prims.core msg' i.val - 1))
              (chain prims pk (wotsChainAdrs adrs i.val) sig[i.val]
                (chainStepsCore prims.core msg i.val)
                (chainStepsCore prims.core msg' i.val - 1 - chainStepsCore prims.core msg i.val)) =
            (wotsSign prims msg' sk pk adrs)[i.val] ∨
          ∃ t, chainStepsCore prims.core msg' i.val ≤ t ∧ t < p.w - 1 ∧
            chain prims pk (wotsChainAdrs adrs i.val) sig[i.val]
                (chainStepsCore prims.core msg i.val) (t - chainStepsCore prims.core msg i.val) ≠
              chain prims pk (wotsChainAdrs adrs i.val) (wotsSign prims msg' sk pk adrs)[i.val]
                (chainStepsCore prims.core msg' i.val)
                (t - chainStepsCore prims.core msg' i.val) ∧
            prims.F pk ((wotsChainAdrs adrs i.val).setHashAddress t)
                (chain prims pk (wotsChainAdrs adrs i.val) sig[i.val]
                  (chainStepsCore prims.core msg i.val)
                  (t - chainStepsCore prims.core msg i.val)) =
              prims.F pk ((wotsChainAdrs adrs i.val).setHashAddress t)
                (chain prims pk (wotsChainAdrs adrs i.val) (wotsSign prims msg' sk pk adrs)[i.val]
                  (chainStepsCore prims.core msg' i.val)
                  (t - chainStepsCore prims.core msg' i.val))) := by
  have hhonest : wotsPkFromSigTops prims (wotsSign prims msg' sk pk adrs) msg' pk adrs =
      wotsPkGenTops prims sk pk adrs := wotsPkFromSigTops_wotsSign prims msg' sk pk adrs
  by_cases htops : wotsPkFromSigTops prims sig msg pk adrs = wotsPkGenTops prims sk pk adrs
  · refine Or.inr ?_
    have := wotsPkFromSigTops_cases valid prims laws sig (wotsSign prims msg' sk pk adrs) msg msg'
      pk adrs hne (htops.trans hhonest.symm)
    exact this
  · refine Or.inl ⟨htops, ?_⟩
    rw [wotsPkFromSig_eq_tl, wotsPkGen_eq_tl] at hpk
    exact hpk

/-! ## The extracted witness

`WotsWitness` packages the three outcomes as the data a reduction submits: one value, together
with — for the two chain branches — the chain index and hash-address step that name the tweak it is
submitted against.  The `T_len` tweak is named by `adrs` alone, so `tlCollision` carries the value
and nothing else.  Every honest object a witness attacks is an argument of `WotsWitness.Valid` and
never a constructor field — the chain-end vector `honestTops` for the `T_len` branch, and for the
two chain branches the honest signature `honestSig` together with the message `honestMsg` it
signs, from which `Valid` *computes* the honest chain value at the named step.

That computation is the identification a source-final-validity game needs: its winning condition
compares the submitted value against the challenge *recorded* at the named target, so a pair of
arbitrary distinct values with equal images is not a win.  `WotsWitness.Valid` therefore carries
the hash-value half of that winning condition — the distinctness and the equal images, against a
partner the predicate names rather than quantifies over — together with the step bounds that place
the address in a role ledger, and nothing beyond that.  It does not assert that the honest object
was recorded as a game target, and it says nothing about the rest of a transcript, both of which
are program-level obligations of the reduction. -/

/-- A witness against one WOTS+ component hash at a fixed base address.

Each constructor carries only the value a reduction submits, together with, for the two chain
branches, the chain index and hash-address step that name the tweak; the `T_len` tweak is named by
`adrs`, so `tlCollision` carries neither.  Every honest object a witness attacks is supplied to
`WotsWitness.Valid`, which reads the attacked chain value off the honest signature. -/
inductive WotsWitness (p : Params) (prims : Primitives p) where
  /-- A second preimage of the honest chain-end vector under `T_len` at `wotsPkAdrs adrs`. -/
  | tlCollision (recovered : Vector prims.Y p.len)
  /-- An `F`-preimage of the honest revealed value of chain `chainIdx`, at hash-address `step`. -/
  | fPreimage (chainIdx : Fin p.len) (step : ℕ) (value : prims.Y)
  /-- An `F`-collision at hash-address `step` of chain `chainIdx`.  `value` is the submitted
  colliding value; the honest chain value it collides with is not carried here but computed by
  `WotsWitness.Valid` from the honest signature and message. -/
  | fCollision (chainIdx : Fin p.len) (step : ℕ) (value : prims.Y)

/-- The winning condition each witness asserts, against the honest chain ends `honestTops`, the
honest signature `honestSig`, and the message `honestMsg` that `honestSig` signs, at base address
`adrs`.

Write `b` for `chainStepsCore prims.core honestMsg chainIdx`, the hash index at which the honest
signature reveals chain `chainIdx`.  Then:

* `tlCollision recovered` asserts a `T_len` second preimage of `honestTops` at `wotsPkAdrs adrs`;
* `fPreimage chainIdx step value` asserts an `F`-preimage of the honest revealed value
  `honestSig[chainIdx]` at hash-address `step`, and pins `step + 1 = b` — the one address at
  which an honest signer applied `F` to reach `honestSig[chainIdx]`;
* `fCollision chainIdx step value` asserts an `F`-collision at a hash-address `step` in
  `[b, w - 2]` between `value` and
  `chain prims pk (wotsChainAdrs adrs chainIdx) honestSig[chainIdx] b (step - b)`, the honest
  chain value at that step.  Advancing the revealed element is how the honest value at a step at
  or above `b` is named without the secret seed: when `honestSig` is an honest signature on
  `honestMsg`, `chain_compose` identifies it with the value the signer hashed at `step`, which is
  motivation rather than a hypothesis — nothing here requires `honestSig` to be honest.

Both chain cases pin the hash-address step below `w - 1`, which is what places their address in
the `wotsFTcr` role ledger (`mem_wotsStepAddresses_of_lt`).  In the `fPreimage` case that bound is
redundant — `step + 1 = b` and `chainStepsCore_le` already give it — and is kept so that a consumer
rewriting with `valid_fPreimage` reaches the ledger lemma without re-deriving anything.

This is a statement about hash values only.  It does not say that `honestTops`,
`honestSig[chainIdx]`, or the computed chain value was committed as a game target, nor that any
execution queried them. -/
def WotsWitness.Valid {p : Params} {prims : Primitives p} (pk : prims.PkSeed) (adrs : Adrs)
    (honestTops : Vector prims.Y p.len) (honestSig : WotsSig p prims.core) (honestMsg : prims.Y) :
    WotsWitness p prims → Prop
  | .tlCollision recovered =>
      recovered ≠ honestTops ∧
        prims.Tl pk (wotsPkAdrs adrs) recovered.toList =
          prims.Tl pk (wotsPkAdrs adrs) honestTops.toList
  | .fPreimage i step value =>
      step < p.w - 1 ∧ step + 1 = chainStepsCore prims.core honestMsg i.val ∧
        prims.F pk ((wotsChainAdrs adrs i.val).setHashAddress step) value = honestSig[i.val]
  | .fCollision i step value =>
      step < p.w - 1 ∧ chainStepsCore prims.core honestMsg i.val ≤ step ∧
        value ≠ chain prims pk (wotsChainAdrs adrs i.val) honestSig[i.val]
            (chainStepsCore prims.core honestMsg i.val)
            (step - chainStepsCore prims.core honestMsg i.val) ∧
        prims.F pk ((wotsChainAdrs adrs i.val).setHashAddress step) value =
          prims.F pk ((wotsChainAdrs adrs i.val).setHashAddress step)
            (chain prims pk (wotsChainAdrs adrs i.val) honestSig[i.val]
              (chainStepsCore prims.core honestMsg i.val)
              (step - chainStepsCore prims.core honestMsg i.val))

/-- Unfolding equation for the `T_len` branch of `WotsWitness.Valid`. -/
@[simp] theorem WotsWitness.valid_tlCollision {prims : Primitives p} (pk : prims.PkSeed)
    (adrs : Adrs) (honestTops : Vector prims.Y p.len) (honestSig : WotsSig p prims.core)
    (honestMsg : prims.Y) (recovered : Vector prims.Y p.len) :
    (WotsWitness.tlCollision recovered).Valid pk adrs honestTops honestSig honestMsg ↔
      recovered ≠ honestTops ∧
        prims.Tl pk (wotsPkAdrs adrs) recovered.toList =
          prims.Tl pk (wotsPkAdrs adrs) honestTops.toList := Iff.rfl

/-- Unfolding equation for the `F`-preimage branch of `WotsWitness.Valid`. -/
@[simp] theorem WotsWitness.valid_fPreimage {prims : Primitives p} (pk : prims.PkSeed)
    (adrs : Adrs) (honestTops : Vector prims.Y p.len) (honestSig : WotsSig p prims.core)
    (honestMsg : prims.Y) (i : Fin p.len) (step : ℕ) (value : prims.Y) :
    (WotsWitness.fPreimage i step value).Valid pk adrs honestTops honestSig honestMsg ↔
      step < p.w - 1 ∧ step + 1 = chainStepsCore prims.core honestMsg i.val ∧
        prims.F pk ((wotsChainAdrs adrs i.val).setHashAddress step) value =
          honestSig[i.val] := Iff.rfl

/-- Unfolding equation for the `F`-collision branch of `WotsWitness.Valid`.  The second value is
the honest chain value at `step`, read off `honestSig` rather than supplied by the witness. -/
@[simp] theorem WotsWitness.valid_fCollision {prims : Primitives p} (pk : prims.PkSeed)
    (adrs : Adrs) (honestTops : Vector prims.Y p.len) (honestSig : WotsSig p prims.core)
    (honestMsg : prims.Y) (i : Fin p.len) (step : ℕ) (value : prims.Y) :
    (WotsWitness.fCollision i step value).Valid pk adrs honestTops honestSig honestMsg ↔
      step < p.w - 1 ∧ chainStepsCore prims.core honestMsg i.val ≤ step ∧
        value ≠ chain prims pk (wotsChainAdrs adrs i.val) honestSig[i.val]
            (chainStepsCore prims.core honestMsg i.val)
            (step - chainStepsCore prims.core honestMsg i.val) ∧
        prims.F pk ((wotsChainAdrs adrs i.val).setHashAddress step) value =
          prims.F pk ((wotsChainAdrs adrs i.val).setHashAddress step)
            (chain prims pk (wotsChainAdrs adrs i.val) honestSig[i.val]
              (chainStepsCore prims.core honestMsg i.val)
              (step - chainStepsCore prims.core honestMsg i.val)) := Iff.rfl

/-- Search one WOTS+ chain for a witness: nothing unless the forged step count `a` is strictly
below the honest step count `b`, then the `F`-preimage if advancing the forged value to digit `b`
lands on the honest revealed value, and otherwise the first `F`-collision at or above `b`. -/
def findWotsChainWitness (prims : Primitives p) [DecidableEq prims.Y] (sig : WotsSig p prims.core)
    (msg : prims.Y) (sig' : WotsSig p prims.core) (msg' : prims.Y) (pk : prims.PkSeed)
    (adrs : Adrs) (i : Fin p.len) : Option (WotsWitness p prims) :=
  let a := chainStepsCore prims.core msg i.val
  let b := chainStepsCore prims.core msg' i.val
  let chAdrs := wotsChainAdrs adrs i.val
  if a < b then
    let advanced := chain prims pk chAdrs sig[i.val] a (b - a)
    if advanced = sig'[i.val] then
      some (.fPreimage i (b - 1) (chain prims pk chAdrs sig[i.val] a (b - 1 - a)))
    else
      (findChainDivergence prims pk chAdrs advanced sig'[i.val] b (p.w - 1 - b)).map fun j =>
        .fCollision i (b + j) (chain prims pk chAdrs advanced b j)
  else none

/-- Compute a WOTS+ witness from a forged signature on `msg` and an honest signature on `msg'` at
the same base address: the recovered chain-end vector when it differs from the honest one — a
`T_len` second preimage exactly when the two recovered public keys agree — and otherwise the first
chain that yields an `F`-preimage or an `F`-collision.

The branch is decided by the chain ends alone, not by the two public keys.  On a forgery whose
recovered public key differs this therefore still returns a `tlCollision`, and that witness is
*not* valid; ruling it out is exactly what `findWotsWitness_sound`'s public-key hypothesis does,
and the malformed-forgery canary of `HashSigTest.SLHDSA.WotsWitnesses` exercises the gap.  The
split is deliberate: a caller reaching this point has already checked that the forgery verifies,
and testing the compression again here would move that hypothesis onto
`findWotsWitness_isSome`, which is otherwise free of it. -/
def findWotsWitness (prims : Primitives p) [DecidableEq prims.Y] (sig : WotsSig p prims.core)
    (msg : prims.Y) (sig' : WotsSig p prims.core) (msg' : prims.Y) (pk : prims.PkSeed)
    (adrs : Adrs) : Option (WotsWitness p prims) :=
  if wotsPkFromSigTops prims sig msg pk adrs = wotsPkFromSigTops prims sig' msg' pk adrs then
    (List.finRange p.len).findSome? (findWotsChainWitness prims sig msg sig' msg' pk adrs)
  else
    some (.tlCollision (wotsPkFromSigTops prims sig msg pk adrs))

/-- Whatever `findWotsChainWitness` returns satisfies `WotsWitness.Valid` against the honest
signature `sig'` and the message `msg'` it signs.  This search never returns the `T_len`
constructor, so it needs no public-key hypothesis, and the `honestTops` argument of `Valid` is
inert here — but `honestSig` and `honestMsg` are not: the `fPreimage` step and the `fCollision`
partner are both fixed by them, which is what makes the returned witness an attack on a named
honest value rather than on an arbitrary one.

*Deterministic inclusion.* -/
theorem findWotsChainWitness_sound (prims : Primitives p) [DecidableEq prims.Y]
    (sig : WotsSig p prims.core) (msg : prims.Y) (sig' : WotsSig p prims.core) (msg' : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) (i : Fin p.len) {w : WotsWitness p prims}
    (hw : findWotsChainWitness prims sig msg sig' msg' pk adrs i = some w) :
    w.Valid pk adrs (wotsPkFromSigTops prims sig' msg' pk adrs) sig' msg' := by
  set a := chainStepsCore prims.core msg i.val with ha
  set b := chainStepsCore prims.core msg' i.val with hb
  set chAdrs := wotsChainAdrs adrs i.val with hchAdrs
  have hblt : b < p.w := chainStepsCore_lt prims.core msg' i.val
  rw [findWotsChainWitness] at hw
  simp only [← ha, ← hb, ← hchAdrs] at hw
  split at hw
  · rename_i hab
    split at hw
    · rename_i hadv
      rw [Option.some.injEq] at hw
      subst hw
      refine ⟨by omega, by omega, ?_⟩
      have hstep : chain prims pk chAdrs sig[i.val] a (b - a) =
          prims.F pk (chAdrs.setHashAddress (b - 1))
            (chain prims pk chAdrs sig[i.val] a (b - 1 - a)) := by
        rw [show b - a = (b - 1 - a) + 1 by omega, chain_succ,
          show a + (b - 1 - a) = b - 1 by omega]
      rw [← hstep]
      exact hadv
    · rename_i hadv
      rw [Option.map_eq_some_iff] at hw
      obtain ⟨j, hj, rfl⟩ := hw
      obtain ⟨hjlt, hjne, hjcoll⟩ := findChainDivergence_sound prims pk chAdrs _ _ b _ j hj
      have hsub : b + j - b = j := by omega
      exact ⟨by omega, Nat.le_add_right b j,
        by simpa only [← hb, ← hchAdrs, hsub] using hjne,
        by simpa only [← hb, ← hchAdrs, hsub] using hjcoll⟩
  · exact absurd hw (by simp)

/-- The chain search succeeds at every chain whose forged step count is strictly below the honest
one and whose two chains reach the same step-`(w - 1)` endpoint: the preimage test decides the
branch, and on its negative side `findChainDivergence_isSome_of_ne` supplies the collision.

*Deterministic inclusion.* -/
theorem findWotsChainWitness_isSome_of_lt (prims : Primitives p) [DecidableEq prims.Y]
    (sig : WotsSig p prims.core) (msg : prims.Y) (sig' : WotsSig p prims.core) (msg' : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) (i : Fin p.len)
    (hlt : chainStepsCore prims.core msg i.val < chainStepsCore prims.core msg' i.val)
    (hend : chain prims pk (wotsChainAdrs adrs i.val) sig[i.val]
          (chainStepsCore prims.core msg i.val)
          (p.w - 1 - chainStepsCore prims.core msg i.val) =
        chain prims pk (wotsChainAdrs adrs i.val) sig'[i.val]
          (chainStepsCore prims.core msg' i.val)
          (p.w - 1 - chainStepsCore prims.core msg' i.val)) :
    (findWotsChainWitness prims sig msg sig' msg' pk adrs i).isSome := by
  rw [findWotsChainWitness]
  simp only [hlt, if_true]
  split
  · simp
  · rename_i hadv
    have hcomp : chain prims pk (wotsChainAdrs adrs i.val)
          (chain prims pk (wotsChainAdrs adrs i.val) sig[i.val]
            (chainStepsCore prims.core msg i.val)
            (chainStepsCore prims.core msg' i.val - chainStepsCore prims.core msg i.val))
          (chainStepsCore prims.core msg' i.val)
          (p.w - 1 - chainStepsCore prims.core msg' i.val) =
        chain prims pk (wotsChainAdrs adrs i.val) sig'[i.val]
          (chainStepsCore prims.core msg' i.val)
          (p.w - 1 - chainStepsCore prims.core msg' i.val) := by
      have h := chain_compose prims pk (wotsChainAdrs adrs i.val) sig[i.val]
        (chainStepsCore prims.core msg i.val)
        (chainStepsCore prims.core msg' i.val - chainStepsCore prims.core msg i.val)
        (p.w - 1 - chainStepsCore prims.core msg' i.val)
      rw [show chainStepsCore prims.core msg i.val +
          (chainStepsCore prims.core msg' i.val - chainStepsCore prims.core msg i.val) =
        chainStepsCore prims.core msg' i.val by omega,
        show chainStepsCore prims.core msg' i.val - chainStepsCore prims.core msg i.val +
          (p.w - 1 - chainStepsCore prims.core msg' i.val) =
        p.w - 1 - chainStepsCore prims.core msg i.val by
          have := chainStepsCore_le prims.core msg' i.val; omega] at h
      rw [h, hend]
    have := findChainDivergence_isSome_of_ne prims pk (wotsChainAdrs adrs i.val) _ _
      (chainStepsCore prims.core msg' i.val)
      (p.w - 1 - chainStepsCore prims.core msg' i.val) hadv hcomp
    rw [Option.isSome_map]
    exact this

/-- **Extractor soundness.**  A witness returned by `findWotsWitness` satisfies
`WotsWitness.Valid` against the chain ends `sig'` recovers on `msg'`, the honest signature `sig'`,
and the message `msg'` it signs.

The public-key hypothesis is used only by the `T_len` branch, where it supplies the equality of the
two compressions; `findWotsChainWitness_sound` is the hypothesis-free statement for the two chain
branches.  As `WotsWitness.Valid` records, this says nothing about whether those honest objects
were committed as game targets.

*Deterministic inclusion.* -/
theorem findWotsWitness_sound (prims : Primitives p) [DecidableEq prims.Y]
    (sig : WotsSig p prims.core) (msg : prims.Y) (sig' : WotsSig p prims.core) (msg' : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs)
    (hpk : wotsPkFromSig prims sig msg pk adrs = wotsPkFromSig prims sig' msg' pk adrs)
    {w : WotsWitness p prims}
    (hw : findWotsWitness prims sig msg sig' msg' pk adrs = some w) :
    w.Valid pk adrs (wotsPkFromSigTops prims sig' msg' pk adrs) sig' msg' := by
  rw [findWotsWitness] at hw
  split at hw
  · obtain ⟨i, _, hi⟩ := List.exists_of_findSome?_eq_some hw
    exact findWotsChainWitness_sound prims sig msg sig' msg' pk adrs i hi
  · rename_i htops
    rw [Option.some.injEq] at hw
    subst hw
    refine ⟨htops, ?_⟩
    rw [wotsPkFromSig_eq_tl, wotsPkFromSig_eq_tl] at hpk
    exact hpk

/-- **Extractor completeness.**  On two distinct messages the search always returns a witness:
either the two signatures recover different chain ends, and the `T_len` branch fires, or they
recover the same chain ends and `wotsPkFromSigTops_cases` supplies a chain that yields one.

No public-key hypothesis is needed to make the search *succeed*.  It is `findWotsWitness_sound`
that needs the two recovered public keys to agree, and only for the `T_len` branch.  The
chain-level half of the argument is `findWotsChainWitness_isSome_of_lt`.

*Deterministic inclusion.* -/
theorem findWotsWitness_isSome (valid : p.Valid) (prims : Primitives p) [DecidableEq prims.Y]
    (laws : prims.core.ByteLaws) (sig : WotsSig p prims.core) (msg : prims.Y)
    (sig' : WotsSig p prims.core) (msg' : prims.Y) (pk : prims.PkSeed) (adrs : Adrs)
    (hne : msg ≠ msg') :
    (findWotsWitness prims sig msg sig' msg' pk adrs).isSome := by
  rw [findWotsWitness]
  split
  · rename_i htops
    obtain ⟨i, hlt, -⟩ :=
      wotsPkFromSigTops_cases valid prims laws sig sig' msg msg' pk adrs hne htops
    have hend : chain prims pk (wotsChainAdrs adrs i.val) sig[i.val]
          (chainStepsCore prims.core msg i.val)
          (p.w - 1 - chainStepsCore prims.core msg i.val) =
        chain prims pk (wotsChainAdrs adrs i.val) sig'[i.val]
          (chainStepsCore prims.core msg' i.val)
          (p.w - 1 - chainStepsCore prims.core msg' i.val) := by
      have := congrArg (fun v : Vector prims.Y p.len => v[i.val]) htops
      simpa only [wotsPkFromSigTops_eq_ofFn, Vector.getElem_ofFn] using this
    have hchain : (findWotsChainWitness prims sig msg sig' msg' pk adrs i).isSome :=
      findWotsChainWitness_isSome_of_lt prims sig msg sig' msg' pk adrs i hlt hend
    obtain ⟨w, hwv⟩ := Option.isSome_iff_exists.mp hchain
    have : ((List.finRange p.len).findSome?
        (findWotsChainWitness prims sig msg sig' msg' pk adrs)) ≠ none := by
      intro hnone
      rw [List.findSome?_eq_none_iff] at hnone
      exact absurd (hnone i (List.mem_finRange i)) (by rw [hwv]; simp)
    exact Option.isSome_iff_ne_none.mpr this
  · simp

/-! ## Ledger membership and encoded distinctness

*Transcript transport.*  Every address a witness names at a reachable WOTS+ instance is a member
of the slice-1 role ledger it is submitted against, and — under `EncodedTargetLedgerConditions` —
distinct addresses of one ledger carry distinct encoded tweaks.  The three roles are reached
separately, because they have three different ledgers:

* the `fCollision` witness attacks `wotsFTcr`, whose ledger is `wotsStepAddresses`
  (`mem_wotsStepAddresses_of_lt`, `wotsStepAdrsKey_injective`);
* the `fPreimage` witness attacks `wotsFPre`, whose ledger is the one-step-per-chain
  `optionalWotsAddresses` of the selection the reduction makes
  (`wotsPreimageAdrs_mem_optionalWotsAddresses`, `wotsOptionalStepAdrsKey_injective`); its address
  is also a `wotsStepAddresses` member (`wotsPreimageAdrs_mem_wotsStepAddresses`), which is a
  weaker statement about a different role's ledger and not what a PRE reduction consumes;
* the `tlCollision` witness attacks `wotsTl`, whose ledger is `wotsPkAddresses`; its address is
  literally `wotsPkAdrs (wotsInstanceAdrs pos)`, which `mem_wotsPkAddresses` already lists, so
  that lemma is used directly rather than restated.

These are statements about the ledgers, not about any execution: nothing here says a logged query
carried the witness values, and which chain a PRE reduction selects is its own choice, carried
here as the `select` argument. -/

variable {vp : ValidatedParams}

/-- Every WOTS+ hash-step address below `w - 1` at a reachable instance is a listed `wotsFTcr`
target.  The address is definitionally `wotsStepAdrs`, so this is `mem_wotsStepAddresses` in the
construction's own vocabulary. -/
theorem mem_wotsStepAddresses_of_lt (pos : LayerPosition vp) (i : Fin vp.params.len) {t : ℕ}
    (ht : t < vp.params.w - 1) :
    (wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress t ∈ wotsStepAddresses vp :=
  mem_wotsStepAddresses vp (pos, i) ⟨t, ht⟩

/-- The `F`-preimage branch of `chainPair_cases` names the address one step below the honest
digit; on a reachable instance it is a listed `wotsFTcr` target, because the honest digit is a
genuine base-`w` digit.  The caller's `chainStepsCore … msg i < chainStepsCore … msg' i` supplies
the positivity hypothesis; taking it in this weaker form drops the forged message from the
statement. -/
theorem wotsPreimageAdrs_mem_wotsStepAddresses {prims : Primitives vp.params}
    (pos : LayerPosition vp) (i : Fin vp.params.len) (msg' : prims.Y)
    (hpos : 0 < chainStepsCore prims.core msg' i.val) :
    (wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress
        (chainStepsCore prims.core msg' i.val - 1) ∈ wotsStepAddresses vp := by
  refine mem_wotsStepAddresses_of_lt pos i ?_
  have := chainStepsCore_lt prims.core msg' i.val
  omega

/-- The `F`-preimage witness's own role ledger.  A PRE reduction picks at most one hash step per
chain, and at a chain whose selected step is the one below the honest digit the witness address is
a listed `wotsFPre` target of that selection. -/
theorem wotsPreimageAdrs_mem_optionalWotsAddresses {prims : Primitives vp.params}
    (pos : LayerPosition vp) (i : Fin vp.params.len) (msg' : prims.Y)
    (select : WotsChainCoord vp → Option (Fin (vp.params.w - 1)))
    {step : Fin (vp.params.w - 1)} (hsel : select (pos, i) = some step)
    (hstep : step.val = chainStepsCore prims.core msg' i.val - 1) :
    (wotsChainAdrs (wotsInstanceAdrs pos) i.val).setHashAddress
        (chainStepsCore prims.core msg' i.val - 1) ∈ optionalWotsAddresses vp select := by
  have hmem := mem_optionalWotsAddresses vp select (pos, i) hsel
  rwa [wotsStepAdrs, hstep] at hmem

/-- Under the encoded-ledger conditions, distinct WOTS+ chain-step coordinates carry distinct
encoded tweaks: two witnesses naming different `(instance, chain, step)` triples attack different
tweaks of `wotsFTcrCProblem`.

The conditions are consumed, not assumed afresh: `approvedEncodedTargetLedgerConditions` discharges
them for every approved profile, so the SHA-2 zero fallback is never treated as unreachable. -/
theorem wotsStepAdrsKey_injective {prims : Primitives vp.params}
    (conditions : EncodedTargetLedgerConditions vp prims) :
    Function.Injective fun coord : WotsChainCoord vp × Fin (vp.params.w - 1) =>
      prims.adrsToKey (wotsStepAdrs coord.1 coord.2) := by
  intro c d hcd
  have hinj := (encodeTargets_nodup_iff_injOn prims (wotsStepAddresses vp)
    (wotsStepAddresses_nodup vp)).1 conditions.wotsFTcr
  exact wotsStepAdrs_injective vp
    (hinj _ (mem_wotsStepAddresses vp c.1 c.2) _ (mem_wotsStepAddresses vp d.1 d.2) hcd)

/-- Under the encoded-ledger conditions, two chains a PRE selection retains carry distinct encoded
tweaks: two `fPreimage` witnesses at different chains of one selection attack different tweaks of
`wotsFPreCProblem`.  The selection is the reduction's own, and the conditions are consumed at it
rather than assumed afresh. -/
theorem wotsOptionalStepAdrsKey_injective {prims : Primitives vp.params}
    (conditions : EncodedTargetLedgerConditions vp prims)
    (select : WotsChainCoord vp → Option (Fin (vp.params.w - 1)))
    {c d : WotsChainCoord vp} {sc sd : Fin (vp.params.w - 1)}
    (hc : select c = some sc) (hd : select d = some sd)
    (hkey : prims.adrsToKey (wotsStepAdrs c sc) = prims.adrsToKey (wotsStepAdrs d sd)) :
    c = d := by
  have hinj := (encodeTargets_nodup_iff_injOn prims (optionalWotsAddresses vp select)
    (optionalWotsAddresses_nodup vp select)).1 (conditions.wotsFPre select)
  exact congrArg Prod.fst (wotsStepAdrs_injective vp (a₁ := (c, sc)) (a₂ := (d, sd))
    (hinj _ (mem_optionalWotsAddresses vp select c hc) _
      (mem_optionalWotsAddresses vp select d hd) hkey))

/-- Under the encoded-ledger conditions, distinct WOTS+ instances carry distinct encoded
compression tweaks: two `T_len` witnesses at different instances attack different tweaks of
`wotsTlTcrCProblem`. -/
theorem wotsPkAdrsKey_injective {prims : Primitives vp.params}
    (conditions : EncodedTargetLedgerConditions vp prims) :
    Function.Injective fun pos : LayerPosition vp =>
      prims.adrsToKey (wotsPkAdrs (wotsInstanceAdrs pos)) := by
  intro pos pos' h
  have hinj := (encodeTargets_nodup_iff_injOn prims (wotsPkAddresses vp)
    (wotsPkAddresses_nodup vp)).1 conditions.wotsTl
  have hadrs := hinj _ (mem_wotsPkAddresses vp pos) _ (mem_wotsPkAddresses vp pos') h
  exact (List.nodup_map_iff_inj_on (allWotsInstances_nodup vp)).1
    (wotsPkAddresses_nodup vp) pos (mem_allWotsInstances vp pos) pos'
    (mem_allWotsInstances vp pos') hadrs

/-! ## Game shapes

`WotsWitness.Valid` is stated in the construction's own vocabulary (`prims.F`, `prims.Tl` at a
structural `Adrs`).  These three bridges rewrite it into the canonical games' `eval` vocabulary at
the encoded tweak, using the attacked-member equations of `HashSig.SLHDSA.Security.CanonicalGames`.
Each takes explicitly only the honest objects its own branch mentions; the others are implicit and
read off the hypothesis.  They change presentation only: no game is played and no advantage is
stated. -/

variable (prims : Primitives p)

/-- The `F`-preimage branch, read in `wotsFPreCProblem`'s vocabulary: the submitted value evaluates
to the honest revealed chain value at the encoded chain-step tweak, at the step the honest signer
hashed to reach it. -/
theorem wotsWitness_valid_fPreimage_eval [SampleableType prims.PkSeed] (pk : prims.PkSeed)
    (adrs : Adrs) {honestTops : Vector prims.Y p.len} (honestSig : WotsSig p prims.core)
    (honestMsg : prims.Y) (i : Fin p.len) (step : ℕ) (value : prims.Y)
    (h : (WotsWitness.fPreimage i step value).Valid pk adrs honestTops honestSig honestMsg) :
    step < p.w - 1 ∧ step + 1 = chainStepsCore prims.core honestMsg i.val ∧
      (wotsFPreCProblem prims).th.eval pk
          (prims.adrsToKey ((wotsChainAdrs adrs i.val).setHashAddress step)) value =
        honestSig[i.val] :=
  ⟨h.1, h.2.1, by rw [wotsFPreCProblem_eval_adrsToKey]; exact h.2.2⟩

/-- The `F`-collision branch, read in `wotsFTcrCProblem`'s vocabulary: the submitted value and the
honest chain value at the named step are distinct and evaluate equally at the encoded chain-step
tweak. -/
theorem wotsWitness_valid_fCollision_eval [SampleableType prims.PkSeed] (pk : prims.PkSeed)
    (adrs : Adrs) {honestTops : Vector prims.Y p.len} (honestSig : WotsSig p prims.core)
    (honestMsg : prims.Y) (i : Fin p.len) (step : ℕ) (value : prims.Y)
    (h : (WotsWitness.fCollision i step value).Valid pk adrs honestTops honestSig honestMsg) :
    step < p.w - 1 ∧ chainStepsCore prims.core honestMsg i.val ≤ step ∧
      value ≠ chain prims pk (wotsChainAdrs adrs i.val) honestSig[i.val]
          (chainStepsCore prims.core honestMsg i.val)
          (step - chainStepsCore prims.core honestMsg i.val) ∧
      (wotsFTcrCProblem prims).th.eval pk
          (prims.adrsToKey ((wotsChainAdrs adrs i.val).setHashAddress step)) value =
        (wotsFTcrCProblem prims).th.eval pk
          (prims.adrsToKey ((wotsChainAdrs adrs i.val).setHashAddress step))
          (chain prims pk (wotsChainAdrs adrs i.val) honestSig[i.val]
            (chainStepsCore prims.core honestMsg i.val)
            (step - chainStepsCore prims.core honestMsg i.val)) :=
  ⟨h.1, h.2.1, h.2.2.1, by
    rw [wotsFTcrCProblem_eval_adrsToKey, wotsFTcrCProblem_eval_adrsToKey]
    exact h.2.2.2⟩

/-- The `T_len` branch, read in `wotsTlTcrCProblem`'s vocabulary: two distinct chain-end vectors
with the same evaluation at the encoded compression tweak. -/
theorem wotsWitness_valid_tlCollision_eval [SampleableType prims.PkSeed] (pk : prims.PkSeed)
    (adrs : Adrs) (honestTops : Vector prims.Y p.len) {honestSig : WotsSig p prims.core}
    {honestMsg : prims.Y} (recovered : Vector prims.Y p.len)
    (h : (WotsWitness.tlCollision recovered).Valid pk adrs honestTops honestSig honestMsg) :
    recovered ≠ honestTops ∧
      (wotsTlTcrCProblem prims).th.eval pk (prims.adrsToKey (wotsPkAdrs adrs)) recovered =
        (wotsTlTcrCProblem prims).th.eval pk (prims.adrsToKey (wotsPkAdrs adrs)) honestTops :=
  ⟨h.1, by
    rw [wotsTlTcrCProblem_eval_adrsToKey, wotsTlTcrCProblem_eval_adrsToKey]
    exact h.2⟩

end SLHDSA.Security
