/-
Copyright (c) 2026 Alexander Hicks. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module
public import HashSig.SLHDSA.Security.CanonicalGames
public import HashSig.SLHDSA.Security.ReachableTargets

/-!
# FORS witnesses

Deterministic translations of a FORS public-key match into a concrete witness against one named
FORS component hash: a `T_k` second preimage of the honest root vector at the `FORS_ROOTS`
compression address, an ordered-pair collision of `H` at an exact `FORS_TREE` internal-node
address, or an `F`-preimage of an honest leaf image at an exact `FORS_TREE` leaf address.  The
case analysis is the Lean counterpart of three of the four branches of the FORS translation in the
EasyCrypt SPHINCS+ development (`FORS_ES.ec`, theorem `EUFCMA_MFORSTWESNPRF_OPRE` at `:3827`).

## What is proved, and what is not

Every *deterministic-inclusion* statement below is about a primitive bundle, a public seed, a
secret seed, a structural address, a message digest, and a FORS signature.  Unlike the WOTS+
witnesses, the honest secret seed is not confined to one lemma: the FORS honest partner a witness
attacks — the honest root vector, the honest child pair at an internal node, the honest leaf image
— is a function of the honest tree, and the honest tree is what `sk` generates.  The
*transcript-transport* statements are about a role ledger over a `ValidatedParams`; they mention
no signature at all.  Nothing here constructs an adversary, states an advantage, performs a game
hop, or claims that any honest execution queried the honest value a witness attacks.  In
particular a witness lemma is **not** a reduction: that the game's target was committed before the
forgery was seen is a simulation-fidelity obligation of the later program-level slice, not a fact
established here.

The FORS translation of `FORS_ES.ec` splits **four** ways, not three.  The fourth branch is
`valid_ITSR` (`FORS_ES.ec:3213`), which selects the FORS leaf index the honest signer never
opened; it is a statement about the digest transcript and the signing log, not about one FORS
signature, and it is deliberately absent here.  Consequently this module never establishes that a
witness address is *unopened*, which is the second half of the FORS-`F` winning condition
(`FORS_ES.ec:4461`); only the preimage half (`:4462`) is proved.

## Labels

*Deterministic inclusion* — a statement whose only free objects are `prims`, seeds, addresses,
a digest and signature data:

* the four definitions `forsSigLeafIndex`, `forsHonestRoots`, `forsRecoveredRoots`,
  `forsHonestChildren`, with their equations `forsSigLeafIndex_eq`, `forsHonestRoots_getElem`,
  `forsRecoveredRoots_getElem`, `forsHonestChildren_eq`, `forsPkGen_eq_tl_honestRoots`,
  `forsPkFromSig_eq_tl_recoveredRoots`, and the index facts `forsSigLeafIndex_div_pow_a`,
  `forsSigLeafIndex_div_lt`;
* `forsRootsBinding`, `forsTreeBinding`, `forsLeafPreimage`, `forsPkFromSig_cases`;
* `ForsWitness`, `ForsWitness.Valid` and its three unfolding equations
  `ForsWitness.valid_tlCollision`, `ForsWitness.valid_hCollision`,
  `ForsWitness.valid_fPreimage`;
* `findForsTreeCollision`, `findForsTreeCollision_sound`, `findForsTreeCollision_isSome_of_ne`,
  `findForsTreeCollision_eq_none_imp`, `findForsWitness`, `findForsWitness_sound`;
* the three game-shape bridges `forsWitness_valid_tlCollision_eval`,
  `forsWitness_valid_hCollision_eval`, `forsWitness_valid_fPreimage_eval`.

*Transcript transport* — a statement about a role ledger of `HashSig.SLHDSA.Security`:

* `mem_forsLeafAddresses_of_digest`, `mem_forsTreeAddresses_of_digest`;
* `forsLeafAdrsKey_injective`, `forsTreeAdrsKey_injective`, `forsRootAdrsKey_injective`.

The `T_k` witness address is `forsPkAdrs pos.forsAdrs`, which `mem_forsRootAddresses` already
lists in the `forsTl` ledger; that lemma is used directly rather than restated.

The three encoded-distinctness lemmas consume `EncodedTargetLedgerConditions` rather than assuming
a fresh injectivity hypothesis, so a concrete profile discharges them through
`approvedEncodedTargetLedgerConditions`; the SHA-2 zero fallback is therefore never treated as
unreachable.

## The case analysis

Fix a digest `md`, a FORS signature `sig`, and the honest key material `(sk, pk)` at the
instance address `adrs`.  Recovery compresses the `k` roots `sig` climbs to, and key generation
compresses the `k` honest roots; a public-key match therefore equates the two `T_k` images.
Either the two root vectors differ — a `T_k` second preimage at `forsPkAdrs adrs`, the residual
TRCO branch of `FORS_ES.ec:6346-6355`, whose core is `eq_from_flatten_nth` (`:871`) — or they
agree entry by entry.  In the latter case each tree `i` climbs the forged opening of the honest
leaf index `forsSigLeafIndex p md i` to the honest tree-`i` root, and at each tree either the
forged leaf image differs from the honest one, and `PerfectMerkleTree.climb_binding` extracts an
`H`-collision at an internal node on that leaf's root path — the `valid_TRHTCR` branch
(`FORS_ES.ec:3242`), whose extractor is `extract_collision_bt_ap_trh` (`:729`) over `ecbtapP`
(`MerkleTrees.ec:152`) — or it agrees, and the revealed secret value is an `F`-preimage of the
honest leaf image — the `valid_OpenPRE` branch (`:3231`).

The FORS-`F` branch is an **open-preimage** witness, not a target-collision one.  The
source's postcondition (`FORS_ES.ec:4454-4462`) asks for an index in range, an index the signer
never opened, and `f pp tw x = y`; it carries no `x <> x'`, and the winning condition of
`SM_DT_OpenPRE_SourceFinalValidity.Experiment` carries none either.  A value equal to the honest
secret is therefore allowed to win, and adding a distinctness hypothesis here would state
something strictly stronger than the source establishes and strictly stronger than the game needs.

`MultiExtractability` is deliberately not imported: it is a probabilistic shared-ROM game over
sequential checkpoints and pruned batch openings, whereas the collision needed here is against one
fixed honest tree, which is exactly what `PerfectMerkleTree.findCollision` and `climb_binding`
give.

## References

- NIST FIPS 205, §8 (Algorithms 14–17)
- Barbosa, Dupressoir, Hülsing, Meijers, and Strub, "A Tight Security Proof for SPHINCS+,
  Formally Verified" (`FORS_ES.ec`, `MerkleTrees.ec`)
-/

public section

namespace SLHDSA.Security

open CanonicalGames

variable {p : Params}

/-! ## The two root vectors

FORS signing and FORS key generation both compress `k` roots under `T_k` at `forsPkAdrs adrs`.
Naming the two vectors separates the compression step from the per-tree Merkle argument. -/

/-- The global FORS leaf index tree `i` opens on digest `md`: FIPS 205 Algorithm 16 line 4 and
Algorithm 17 line 5 both index the FORS trees continuously, so tree `i`'s local leaf
`forsIdx p md i` sits at `i * 2 ^ a + forsIdx p md i`. -/
def forsSigLeafIndex (p : Params) (md : List Byte) (i : ℕ) : ℕ := i * 2 ^ p.a + forsIdx p md i

/-- Unfolding equation for `forsSigLeafIndex`. -/
theorem forsSigLeafIndex_eq (p : Params) (md : List Byte) (i : ℕ) :
    forsSigLeafIndex p md i = i * 2 ^ p.a + forsIdx p md i := by rfl

/-- The global leaf index of tree `i` names tree `i` again once the tree height `a` is divided
out: the FORS numbering is continuous across the `k` trees, so the top `⌈log₂ k⌉` bits are the
tree number. -/
theorem forsSigLeafIndex_div_pow_a (p : Params) (md : List Byte) (i : ℕ) :
    forsSigLeafIndex p md i / 2 ^ p.a = i := by
  rw [forsSigLeafIndex, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos p.a),
    Nat.div_eq_of_lt (forsIdx_lt p md i), Nat.zero_add]

/-- At any height `z ≤ a`, the ancestor of tree `i`'s opened leaf carries the global height-`z`
index `i * 2 ^ (a - z) + j` with `j < 2 ^ (a - z)`, which is the coordinate shape
`forsTreeAddresses` lists.  FIPS 205 Algorithm 16 line 7 uses the same shape for the
authentication path. -/
theorem forsSigLeafIndex_div_lt (p : Params) (md : List Byte) (i z : ℕ) (hz : z ≤ p.a) :
    forsSigLeafIndex p md i / 2 ^ z = i * 2 ^ (p.a - z) + forsIdx p md i / 2 ^ z ∧
      forsIdx p md i / 2 ^ z < 2 ^ (p.a - z) := by
  have hpow : (2 : ℕ) ^ p.a = 2 ^ (p.a - z) * 2 ^ z := by
    rw [← pow_add]; congr 1; omega
  constructor
  · rw [forsSigLeafIndex, hpow, ← Nat.mul_assoc, Nat.add_comm,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos z), Nat.add_comm]
  · exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm, ← hpow]; exact forsIdx_lt p md i)

/-- The `k` honest FORS tree roots at `adrs`, in tree order — the vector `forsPkGen` compresses
(FIPS 205 Algorithm 15 at `z = a`). -/
def forsHonestRoots (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    Vector prims.Y p.k :=
  Vector.ofFn fun i : Fin p.k => forsRoot prims sk pk adrs i.val

/-- Unfolding equation for `forsHonestRoots`: entry `i` is the honest root of tree `i`. -/
@[simp] theorem forsHonestRoots_getElem {prims : Primitives p} (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (i : ℕ) (hi : i < p.k) :
    (forsHonestRoots prims sk pk adrs)[i] = forsRoot prims sk pk adrs i := by
  simp [forsHonestRoots]

/-- The `k` roots a FORS signature climbs to on digest `md`, in tree order — the vector
`forsPkFromSig` compresses (FIPS 205 Algorithm 17 lines 3–19). -/
def forsRecoveredRoots (prims : Primitives p) (sig : ForsSigCore p prims.core) (md : List Byte)
    (pk : prims.PkSeed) (adrs : Adrs) : Vector prims.Y p.k :=
  Vector.ofFn fun i : Fin p.k =>
    PerfectMerkleTree.climb (forsNodeHash prims pk adrs) (forsSigLeafIndex p md i.val)
      (prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val)) (sig[i.val]).sk)
      (sig[i.val]).auth.toList

/-- Unfolding equation for `forsRecoveredRoots`: entry `i` is the climb of tree `i`'s
authentication path from the `F` image of its revealed secret value. -/
@[simp] theorem forsRecoveredRoots_getElem {prims : Primitives p} (sig : ForsSigCore p prims.core)
    (md : List Byte) (pk : prims.PkSeed) (adrs : Adrs) (i : ℕ) (hi : i < p.k) :
    (forsRecoveredRoots prims sig md pk adrs)[i] =
      PerfectMerkleTree.climb (forsNodeHash prims pk adrs) (forsSigLeafIndex p md i)
        (prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i)) (sig[i]).sk)
        (sig[i]).auth.toList := by
  simp [forsRecoveredRoots]

/-- FORS key generation compresses the honest root vector. -/
theorem forsPkGen_eq_tl_honestRoots (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    forsPkGen prims sk pk adrs =
      prims.Tl pk (forsPkAdrs adrs) (forsHonestRoots prims sk pk adrs).toList :=
  forsPkGen_eq_tl prims sk pk adrs

/-- FORS recovery compresses the recovered root vector. -/
theorem forsPkFromSig_eq_tl_recoveredRoots (prims : Primitives p) (sig : ForsSigCore p prims.core)
    (md : List Byte) (pk : prims.PkSeed) (adrs : Adrs) :
    forsPkFromSig prims sig md pk adrs =
      prims.Tl pk (forsPkAdrs adrs) (forsRecoveredRoots prims sig md pk adrs).toList :=
  forsPkFromSig_eq_tl prims sig md pk adrs

/-! ## The three branches -/

/-- **FORS root-compression binding.**  A signature that recovers the honest FORS public key
compresses its recovered roots to the same `T_k` image as the honest roots, at `forsPkAdrs adrs`.

This is only half of a `T_k` second preimage: that the two root vectors *differ* is the caller's
case split, and `forsPkFromSig_cases` is what supplies it.  The EasyCrypt counterpart is the
residual TRCO branch (`FORS_ES.ec:6346-6355`), whose core is `eq_from_flatten_nth` (`:871`).

*Deterministic inclusion.* -/
theorem forsRootsBinding (prims : Primitives p) (sig : ForsSigCore p prims.core) (md : List Byte)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (hpk : forsPkFromSig prims sig md pk adrs = forsPkGen prims sk pk adrs) :
    prims.Tl pk (forsPkAdrs adrs) (forsRecoveredRoots prims sig md pk adrs).toList =
      prims.Tl pk (forsPkAdrs adrs) (forsHonestRoots prims sk pk adrs).toList := by
  rw [← forsPkFromSig_eq_tl_recoveredRoots, ← forsPkGen_eq_tl_honestRoots]
  exact hpk

/-- The honest child pair of the FORS internal node at height `z`, global index `t`: the two
honest subtree roots one level below.  Meaningful only at `0 < z`, which every statement below
that mentions it asserts; at `z = 0` truncated subtraction would silently name the leaf level, and
`forsNodeAdrs adrs 0 t` is a `forsF` leaf target rather than a `forsH` node target. -/
def forsHonestChildren (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (z t : ℕ) : prims.Y × prims.Y :=
  PerfectMerkleTree.honestChildren (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) z t

/-- Unfolding equation for `forsHonestChildren`, in the construction's own vocabulary. -/
theorem forsHonestChildren_eq (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (z t : ℕ) :
    forsHonestChildren prims sk pk adrs z t =
      (PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs)
          (z - 1) (2 * t),
        PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs)
          (z - 1) (2 * t + 1)) := by rfl

/-- **FORS tree binding.**  If tree `i` of a signature climbs to the honest tree-`i` root while
its forged leaf image differs from the honest leaf image, then some internal node of height
`0 < z ≤ a` on the opened leaf's root path carries an `H`-collision between the honest child pair
there and a second, different pair — at exactly the address
`forsNodeAdrs adrs z (forsSigLeafIndex p md i / 2 ^ z)`.

This is the `valid_TRHTCR` branch (`FORS_ES.ec:3242`, postcondition `:5783-5792`); the extractor
is `extract_collision_bt_ap_trh` (`:729`), whose correctness is `ecbtapP` (`MerkleTrees.ec:152`).
The Lean port already exists as `PerfectMerkleTree.climb_binding`, and the orientation matches:
`ecbtapP` returns the honest child pair first, and so does `climb_binding`.

*Deterministic inclusion.* -/
theorem forsTreeBinding (prims : Primitives p) (sig : ForsSigCore p prims.core) (md : List Byte)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (i : Fin p.k)
    (hroot : (forsRecoveredRoots prims sig md pk adrs)[i.val] =
      (forsHonestRoots prims sk pk adrs)[i.val])
    (hleaf : forsLeaf prims sk pk adrs (forsSigLeafIndex p md i.val) ≠
      prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val)) (sig[i.val]).sk) :
    ∃ z c, 0 < z ∧ z ≤ p.a ∧
      forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z) ≠ c ∧
      prims.H pk (forsNodeAdrs adrs z (forsSigLeafIndex p md i.val / 2 ^ z))
          (forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z)).1
          (forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z)).2 =
        prims.H pk (forsNodeAdrs adrs z (forsSigLeafIndex p md i.val / 2 ^ z)) c.1 c.2 := by
  have hlen : (sig[i.val]).auth.toList.length = p.a := by simp
  have hclimb : PerfectMerkleTree.climb (forsNodeHash prims pk adrs)
        (forsSigLeafIndex p md i.val)
        (prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val)) (sig[i.val]).sk)
        (sig[i.val]).auth.toList =
      PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) p.a
        (forsSigLeafIndex p md i.val / 2 ^ p.a) := by
    rw [forsSigLeafIndex_div_pow_a]
    rw [forsRecoveredRoots_getElem, forsHonestRoots_getElem, forsRoot_eq_merkleRoot] at hroot
    exact hroot
  obtain ⟨z, c, hzpos, hzle, hne, hcoll⟩ :=
    PerfectMerkleTree.climb_binding (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs)
      p.a (forsSigLeafIndex p md i.val) _ _ hlen hclimb hleaf
  refine ⟨z, c, hzpos, hzle, ?_, ?_⟩
  · rw [forsHonestChildren_eq]; exact hne
  · rw [forsHonestChildren_eq]; simpa only [forsNodeHash_eq_h] using hcoll

/-- **FORS leaf preimage.**  If tree `i`'s forged leaf image agrees with the honest one, the
revealed secret value is an `F`-preimage of the honest leaf image at
`forsNodeAdrs adrs 0 (forsSigLeafIndex p md i)`.

This is the `valid_OpenPRE` branch (`FORS_ES.ec:3231`), whose postcondition's hash obligation is
`f pp tw x = y` (`:4462`).  There is deliberately no `≠`: the source asks only that the value be
*a* preimage of the recorded image, and `SM_DT_OpenPRE_SourceFinalValidity.Experiment`'s winning
condition asks only that too.  The remaining half of that postcondition — that the index was never
opened (`:4461`) — is the `valid_ITSR` branch and is not proved here.

*Deterministic inclusion.* -/
theorem forsLeafPreimage (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (t : ℕ) (x : prims.Y)
    (hleaf : forsLeaf prims sk pk adrs t = prims.F pk (forsNodeAdrs adrs 0 t) x) :
    prims.F pk (forsNodeAdrs adrs 0 t) x =
      prims.F pk (forsNodeAdrs adrs 0 t) (forsSkGenCore prims.core sk pk adrs t) := by
  rw [← hleaf, forsLeaf_eq_f]

/-- **FORS instance trichotomy.**  A signature on digest `md` that recovers the honest FORS public
key at `adrs` yields one of three witnesses: a `T_k` second preimage of the honest root vector at
`forsPkAdrs adrs`; an `H`-collision at an internal node on some tree's opened root path; or, at
*every* tree, an `F`-preimage of that tree's honest leaf image.

The proof splits on whether the recovered roots equal the honest ones, and then on whether some
tree's forged leaf image differs from the honest one.  It is exhaustive by construction: both
splits are decisions on a proposition and its negation.

These are the three non-ITSR branches of the four-way FORS split of `FORS_ES.ec`
(`EUFCMA_MFORSTWESNPRF_OPRE`, `:3827`); the fourth, `valid_ITSR` (`:3213`), decides *which* tree's
preimage the third branch should be submitted at and is not available from one signature.

*Deterministic inclusion.* -/
theorem forsPkFromSig_cases (prims : Primitives p) (sig : ForsSigCore p prims.core)
    (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (hpk : forsPkFromSig prims sig md pk adrs = forsPkGen prims sk pk adrs) :
    (forsRecoveredRoots prims sig md pk adrs ≠ forsHonestRoots prims sk pk adrs ∧
        prims.Tl pk (forsPkAdrs adrs) (forsRecoveredRoots prims sig md pk adrs).toList =
          prims.Tl pk (forsPkAdrs adrs) (forsHonestRoots prims sk pk adrs).toList) ∨
      (∃ (i : Fin p.k) (z : ℕ) (c : prims.Y × prims.Y), 0 < z ∧ z ≤ p.a ∧
        forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z) ≠ c ∧
        prims.H pk (forsNodeAdrs adrs z (forsSigLeafIndex p md i.val / 2 ^ z))
            (forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z)).1
            (forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z)).2 =
          prims.H pk (forsNodeAdrs adrs z (forsSigLeafIndex p md i.val / 2 ^ z)) c.1 c.2) ∨
      (∀ i : Fin p.k,
        prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val)) (sig[i.val]).sk =
          prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val))
            (forsSkGenCore prims.core sk pk adrs (forsSigLeafIndex p md i.val))) := by
  by_cases hroots : forsRecoveredRoots prims sig md pk adrs = forsHonestRoots prims sk pk adrs
  · by_cases hsome : ∃ i : Fin p.k,
        forsLeaf prims sk pk adrs (forsSigLeafIndex p md i.val) ≠
          prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val)) (sig[i.val]).sk
    · obtain ⟨i, hi⟩ := hsome
      obtain ⟨z, c, hz⟩ := forsTreeBinding prims sig md sk pk adrs i (by rw [hroots]) hi
      exact Or.inr (Or.inl ⟨i, z, c, hz⟩)
    · refine Or.inr (Or.inr fun i => ?_)
      simp only [not_exists, not_not] at hsome
      exact forsLeafPreimage prims sk pk adrs _ _ (hsome i)
  · exact Or.inl ⟨hroots, forsRootsBinding prims sig md sk pk adrs hpk⟩

/-! ## The extracted witness

`ForsWitness` packages the three outcomes as the data a reduction submits: the recovered root
vector, an adversarial child pair together with the height that names its tweak, or the revealed
secret value together with the tree that names its tweak.  Every honest object a witness attacks
is an argument of `ForsWitness.Valid` and never a constructor field: `Valid` takes the honest
secret seed, the public seed, the instance address and the *forged* digest, and from them
*computes* the honest root vector, the honest child pair at the named node, and the honest leaf
image at the named tree's opened leaf.

That computation is the identification a source-final-validity game needs: its winning condition
compares the submitted value against the challenge *recorded* at the named target, so a pair of
arbitrary distinct values with equal images is not a win.  `ForsWitness.Valid` therefore carries
the hash-value half of that winning condition — for the two collision branches the distinctness
and the equal images, for the preimage branch the equal images alone, against a partner the
predicate names rather than quantifies over — together with the height bounds that place the
address in a role ledger, and nothing beyond that.  It does not assert that the honest object was
recorded as a game target, that the preimage branch's index was never opened, or anything about
the rest of a transcript; those are program-level obligations of the reduction.

Only the forged digest appears.  The honest digest does not, because — unlike the WOTS+ case,
where the honest partner is read off the honest signature — every FORS honest partner is a
function of the honest tree, which `sk` generates. -/

/-- A witness against one FORS component hash at a fixed instance address.

Each constructor carries only the value a reduction submits, together with the coordinate that
names its tweak: the tree height for the `H` branch, the tree number for the `F` branch.  The
`T_k` tweak is named by `adrs` alone, so `tlCollision` carries no coordinate; and the `H` branch's
horizontal index is not carried either, because the forged digest already fixes it.  Every honest
object a witness attacks is supplied to `ForsWitness.Valid`, which reads it off the honest tree. -/
inductive ForsWitness (p : Params) (prims : Primitives p) where
  /-- A second preimage of the honest FORS root vector under `T_k` at `forsPkAdrs adrs`. -/
  | tlCollision (recovered : Vector prims.Y p.k)
  /-- An `H`-collision at the height-`height` node of tree `tree`'s opened root path.  `children`
  is the submitted pair; the honest pair it collides with is not carried here but computed by
  `ForsWitness.Valid` from the honest tree. -/
  | hCollision (tree : Fin p.k) (height : ℕ) (children : prims.Y × prims.Y)
  /-- An `F`-preimage of the honest leaf image at the leaf tree `tree` opens. -/
  | fPreimage (tree : Fin p.k) (value : prims.Y)

/-- The winning condition each witness asserts, against the honest tree that `sk` generates at
`adrs` under the public seed `pk`, at the forged digest `md`.

Write `idx = forsSigLeafIndex p md tree` for the global leaf index the digest opens in tree
`tree`.  Then:

* `tlCollision recovered` asserts a `T_k` second preimage of `forsHonestRoots prims sk pk adrs`
  at `forsPkAdrs adrs`;
* `hCollision tree height children` asserts an `H`-collision at
  `forsNodeAdrs adrs height (idx / 2 ^ height)` between `children` and
  `forsHonestChildren prims sk pk adrs height (idx / 2 ^ height)`, the honest child pair there,
  and pins `0 < height ≤ a`.  Both bounds are load-bearing: `height ≤ a` is what places the
  address in the `forsH` ledger, and `0 < height` is what keeps it out of the `forsF` one —
  `forsNodeAdrs adrs 0 t` is a FORS *leaf* address, and it is also the height at which
  `forsHonestChildren`'s `height - 1` would truncate;
* `fPreimage tree value` asserts that `value` is an `F`-preimage at `forsNodeAdrs adrs 0 idx` of
  the honest leaf image there.  There is deliberately no distinctness conjunct: the FORS-`F`
  branch is an open-preimage witness, and the honest secret value itself is allowed to win.

This is a statement about hash values only.  It does not say that the honest roots, the honest
child pair, or the honest leaf image was committed as a game target, nor that any execution
queried them, nor — in the `fPreimage` case — that the named index was never opened. -/
def ForsWitness.Valid {p : Params} {prims : Primitives p} (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (md : List Byte) : ForsWitness p prims → Prop
  | .tlCollision recovered =>
      recovered ≠ forsHonestRoots prims sk pk adrs ∧
        prims.Tl pk (forsPkAdrs adrs) recovered.toList =
          prims.Tl pk (forsPkAdrs adrs) (forsHonestRoots prims sk pk adrs).toList
  | .hCollision i z c =>
      0 < z ∧ z ≤ p.a ∧
        forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z) ≠ c ∧
        prims.H pk (forsNodeAdrs adrs z (forsSigLeafIndex p md i.val / 2 ^ z))
            (forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z)).1
            (forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z)).2 =
          prims.H pk (forsNodeAdrs adrs z (forsSigLeafIndex p md i.val / 2 ^ z)) c.1 c.2
  | .fPreimage i value =>
      prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val)) value =
        prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val))
          (forsSkGenCore prims.core sk pk adrs (forsSigLeafIndex p md i.val))

/-- Unfolding equation for the `T_k` branch of `ForsWitness.Valid`. -/
@[simp] theorem ForsWitness.valid_tlCollision {prims : Primitives p} (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (md : List Byte) (recovered : Vector prims.Y p.k) :
    (ForsWitness.tlCollision recovered).Valid sk pk adrs md ↔
      recovered ≠ forsHonestRoots prims sk pk adrs ∧
        prims.Tl pk (forsPkAdrs adrs) recovered.toList =
          prims.Tl pk (forsPkAdrs adrs) (forsHonestRoots prims sk pk adrs).toList := Iff.rfl

/-- Unfolding equation for the `H`-collision branch of `ForsWitness.Valid`.  The first pair is the
honest child pair at the named node, read off the honest tree rather than supplied by the
witness. -/
@[simp] theorem ForsWitness.valid_hCollision {prims : Primitives p} (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (md : List Byte) (i : Fin p.k) (z : ℕ)
    (c : prims.Y × prims.Y) :
    (ForsWitness.hCollision i z c).Valid sk pk adrs md ↔
      0 < z ∧ z ≤ p.a ∧
        forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z) ≠ c ∧
        prims.H pk (forsNodeAdrs adrs z (forsSigLeafIndex p md i.val / 2 ^ z))
            (forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z)).1
            (forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z)).2 =
          prims.H pk (forsNodeAdrs adrs z (forsSigLeafIndex p md i.val / 2 ^ z)) c.1 c.2 :=
  Iff.rfl

/-- Unfolding equation for the `F`-preimage branch of `ForsWitness.Valid`. -/
@[simp] theorem ForsWitness.valid_fPreimage {prims : Primitives p} (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (md : List Byte) (i : Fin p.k) (value : prims.Y) :
    (ForsWitness.fPreimage i value).Valid sk pk adrs md ↔
      prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val)) value =
        prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val))
          (forsSkGenCore prims.core sk pk adrs (forsSigLeafIndex p md i.val)) := Iff.rfl

/-- Search tree `i` for an `H`-collision: nothing when the forged leaf image already agrees with
the honest one, and otherwise the collision `PerfectMerkleTree.findCollision` locates on the
opened leaf's root path.

The search does not check that tree `i` climbs to the honest root; that check is the caller's, and
`findForsTreeCollision_sound` carries it as `hroot`.  Without it `findCollision` can still return a
collision — its kernel tests the hash equality before returning `some` — but the first pair it
returns need not be the honest one, so the witness need not be valid.  The malformed-input canary
of `HashSigTest.SLHDSA.ForsWitnesses` exercises exactly that gap. -/
def findForsTreeCollision (prims : Primitives p) [DecidableEq prims.Y]
    (sig : ForsSigCore p prims.core) (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (i : Fin p.k) : Option (ForsWitness p prims) :=
  let idx := forsSigLeafIndex p md i.val
  let y := prims.F pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).sk
  if forsLeaf prims sk pk adrs idx = y then none
  else
    (PerfectMerkleTree.findCollision (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs)
      idx y (sig[i.val]).auth.toList).map fun w => .hCollision i w.1 w.2.2

/-- Compute a FORS witness from a signature on digest `md` against the honest key material at
`adrs`: the recovered root vector when it differs from the honest one — a `T_k` second preimage
exactly when the two FORS public keys agree — then the first tree that yields an `H`-collision,
and otherwise the revealed secret value of the caller-chosen tree `target`.

The first branch is decided by the root vectors alone, not by the two public keys.  On a signature
whose recovered public key differs this therefore still returns a `tlCollision`, and that witness
is *not* valid; ruling it out is exactly what `findForsWitness_sound`'s public-key hypothesis
does, and the malformed-forgery canary of `HashSigTest.SLHDSA.ForsWitnesses` exercises the gap.

`target` is the caller's choice of tree for the preimage branch.  In the source that choice is the
ITSR one — `find (fun i => ! i ∈ lidxs) lidxs'` (`FORS_ES.ec:3223`), the only choice point in the
whole FORS translation — and it needs the signing log, which is not available here.  Every tree is
a sound choice for the hash half of the winning condition; which trees are *unopened* is the
transcript question this module does not answer. -/
def findForsWitness (prims : Primitives p) [DecidableEq prims.Y] (sig : ForsSigCore p prims.core)
    (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (target : Fin p.k) :
    ForsWitness p prims :=
  if forsRecoveredRoots prims sig md pk adrs = forsHonestRoots prims sk pk adrs then
    ((List.finRange p.k).findSome? (findForsTreeCollision prims sig md sk pk adrs)).getD
      (.fPreimage target (sig[target.val]).sk)
  else .tlCollision (forsRecoveredRoots prims sig md pk adrs)

/-- Whatever `findForsTreeCollision` returns satisfies `ForsWitness.Valid` against the honest tree
at `adrs`, provided tree `i` climbs to the honest tree-`i` root.  That hypothesis is what orients
the extracted pair: `PerfectMerkleTree.findCollision_oriented` is what identifies the first pair
`findCollision` returns with the honest child pair at the node it names.

*Deterministic inclusion.* -/
theorem findForsTreeCollision_sound (prims : Primitives p) [DecidableEq prims.Y]
    (sig : ForsSigCore p prims.core) (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (i : Fin p.k)
    (hroot : (forsRecoveredRoots prims sig md pk adrs)[i.val] =
      (forsHonestRoots prims sk pk adrs)[i.val])
    {w : ForsWitness p prims}
    (hw : findForsTreeCollision prims sig md sk pk adrs i = some w) :
    w.Valid sk pk adrs md := by
  rw [findForsTreeCollision] at hw
  split at hw
  · exact absurd hw (by simp)
  · rename_i hleaf
    rw [Option.map_eq_some_iff] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    have hlen : (sig[i.val]).auth.toList.length = p.a := by simp
    have hclimb : PerfectMerkleTree.climb (forsNodeHash prims pk adrs)
          (forsSigLeafIndex p md i.val)
          (prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val)) (sig[i.val]).sk)
          (sig[i.val]).auth.toList =
        PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) p.a
          (forsSigLeafIndex p md i.val / 2 ^ p.a) := by
      rw [forsSigLeafIndex_div_pow_a]
      rw [forsRecoveredRoots_getElem, forsHonestRoots_getElem, forsRoot_eq_merkleRoot] at hroot
      exact hroot
    obtain ⟨z, c, hor⟩ := PerfectMerkleTree.findCollision_oriented
      (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) p.a
      (forsSigLeafIndex p md i.val) _ _ hlen hclimb hleaf
    rw [hor, Option.some.injEq] at hu
    subst hu
    obtain ⟨hzpos, hzle, hne, hcoll⟩ := PerfectMerkleTree.findCollision_sound
      (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) p.a
      (forsSigLeafIndex p md i.val) _ _ hlen z _ c hor
    refine ⟨hzpos, hzle, ?_, ?_⟩
    · rw [forsHonestChildren_eq]; exact hne
    · rw [forsHonestChildren_eq]
      simpa only [forsNodeHash_eq_h, PerfectMerkleTree.honestChildren] using hcoll

/-- The tree search succeeds at every tree that climbs to the honest root with a forged leaf image
different from the honest one: `PerfectMerkleTree.findCollision_oriented` supplies the collision.

*Deterministic inclusion.* -/
theorem findForsTreeCollision_isSome_of_ne (prims : Primitives p) [DecidableEq prims.Y]
    (sig : ForsSigCore p prims.core) (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (i : Fin p.k)
    (hroot : (forsRecoveredRoots prims sig md pk adrs)[i.val] =
      (forsHonestRoots prims sk pk adrs)[i.val])
    (hleaf : forsLeaf prims sk pk adrs (forsSigLeafIndex p md i.val) ≠
      prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val)) (sig[i.val]).sk) :
    (findForsTreeCollision prims sig md sk pk adrs i).isSome := by
  have hlen : (sig[i.val]).auth.toList.length = p.a := by simp
  have hclimb : PerfectMerkleTree.climb (forsNodeHash prims pk adrs)
        (forsSigLeafIndex p md i.val)
        (prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val)) (sig[i.val]).sk)
        (sig[i.val]).auth.toList =
      PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) p.a
        (forsSigLeafIndex p md i.val / 2 ^ p.a) := by
    rw [forsSigLeafIndex_div_pow_a]
    rw [forsRecoveredRoots_getElem, forsHonestRoots_getElem, forsRoot_eq_merkleRoot] at hroot
    exact hroot
  obtain ⟨z, c, hor⟩ := PerfectMerkleTree.findCollision_oriented
    (forsLeaf prims sk pk adrs) (forsNodeHash prims pk adrs) p.a
    (forsSigLeafIndex p md i.val) _ _ hlen hclimb hleaf
  rw [findForsTreeCollision]
  simp only [hleaf, if_false, hor, Option.map_some, Option.isSome_some]

/-- A tree at which the search finds nothing, and which climbs to the honest root, has a forged
leaf image equal to the honest one — the `F`-preimage branch.  Contrapositive of
`findForsTreeCollision_isSome_of_ne`.

*Deterministic inclusion.* -/
theorem findForsTreeCollision_eq_none_imp (prims : Primitives p) [DecidableEq prims.Y]
    (sig : ForsSigCore p prims.core) (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (i : Fin p.k)
    (hroot : (forsRecoveredRoots prims sig md pk adrs)[i.val] =
      (forsHonestRoots prims sk pk adrs)[i.val])
    (hnone : findForsTreeCollision prims sig md sk pk adrs i = none) :
    forsLeaf prims sk pk adrs (forsSigLeafIndex p md i.val) =
      prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val)) (sig[i.val]).sk := by
  by_contra hleaf
  have := findForsTreeCollision_isSome_of_ne prims sig md sk pk adrs i hroot hleaf
  rw [hnone] at this
  exact absurd this (by simp)

/-- **Extractor soundness.**  The witness `findForsWitness` returns satisfies `ForsWitness.Valid`
against the honest tree at `adrs` and the forged digest `md`.

The public-key hypothesis is used only by the `T_k` branch, where it supplies the equality of the
two compressions; the other two branches are guarded by the root-vector test the extractor
performs itself.  As `ForsWitness.Valid` records, this says nothing about whether those honest
objects were committed as game targets, nor — in the preimage branch — about whether `target`'s
leaf index was ever opened.

*Deterministic inclusion.* -/
theorem findForsWitness_sound (prims : Primitives p) [DecidableEq prims.Y]
    (sig : ForsSigCore p prims.core) (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (target : Fin p.k)
    (hpk : forsPkFromSig prims sig md pk adrs = forsPkGen prims sk pk adrs) :
    (findForsWitness prims sig md sk pk adrs target).Valid sk pk adrs md := by
  rw [findForsWitness]
  split
  · rename_i hroots
    rcases hfind : (List.finRange p.k).findSome? (findForsTreeCollision prims sig md sk pk adrs)
      with _ | w
    · rw [Option.getD_none]
      rw [List.findSome?_eq_none_iff] at hfind
      have hleaf := findForsTreeCollision_eq_none_imp prims sig md sk pk adrs target
        (by rw [hroots]) (hfind target (List.mem_finRange target))
      exact forsLeafPreimage prims sk pk adrs _ _ hleaf
    · rw [Option.getD_some]
      obtain ⟨i, -, hi⟩ := List.exists_of_findSome?_eq_some hfind
      exact findForsTreeCollision_sound prims sig md sk pk adrs i (by rw [hroots]) hi
  · rename_i hroots
    refine ⟨hroots, ?_⟩
    exact forsRootsBinding prims sig md sk pk adrs hpk

/-! ## Ledger membership and encoded distinctness

*Transcript transport.*  Every address a witness names at a reachable bottom-layer position is a
member of the slice-1 role ledger it is submitted against, and — under
`EncodedTargetLedgerConditions` — distinct addresses of one ledger carry distinct encoded tweaks.
The three roles are reached separately, because they have three different ledgers:

* the `fPreimage` witness attacks `forsF`, whose ledger is `forsLeafAddresses`
  (`mem_forsLeafAddresses_of_digest`, `forsLeafAdrsKey_injective`);
* the `hCollision` witness attacks `forsH`, whose ledger is `forsTreeAddresses`
  (`mem_forsTreeAddresses_of_digest`, `forsTreeAdrsKey_injective`);
* the `tlCollision` witness attacks `forsTl`, whose ledger is `forsRootAddresses`; its address is
  literally `forsPkAdrs pos.forsAdrs`, which `mem_forsRootAddresses` already lists, so that lemma
  is used directly rather than restated.  Distinctness of its encoded tweaks is
  `forsRootAdrsKey_injective`.

These are statements about the ledgers, not about any execution: nothing here says a logged query
carried the witness values, and nothing here says the `fPreimage` index was unopened. -/

variable {vp : ValidatedParams}

/-- The FORS leaf address a digest names in tree `i` at a reachable bottom position is a listed
`forsF` target.  The address is definitionally `forsLeafAddresses`' own, so this is
`mem_forsLeafAddresses` in the construction's own vocabulary. -/
theorem mem_forsLeafAddresses_of_digest (pos : BottomPosition vp) (md : List Byte)
    (i : Fin vp.params.k) :
    forsNodeAdrs pos.forsAdrs 0 (forsSigLeafIndex vp.params md i.val) ∈ forsLeafAddresses vp :=
  mem_forsLeafAddresses vp pos i ⟨forsIdx vp.params md i.val, forsIdx_lt _ _ _⟩

/-- Every internal node of height `0 < z ≤ a` on the root path of the leaf a digest names in tree
`i` at a reachable bottom position is a listed `forsH` target.  The horizontal index is the global
one: `forsSigLeafIndex_div_lt` turns `idx / 2 ^ z` into the `i * 2 ^ (a - z) + j` shape the ledger
lists, which is FIPS 205 Algorithm 16's own authentication-path index. -/
theorem mem_forsTreeAddresses_of_digest (pos : BottomPosition vp) (md : List Byte)
    (i : Fin vp.params.k) {z : ℕ} (hz : 0 < z) (hza : z ≤ vp.params.a) :
    forsNodeAdrs pos.forsAdrs z (forsSigLeafIndex vp.params md i.val / 2 ^ z) ∈
      forsTreeAddresses vp := by
  obtain ⟨heq, hlt⟩ := forsSigLeafIndex_div_lt vp.params md i.val z hza
  rw [heq]
  exact mem_forsTreeAddresses vp pos i hz hza hlt

/-- Under the encoded-ledger conditions, distinct FORS leaf coordinates carry distinct encoded
tweaks: two `fPreimage` witnesses at different `(position, tree, leaf)` triples attack different
tweaks of `forsFOpenPreProblem`.

The conditions are consumed, not assumed afresh: `approvedEncodedTargetLedgerConditions` discharges
them for every approved profile, so the SHA-2 zero fallback is never treated as unreachable. -/
theorem forsLeafAdrsKey_injective {prims : Primitives vp.params}
    (conditions : EncodedTargetLedgerConditions vp prims) :
    Function.Injective fun coord : (BottomPosition vp × Fin vp.params.k) × Fin vp.params.t =>
      prims.adrsToKey
        (forsNodeAdrs coord.1.1.forsAdrs 0 (coord.1.2.val * vp.params.t + coord.2.val)) := by
  intro c d hcd
  have hnodup : (((allBottomPositions vp).product (List.finRange vp.params.k)).product
      (List.finRange vp.params.t)).Nodup :=
    ((allBottomPositions_nodup vp).product (List.nodup_finRange vp.params.k)).product
      (List.nodup_finRange vp.params.t)
  have hmem : ∀ e : (BottomPosition vp × Fin vp.params.k) × Fin vp.params.t,
      e ∈ ((allBottomPositions vp).product (List.finRange vp.params.k)).product
        (List.finRange vp.params.t) := by
    rintro ⟨⟨pos, tree⟩, leaf⟩; simp
  have hinj := (encodeTargets_nodup_iff_injOn prims (forsLeafAddresses vp)
    (forsLeafAddresses_nodup vp)).1 conditions.forsF
  have hadrs := hinj _ (mem_forsLeafAddresses vp c.1.1 c.1.2 c.2) _
    (mem_forsLeafAddresses vp d.1.1 d.1.2 d.2) hcd
  exact (List.nodup_map_iff_inj_on hnodup).1 (forsLeafAddresses_nodup vp) c (hmem c) d (hmem d)
    hadrs

/-- Under the encoded-ledger conditions, distinct FORS internal-node coordinates carry distinct
encoded tweaks: two `hCollision` witnesses at different `(position, tree, height, index)` tuples
attack different tweaks of `forsHTcrCProblem`.

The coordinate is stated in the bounded form a witness produces — `0 < z ≤ a` and a horizontal
index below `2 ^ (a - z)` — because those are exactly the coordinates `forsTreeAddresses` lists.
The conditions are consumed, not assumed afresh. -/
theorem forsTreeAdrsKey_injective {prims : Primitives vp.params}
    (conditions : EncodedTargetLedgerConditions vp prims)
    {pos pos' : BottomPosition vp} {i i' : Fin vp.params.k} {z z' j j' : ℕ}
    (hz : 0 < z) (hza : z ≤ vp.params.a) (hj : j < 2 ^ (vp.params.a - z))
    (hz' : 0 < z') (hza' : z' ≤ vp.params.a) (hj' : j' < 2 ^ (vp.params.a - z'))
    (hkey : prims.adrsToKey (forsNodeAdrs pos.forsAdrs z (i.val * 2 ^ (vp.params.a - z) + j)) =
      prims.adrsToKey (forsNodeAdrs pos'.forsAdrs z' (i'.val * 2 ^ (vp.params.a - z') + j'))) :
    pos = pos' ∧ i = i' ∧ z = z' ∧ j = j' := by
  have hnodup : (((allBottomPositions vp).product (List.finRange vp.params.k)).product
      (perfectInternalCoords vp.params.a)).Nodup :=
    ((allBottomPositions_nodup vp).product (List.nodup_finRange vp.params.k)).product
      (perfectInternalCoords_nodup vp.params.a)
  have hmemc : ((pos, i), (z, j)) ∈
      ((allBottomPositions vp).product (List.finRange vp.params.k)).product
        (perfectInternalCoords vp.params.a) := by
    simp [mem_perfectInternalCoords_of_bounds hz hza hj]
  have hmemd : ((pos', i'), (z', j')) ∈
      ((allBottomPositions vp).product (List.finRange vp.params.k)).product
        (perfectInternalCoords vp.params.a) := by
    simp [mem_perfectInternalCoords_of_bounds hz' hza' hj']
  have hinj := (encodeTargets_nodup_iff_injOn prims (forsTreeAddresses vp)
    (forsTreeAddresses_nodup vp)).1 conditions.forsH
  have hadrs := hinj _ (mem_forsTreeAddresses vp pos i hz hza hj) _
    (mem_forsTreeAddresses vp pos' i' hz' hza' hj') hkey
  have hcoord := (List.nodup_map_iff_inj_on hnodup).1 (forsTreeAddresses_nodup vp)
    ((pos, i), (z, j)) hmemc ((pos', i'), (z', j')) hmemd hadrs
  simp only [Prod.mk.injEq] at hcoord
  exact ⟨hcoord.1.1, hcoord.1.2, hcoord.2.1, hcoord.2.2⟩

/-- Under the encoded-ledger conditions, distinct bottom-layer positions carry distinct encoded
FORS-root-compression tweaks: two `tlCollision` witnesses at different positions attack different
tweaks of `forsTlTcrCProblem`. -/
theorem forsRootAdrsKey_injective {prims : Primitives vp.params}
    (conditions : EncodedTargetLedgerConditions vp prims) :
    Function.Injective fun pos : BottomPosition vp =>
      prims.adrsToKey (forsPkAdrs pos.forsAdrs) := by
  intro pos pos' h
  have hinj := (encodeTargets_nodup_iff_injOn prims (forsRootAddresses vp)
    (forsRootAddresses_nodup vp)).1 conditions.forsTl
  have hadrs := hinj _ (mem_forsRootAddresses vp pos) _ (mem_forsRootAddresses vp pos') h
  exact (List.nodup_map_iff_inj_on (allBottomPositions_nodup vp)).1
    (forsRootAddresses_nodup vp) pos (mem_allBottomPositions vp pos) pos'
    (mem_allBottomPositions vp pos') hadrs

/-! ## Game shapes

`ForsWitness.Valid` is stated in the construction's own vocabulary (`prims.F`, `prims.H`,
`prims.Tl` at a structural `Adrs`).  These three bridges rewrite it into the canonical games'
`eval` vocabulary at the encoded tweak, using the attacked-member equations of
`HashSig.SLHDSA.Security.CanonicalGames`.  Each takes explicitly only the honest objects its own
branch mentions; the others are implicit and read off the hypothesis.  They change presentation
only: no game is played and no advantage is stated.

The `fPreimage` bridge lands in `forsFOpenPreProblem` and not in `forsFTcrProblem`, for the reason
the case-analysis section gives.  Slice 6's `forsFTcrProblem_eq_toTCR` and
`forsFDsprProblem_eq_toDSPR` are the route to the other two FORS-`F` games, and they are generic;
nothing here needs a TCR- or DSPR-shaped FORS-`F` bridge. -/

variable (prims : Primitives p)

/-- The `T_k` branch, read in `forsTlTcrCProblem`'s vocabulary: two distinct root vectors with the
same evaluation at the encoded compression tweak. -/
theorem forsWitness_valid_tlCollision_eval [SampleableType prims.PkSeed] (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) {md : List Byte} (recovered : Vector prims.Y p.k)
    (h : (ForsWitness.tlCollision recovered).Valid sk pk adrs md) :
    recovered ≠ forsHonestRoots prims sk pk adrs ∧
      (forsTlTcrCProblem prims).th.eval pk (prims.adrsToKey (forsPkAdrs adrs)) recovered =
        (forsTlTcrCProblem prims).th.eval pk (prims.adrsToKey (forsPkAdrs adrs))
          (forsHonestRoots prims sk pk adrs) :=
  ⟨h.1, by
    rw [forsTlTcrCProblem_eval_adrsToKey, forsTlTcrCProblem_eval_adrsToKey]
    exact h.2⟩

/-- The `H`-collision branch, read in `forsHTcrCProblem`'s vocabulary: the submitted pair and the
honest child pair at the named node are distinct and evaluate equally at the encoded node tweak.
The game's message type is the ordered pair `prims.Y × prims.Y`, so the two children are supplied
as one message and their order is part of the claim. -/
theorem forsWitness_valid_hCollision_eval [SampleableType prims.PkSeed] (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (md : List Byte) (i : Fin p.k) (z : ℕ)
    (c : prims.Y × prims.Y) (h : (ForsWitness.hCollision i z c).Valid sk pk adrs md) :
    0 < z ∧ z ≤ p.a ∧
      forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z) ≠ c ∧
      (forsHTcrCProblem prims).th.eval pk
          (prims.adrsToKey (forsNodeAdrs adrs z (forsSigLeafIndex p md i.val / 2 ^ z)))
          (forsHonestChildren prims sk pk adrs z (forsSigLeafIndex p md i.val / 2 ^ z)) =
        (forsHTcrCProblem prims).th.eval pk
          (prims.adrsToKey (forsNodeAdrs adrs z (forsSigLeafIndex p md i.val / 2 ^ z))) c :=
  ⟨h.1, h.2.1, h.2.2.1, by
    rw [forsHTcrCProblem_eval_adrsToKey, forsHTcrCProblem_eval_adrsToKey]
    exact h.2.2.2⟩

/-- The `F`-preimage branch, read in `forsFOpenPreProblem`'s vocabulary: the submitted value
evaluates to the honest leaf image at the encoded leaf tweak.  This is the hash half of that
game's winning condition; the other half, that the index was never opened, is not established
here. -/
theorem forsWitness_valid_fPreimage_eval [SampleableType prims.PkSeed] [SampleableType prims.Y]
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (md : List Byte) (i : Fin p.k)
    (value : prims.Y) (h : (ForsWitness.fPreimage i value).Valid sk pk adrs md) :
    (forsFOpenPreProblem prims).th.eval pk
        (prims.adrsToKey (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val))) value =
      prims.F pk (forsNodeAdrs adrs 0 (forsSigLeafIndex p md i.val))
        (forsSkGenCore prims.core sk pk adrs (forsSigLeafIndex p md i.val)) := by
  rw [forsFOpenPreProblem_eval_adrsToKey]
  exact h

end SLHDSA.Security
