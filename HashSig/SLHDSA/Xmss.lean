/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Bolton Bailey
-/

module
public import HashSig.SLHDSA.Wots
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound

/-!
# XMSS (FIPS 205 §6)

XMSS (`xmssNode`, `xmssSign`, `xmssPkFromSig`; Algorithms 9–11) is the node-addressed perfect
Merkle tree `PerfectMerkleTree` with WOTS+ public keys as leaves and `H` under the `TREE` address
of each node as the node hash. The canonical `xmss*M` programs depend only on `CorePrimitives`
and issue every public hash through `HasQuery`; they therefore cannot inspect a concrete `Thash`
implementation. The pure `Primitives` API is literally the deterministic interpretation of those
programs by `simulateQ (PublicHash.impl prims)`. The lower-level `*With` combinators expose the
same callback-parametric control flow for naturality and composition proofs.
The Merkle layer is itself the generic `AddressedMerkleTree` engine specialised to heap-style
`(height, index)` addressing, so its completeness, naturality, and oriented binding theorems are
available here:

* `xmssPkFromSig_xmssSign` — XMSS correctness, from `PerfectMerkleTree.climb_authPath` together
  with WOTS+ correctness (`wotsPkFromSig_wotsSign`);
* `xmssPkFromSig_binding` — an XMSS signature whose recovered leaf differs from the honest WOTS+
  public key but which still recovers the honest root exhibits a collision of `H` at the `TREE`
  address `(h, idx / 2 ^ h)` of an ancestor of leaf `idx`, against the honestly precommitted
  child pair. This deterministic statement is the Merkle-layer hook needed by a future
  seed-aware multi-target target-collision reduction; it is not itself such a reduction.

## References

- NIST FIPS 205, §6 (Algorithms 9–11)
-/

@[expose] public section


namespace SLHDSA

open OracleComp

variable {p : Params}

/-! ### XMSS over WOTS+ leaves (FIPS 205 §6) -/

/-- Base WOTS+ address for the leaf at keypair index `t` (type `WOTS_HASH`). -/
def wotsLeafAdrs (adrs : Adrs) (t : ℕ) : Adrs :=
  (adrs.setTypeAndClear .wotsHash).setKeyPairAddress t

/-- The `TREE`-type address of the XMSS node at tree position `(height z, index t)`. -/
def xmssNodeAdrs (adrs : Adrs) (z t : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .tree).setTreeHeight z).setTreeIndex t

/-- An XMSS signature whose WOTS+ component and authentication path have their FIPS-prescribed
lengths in the type, so no caller-supplied length invariant is needed downstream. -/
structure XmssSigCore (p : Params) (core : CorePrimitives p) where
  /-- The `len` WOTS+ chain values. -/
  wots : WotsSig p core
  /-- The `h'` sibling nodes, from the leaf level upward. -/
  auth : Vector core.Y p.hp

/-- Alias for the canonical intrinsically shaped XMSS signature. -/
abbrev XmssSig := XmssSigCore

/-! ### Low-level callback-parametric helpers -/

/-- Callback-parametric XMSS leaf computation: generate the WOTS+ public key at leaf `t`. -/
def xmssLeafWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) : m core.Y :=
  wotsPkGenWith core hash compress sk pk (wotsLeafAdrs adrs t)

/-- Apply the callback for the XMSS internal node at `(height z, index t)`. -/
def xmssNodeHashWith {Y : Type} {m : Type → Type*}
    (nodeHash : Adrs → Y → Y → m Y) (adrs : Adrs)
    (z t : ℕ) (l r : Y) : m Y :=
  nodeHash (xmssNodeAdrs adrs z t) l r

/-- Low-level callback-parametric subtree root at `(height z, index t)`. -/
def xmssNodeWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) : m core.Y :=
  PerfectMerkleTree.merkleRootM (xmssLeafWith core hash compress sk pk adrs)
    (xmssNodeHashWith nodeHash adrs) z t

/-- Low-level callback-parametric XMSS tree root. -/
def xmssRootWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) : m core.Y :=
  xmssNodeWith core hash compress nodeHash sk pk adrs p.hp 0

/-- Low-level callback-parametric XMSS signing. Following FIPS 205 Algorithm 10,
the sibling-only authentication path is computed before the WOTS+ signature. -/
def xmssSignWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) : m (XmssSig p core) := do
  let path ← PerfectMerkleTree.intrinsicAuthPathM
    (xmssLeafWith core hash compress sk pk adrs)
    (xmssNodeHashWith nodeHash adrs) idx p.hp
  let sig ← wotsSignWith core hash msg sk pk (wotsLeafAdrs adrs idx)
  return ⟨sig, path⟩

/-- Low-level callback-parametric XMSS root recovery. The WOTS+ public key is
recovered before the authentication path is climbed. -/
def xmssPkFromSigWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (idx : ℕ) (sig : XmssSig p core) (msg : core.Y) (adrs : Adrs) : m core.Y := do
  let leaf ← wotsPkFromSigWith core hash compress sig.wots msg (wotsLeafAdrs adrs idx)
  PerfectMerkleTree.climbM (xmssNodeHashWith nodeHash adrs) idx leaf sig.auth.toList

/-! ### Canonical explicit-public-hash programs -/

/-- Canonical explicit-public-hash XMSS leaf computation. -/
def xmssLeafM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) : m core.Y :=
  xmssLeafWith core (PublicHash.f core pk) (PublicHash.tl core pk) sk pk adrs t

/-- Canonical explicit-public-hash XMSS internal-node computation. -/
def xmssNodeHashM (core : CorePrimitives p) {m : Type → Type*}
    [HasQuery (publicHashSpec core) m] (pk : core.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : core.Y) : m core.Y :=
  xmssNodeHashWith (PublicHash.h core pk) adrs z t l r

/-- Canonical explicit-public-hash XMSS subtree-root computation. -/
def xmssNodeM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) : m core.Y :=
  xmssNodeWith core (PublicHash.f core pk) (PublicHash.tl core pk)
    (PublicHash.h core pk) sk pk adrs z t

/-- Canonical explicit-public-hash XMSS tree-root computation. -/
def xmssRootM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) : m core.Y :=
  xmssRootWith core (PublicHash.f core pk) (PublicHash.tl core pk)
    (PublicHash.h core pk) sk pk adrs

/-- Canonical explicit-public-hash XMSS signing. -/
def xmssSignM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) : m (XmssSig p core) :=
  xmssSignWith core (PublicHash.f core pk) (PublicHash.tl core pk)
    (PublicHash.h core pk) msg sk pk adrs idx

/-- Canonical explicit-public-hash XMSS root recovery. -/
def xmssPkFromSigM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (idx : ℕ) (sig : XmssSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) : m core.Y :=
  xmssPkFromSigWith core (PublicHash.f core pk) (PublicHash.tl core pk)
    (PublicHash.h core pk) idx sig msg adrs

/-! ### Pure deterministic interpretations -/

/-- The XMSS leaf value at index `t`: the WOTS+ public key of keypair `t`. -/
def xmssLeaf (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (t : ℕ) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (xmssLeafM prims.core sk pk adrs t : OracleComp (publicHashSpec prims.core) prims.Y)

/-- The XMSS internal-node hash at tree position `(height z, index t)` (type `TREE`). -/
def xmssNodeHash (prims : Primitives p) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : prims.Y) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (xmssNodeHashM prims.core pk adrs z t l r :
      OracleComp (publicHashSpec prims.core) prims.Y)

/-- The XMSS subtree root at `(height z, index t)` (FIPS 205 Algorithm 9). -/
def xmssNode (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (xmssNodeM prims.core sk pk adrs z t : OracleComp (publicHashSpec prims.core) prims.Y)

/-- The XMSS tree root (height `h'`, index `0`) — the value committed by key generation. -/
def xmssRoot (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  simulateQ (PublicHash.impl prims)
    (xmssRootM prims.core sk pk adrs : OracleComp (publicHashSpec prims.core) prims.Y)

/-- XMSS signing (FIPS 205 Algorithm 10): WOTS+-sign at leaf `idx` and emit the auth path. -/
def xmssSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) : XmssSig p prims :=
  simulateQ (PublicHash.impl prims)
    (xmssSignM prims.core msg sk pk adrs idx :
      OracleComp (publicHashSpec prims.core) (XmssSig p prims.core))

/-- XMSS root recovery from a signature (FIPS 205 Algorithm 11): recover the WOTS+ public key
(the leaf) then climb the auth path. -/
def xmssPkFromSig (prims : Primitives p) (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (xmssPkFromSigM prims.core idx sig msg pk adrs :
      OracleComp (publicHashSpec prims.core) prims.Y)

/-! ### Pure API equations -/

/-- The deterministic interpretation preserves the established WOTS+-leaf equation. -/
@[simp]
theorem xmssLeaf_eq_wotsPkGen (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    xmssLeaf prims sk pk adrs t = wotsPkGen prims sk pk (wotsLeafAdrs adrs t) := by
  rfl

/-- The deterministic interpretation preserves the established addressed node-hash equation. -/
@[simp]
theorem xmssNodeHash_eq_h (prims : Primitives p) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : prims.Y) :
    xmssNodeHash prims pk adrs z t l r = prims.H pk (xmssNodeAdrs adrs z t) l r := by
  rfl

/-- The deterministic interpretation preserves the established pure perfect-subtree equation. -/
@[simp]
theorem xmssNode_eq_merkleRoot (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) :
    xmssNode prims sk pk adrs z t =
      PerfectMerkleTree.merkleRoot (xmssLeaf prims sk pk adrs)
        (xmssNodeHash prims pk adrs) z t := by
  unfold xmssNode xmssNodeM xmssNodeWith
  rw [PerfectMerkleTree.simulateQ_merkleRootM]
  rfl

/-- The deterministic interpretation preserves the established height-`h'` root equation. -/
@[simp]
theorem xmssRoot_eq_node (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    xmssRoot prims sk pk adrs = xmssNode prims sk pk adrs p.hp 0 := by
  rfl

/-- The pure signing API contains the WOTS+ signature and the intrinsically shaped FIPS
authentication path. -/
@[simp]
theorem xmssSign_eq_pair (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) :
    xmssSign prims msg sk pk adrs idx =
      ⟨wotsSign prims msg sk pk (wotsLeafAdrs adrs idx),
        PerfectMerkleTree.intrinsicAuthPath (xmssLeaf prims sk pk adrs)
          (xmssNodeHash prims pk adrs) idx p.hp⟩ := by
  unfold xmssSign xmssSignM xmssSignWith
  change simulateQ (PublicHash.impl prims) (do
    let path ← PerfectMerkleTree.intrinsicAuthPathM (xmssLeafM prims.core sk pk adrs)
      (xmssNodeHashM prims.core pk adrs) idx p.hp
    let sig ← wotsSignM prims.core msg sk pk (wotsLeafAdrs adrs idx)
    return XmssSigCore.mk sig path) = _
  simp only [simulateQ_bind, simulateQ_pure]
  rw [PerfectMerkleTree.simulateQ_intrinsicAuthPathM, simulateQ_wotsSignM]
  rfl

/-- The pure recovery API first recovers the WOTS+ leaf and then climbs the authentication path. -/
@[simp]
theorem xmssPkFromSig_eq_climb (prims : Primitives p) (idx : ℕ)
    (sig : XmssSig p prims) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    xmssPkFromSig prims idx sig msg pk adrs =
      PerfectMerkleTree.climb (xmssNodeHash prims pk adrs) idx
        (wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx)) sig.auth.toList := by
  unfold xmssPkFromSig
  change simulateQ (PublicHash.impl prims) (do
    let leaf ← wotsPkFromSigM prims.core sig.wots msg pk (wotsLeafAdrs adrs idx)
    PerfectMerkleTree.climbM (xmssNodeHashM prims.core pk adrs) idx leaf sig.auth.toList) = _
  simp only [simulateQ_bind, simulateQ_wotsPkFromSigM]
  simp_rw [PerfectMerkleTree.simulateQ_climbM]
  rfl

/-! ### Naturality -/

/-- A monad morphism commutes with XMSS leaf generation when it commutes with both WOTS+
callbacks. -/
theorem xmssLeafWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y)
    (compressn : Adrs → List core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) :
    F (xmssLeafWith core hashm compressm sk pk adrs t) =
      xmssLeafWith core hashn compressn sk pk adrs t :=
  wotsPkGenWith_natural F core hashm hashn compressm compressn
    hhash hcompress sk pk (wotsLeafAdrs adrs t)

/-- A monad morphism commutes with addressed XMSS node hashing when it commutes with the node
callback. -/
theorem xmssNodeHashWith_natural {Y : Type} {m n : Type → Type*} [Monad m] [Monad n]
    (F : m →ᵐ n) (hashm : Adrs → Y → Y → m Y) (hashn : Adrs → Y → Y → n Y)
    (hhash : ∀ a l r, F (hashm a l r) = hashn a l r)
    (adrs : Adrs) (z t : ℕ) (l r : Y) :
    F (xmssNodeHashWith hashm adrs z t l r) = xmssNodeHashWith hashn adrs z t l r :=
  hhash _ l r

/-- A monad morphism commutes with XMSS subtree-root computation when it commutes with every
public-hash callback. -/
theorem xmssNodeWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y)
    (compressn : Adrs → List core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) :
    F (xmssNodeWith core hashm compressm nodeHashm sk pk adrs z t) =
      xmssNodeWith core hashn compressn nodeHashn sk pk adrs z t := by
  apply PerfectMerkleTree.merkleRootM_natural F
  · intro i
    exact xmssLeafWith_natural F core hashm hashn compressm compressn
      hhash hcompress sk pk adrs i
  · intro h i l r
    exact xmssNodeHashWith_natural F nodeHashm nodeHashn hnode adrs h i l r

/-- A monad morphism commutes with XMSS root computation under pointwise callback maps. -/
theorem xmssRootWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y)
    (compressn : Adrs → List core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    F (xmssRootWith core hashm compressm nodeHashm sk pk adrs) =
      xmssRootWith core hashn compressn nodeHashn sk pk adrs :=
  xmssNodeWith_natural F core hashm hashn compressm compressn nodeHashm nodeHashn
    hhash hcompress hnode sk pk adrs p.hp 0

/-- A monad morphism commutes with XMSS signing under pointwise callback maps. -/
theorem xmssSignWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y)
    (compressn : Adrs → List core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    F (xmssSignWith core hashm compressm nodeHashm msg sk pk adrs idx) =
      xmssSignWith core hashn compressn nodeHashn msg sk pk adrs idx := by
  simp only [xmssSignWith, F.mmap_bind]
  simp_rw [wotsSignWith_natural F core hashm hashn hhash]
  simp_rw [PerfectMerkleTree.intrinsicAuthPathM_natural F
    (xmssLeafWith core hashm compressm sk pk adrs)
    (xmssNodeHashWith nodeHashm adrs)
    (xmssLeafWith core hashn compressn sk pk adrs)
    (xmssNodeHashWith nodeHashn adrs)
    (fun i => xmssLeafWith_natural F core hashm hashn compressm compressn
      hhash hcompress sk pk adrs i)
    (fun h i l r => xmssNodeHashWith_natural F nodeHashm nodeHashn hnode adrs h i l r)]
  simp [F.mmap_pure]

/-- A monad morphism commutes with XMSS recovery under pointwise callback maps. -/
theorem xmssPkFromSigWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y)
    (compressn : Adrs → List core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (idx : ℕ) (sig : XmssSig p core) (msg : core.Y) (adrs : Adrs) :
    F (xmssPkFromSigWith core hashm compressm nodeHashm idx sig msg adrs) =
      xmssPkFromSigWith core hashn compressn nodeHashn idx sig msg adrs := by
  simp only [xmssPkFromSigWith, F.mmap_bind]
  simp_rw [wotsPkFromSigWith_natural F core hashm hashn compressm compressn hhash hcompress]
  simp_rw [PerfectMerkleTree.climbM_natural F _ _
    (fun h i l r => xmssNodeHashWith_natural F nodeHashm nodeHashn hnode adrs h i l r)]

private theorem queryHom_publicHash (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (q : PublicHashQuery core.PkSeed core.AdrsKey core.Y) :
    F.toMonadHom (query (spec := publicHashSpec core) q) =
      query (spec := publicHashSpec core) q :=
  HasQuery.map_query F q

private theorem queryHom_f (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n) (pk : core.PkSeed) :
    ∀ a y, F.toMonadHom (PublicHash.f core pk a y) = PublicHash.f core pk a y := by
  intro a y
  unfold PublicHash.f
  exact queryHom_publicHash core F (.thash pk (core.adrsToKey a) [y])

private theorem queryHom_tl (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n) (pk : core.PkSeed) :
    ∀ a ys, F.toMonadHom (PublicHash.tl core pk a ys) = PublicHash.tl core pk a ys := by
  intro a ys
  unfold PublicHash.tl
  exact queryHom_publicHash core F (.thash pk (core.adrsToKey a) ys)

private theorem queryHom_h (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n) (pk : core.PkSeed) :
    ∀ a l r, F.toMonadHom (PublicHash.h core pk a l r) = PublicHash.h core pk a l r := by
  intro a l r
  unfold PublicHash.h
  exact queryHom_publicHash core F (.thash pk (core.adrsToKey a) [l, r])

/-- Query-preserving monad morphisms commute with explicit XMSS leaf generation. -/
theorem xmssLeafM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) :
    F.toMonadHom (xmssLeafM core sk pk adrs t) = xmssLeafM core sk pk adrs t := by
  apply xmssLeafWith_natural F.toMonadHom core
  · exact queryHom_f core F pk
  · exact queryHom_tl core F pk

/-- Query-preserving monad morphisms commute with one explicit XMSS node-hash query. -/
theorem xmssNodeHashM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [Monad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) (l r : core.Y) :
    F.toMonadHom (xmssNodeHashM core pk adrs z t l r) =
      xmssNodeHashM core pk adrs z t l r :=
  xmssNodeHashWith_natural F.toMonadHom _ _ (queryHom_h core F pk) adrs z t l r

/-- Query-preserving monad morphisms commute with explicit XMSS subtree-root computation. -/
theorem xmssNodeM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) :
    F.toMonadHom (xmssNodeM core sk pk adrs z t) = xmssNodeM core sk pk adrs z t := by
  apply xmssNodeWith_natural F.toMonadHom core
  · exact queryHom_f core F pk
  · exact queryHom_tl core F pk
  · exact queryHom_h core F pk

/-- Query-preserving monad morphisms commute with explicit XMSS root computation. -/
theorem xmssRootM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    F.toMonadHom (xmssRootM core sk pk adrs) = xmssRootM core sk pk adrs := by
  apply xmssRootWith_natural F.toMonadHom core
  · exact queryHom_f core F pk
  · exact queryHom_tl core F pk
  · exact queryHom_h core F pk

/-- Query-preserving monad morphisms commute with explicit XMSS signing. -/
theorem xmssSignM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    F.toMonadHom (xmssSignM core msg sk pk adrs idx) =
      xmssSignM core msg sk pk adrs idx := by
  apply xmssSignWith_natural F.toMonadHom core
  · exact queryHom_f core F pk
  · exact queryHom_tl core F pk
  · exact queryHom_h core F pk

/-- Query-preserving monad morphisms commute with explicit XMSS root recovery. -/
theorem xmssPkFromSigM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (idx : ℕ) (sig : XmssSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) :
    F.toMonadHom (xmssPkFromSigM core idx sig msg pk adrs) =
      xmssPkFromSigM core idx sig msg pk adrs := by
  apply xmssPkFromSigWith_natural F.toMonadHom core
  · exact queryHom_f core F pk
  · exact queryHom_tl core F pk
  · exact queryHom_h core F pk

/-! ### Structural query bounds -/

/-- Closed-form public-hash budget for one height-`z` XMSS subtree: `2 ^ z` WOTS+ leaves at
`p.len * (p.w - 1) + 1` queries each and `2 ^ z - 1` internal nodes at one query each. -/
def xmssNodeQueryBound (p : Params) (z : ℕ) : ℕ :=
  2 ^ z * (p.len * (p.w - 1) + 1) + (2 ^ z - 1) * 1

/-- Closed-form public-hash budget for a sibling-only height-`z` authentication path, specialized
from the generic Merkle bound with WOTS+ leaf budget `p.len * (p.w - 1) + 1` and internal-node
budget `1`. -/
def xmssAuthPathQueryBound (p : Params) (z : ℕ) : ℕ :=
  (2 ^ z - 1) * (p.len * (p.w - 1) + 1) + (2 ^ z - z - 1) * 1

private theorem xmssNodeHashM_isTotalQueryBound_one (core : CorePrimitives p)
    (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) (l r : core.Y) :
    IsTotalQueryBound
      (xmssNodeHashM core pk adrs z t l r :
        OracleComp (publicHashSpec core) core.Y) 1 := by
  simp [xmssNodeHashM, xmssNodeHashWith, PublicHash.h, IsTotalQueryBound]

/-- An XMSS subtree root stays within its structural leaf-and-parent query budget. -/
theorem xmssNodeM_isTotalQueryBound (core : CorePrimitives p)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) :
    IsTotalQueryBound
      (xmssNodeM core sk pk adrs z t : OracleComp (publicHashSpec core) core.Y)
      (xmssNodeQueryBound p z) := by
  change IsTotalQueryBound
    (PerfectMerkleTree.merkleRootM (xmssLeafM core sk pk adrs)
      (xmssNodeHashM core pk adrs) z t) _
  simpa [xmssNodeQueryBound] using
    (PerfectMerkleTree.isTotalQueryBound_merkleRootM
      (xmssLeafM core sk pk adrs) (xmssNodeHashM core pk adrs)
      (p.len * (p.w - 1) + 1) 1 z t
      (fun i => by
        simpa [xmssLeafM, xmssLeafWith, wotsPkGenM] using
          wotsPkGenM_isTotalQueryBound core sk pk (wotsLeafAdrs adrs i))
      (fun h i l r => xmssNodeHashM_isTotalQueryBound_one core pk adrs h i l r))

/-- XMSS root generation has the subtree budget at the parameter-set height. -/
theorem xmssRootM_isTotalQueryBound (core : CorePrimitives p)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (xmssRootM core sk pk adrs : OracleComp (publicHashSpec core) core.Y)
      (xmssNodeQueryBound p p.hp) :=
  xmssNodeM_isTotalQueryBound core sk pk adrs p.hp 0

/-- The sibling-only authentication-path program stays within the sum of one sibling subtree
at every level. -/
theorem xmssAuthPathM_isTotalQueryBound (core : CorePrimitives p)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idx z : ℕ) :
    IsTotalQueryBound
      (PerfectMerkleTree.intrinsicAuthPathM (xmssLeafM core sk pk adrs)
        (xmssNodeHashM core pk adrs) idx z :
          OracleComp (publicHashSpec core) (Vector core.Y z))
      (xmssAuthPathQueryBound p z) := by
  simpa [xmssAuthPathQueryBound] using
    (PerfectMerkleTree.isTotalQueryBound_intrinsicAuthPathM
      (xmssLeafM core sk pk adrs) (xmssNodeHashM core pk adrs)
      (p.len * (p.w - 1) + 1) 1 idx z
      (fun i => by
        simpa [xmssLeafM, xmssLeafWith, wotsPkGenM] using
          wotsPkGenM_isTotalQueryBound core sk pk (wotsLeafAdrs adrs i))
      (fun h i l r => xmssNodeHashM_isTotalQueryBound_one core pk adrs h i l r))

/-- Climbing an XMSS authentication path makes at most one public node-hash query per entry. -/
theorem xmssClimbM_isTotalQueryBound (core : CorePrimitives p)
    (pk : core.PkSeed) (adrs : Adrs) (idx : ℕ) (node : core.Y)
    (auth : List core.Y) :
    IsTotalQueryBound
      (PerfectMerkleTree.climbM (xmssNodeHashM core pk adrs) idx node auth :
        OracleComp (publicHashSpec core) core.Y)
      auth.length := by
  simpa using
    PerfectMerkleTree.isTotalQueryBound_climbM (xmssNodeHashM core pk adrs) 1 idx node auth
      (fun h i l r => xmssNodeHashM_isTotalQueryBound_one core pk adrs h i l r)

/-- XMSS recovery is bounded by the complementary WOTS+ chains, one `T_l` compression, and one
node hash per supplied authentication-path entry. -/
theorem xmssPkFromSigM_isTotalQueryBound (core : CorePrimitives p)
    (idx : ℕ) (sig : XmssSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (xmssPkFromSigM core idx sig msg pk adrs :
        OracleComp (publicHashSpec core) core.Y)
      ((∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) + 1 + p.hp) := by
  change IsTotalQueryBound (do
    let leaf ← wotsPkFromSigM core sig.wots msg pk (wotsLeafAdrs adrs idx)
    PerfectMerkleTree.climbM (xmssNodeHashM core pk adrs) idx leaf sig.auth.toList) _
  exact isTotalQueryBound_bind
    (wotsPkFromSigM_isTotalQueryBound core sig.wots msg pk (wotsLeafAdrs adrs idx)) fun leaf =>
      by simpa using xmssClimbM_isTotalQueryBound core pk adrs idx leaf sig.auth.toList

/-- XMSS signing composes the message-selected WOTS+ chain budget with the sibling-subtree
authentication-path budget. -/
theorem xmssSignM_isTotalQueryBound (core : CorePrimitives p)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    IsTotalQueryBound
      (xmssSignM core msg sk pk adrs idx :
        OracleComp (publicHashSpec core) (XmssSig p core))
      ((∑ i : Fin p.len, chainStepsCore core msg i.val) +
        xmssAuthPathQueryBound p p.hp) := by
  unfold xmssSignM xmssSignWith
  change IsTotalQueryBound (do
    let path ← PerfectMerkleTree.intrinsicAuthPathM (xmssLeafM core sk pk adrs)
      (xmssNodeHashM core pk adrs) idx p.hp
    let sig ← wotsSignM core msg sk pk (wotsLeafAdrs adrs idx)
    return XmssSigCore.mk sig path) _
  have hbound := isTotalQueryBound_bind
    (xmssAuthPathM_isTotalQueryBound core sk pk adrs idx p.hp) fun path =>
      isTotalQueryBound_bind
        (wotsSignM_isTotalQueryBound core msg sk pk (wotsLeafAdrs adrs idx)) fun sig =>
          show IsTotalQueryBound
            (pure ⟨sig, path⟩ : OracleComp (publicHashSpec core) (XmssSig p core)) 0 from
              trivial
  simpa [Nat.add_comm] using hbound

/-- Signing followed by recovery stays within one complete pass over every WOTS+ chain, one
`T_l` compression, the sibling-only authentication-path budget, and one climb hash per tree
level. This is an upper bound on the free-oracle program, not a claim about distinct cache
misses. -/
theorem xmssSignM_then_xmssPkFromSigM_isTotalQueryBound (core : CorePrimitives p)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    IsTotalQueryBound ((do
      let sig ← xmssSignM core msg sk pk adrs idx
      xmssPkFromSigM core idx sig msg pk adrs) :
        OracleComp (publicHashSpec core) core.Y)
      ((p.len * (p.w - 1) + 1) + xmssAuthPathQueryBound p p.hp + p.hp) := by
  have hbound := isTotalQueryBound_bind
    (xmssSignM_isTotalQueryBound core msg sk pk adrs idx) fun sig =>
      xmssPkFromSigM_isTotalQueryBound core idx sig msg pk adrs
  have hsum :
      (∑ i : Fin p.len, chainStepsCore core msg i.val) +
          (∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) =
        p.len * (p.w - 1) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [Nat.add_sub_of_le (chainStepsCore_le core msg _)]
    simp
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hsum] using hbound

/-! ### Deterministic interpretations -/

/-- A fixed deterministic answer table turns explicit XMSS leaf generation into pure WOTS+
key generation for the induced primitive bundle. -/
@[simp]
theorem simulateQ_xmssLeafM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) :
    simulateQ answer
        (xmssLeafM core sk pk adrs t : OracleComp (publicHashSpec core) core.Y) =
      xmssLeaf (PublicHash.withPublicHash core answer) sk pk adrs t := by
  simp [xmssLeaf, PublicHash.impl_withPublicHash]

/-- Canonical deterministic-handler parity for XMSS leaves. -/
@[simp]
theorem simulateQ_xmssLeafM (prims : Primitives p)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    simulateQ (PublicHash.impl prims)
        (xmssLeafM prims.core sk pk adrs t :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      xmssLeaf prims sk pk adrs t := rfl

/-- A fixed deterministic answer table turns an explicit XMSS internal-node query into the pure
node hash for the induced primitive bundle. -/
@[simp]
theorem simulateQ_xmssNodeHashM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (pk : core.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : core.Y) :
    simulateQ answer
        (xmssNodeHashM core pk adrs z t l r :
          OracleComp (publicHashSpec core) core.Y) =
      xmssNodeHash (PublicHash.withPublicHash core answer) pk adrs z t l r := by
  simp [xmssNodeHash, PublicHash.impl_withPublicHash]

/-- Canonical deterministic-handler parity for XMSS internal nodes. -/
@[simp]
theorem simulateQ_xmssNodeHashM (prims : Primitives p) (pk : prims.PkSeed)
    (adrs : Adrs) (z t : ℕ) (l r : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (xmssNodeHashM prims.core pk adrs z t l r :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      xmssNodeHash prims pk adrs z t l r := rfl

/-- A fixed deterministic answer table turns explicit XMSS subtree computation into the pure
subtree algorithm for the induced primitive bundle. -/
@[simp]
theorem simulateQ_xmssNodeM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) :
    simulateQ answer
        (xmssNodeM core sk pk adrs z t : OracleComp (publicHashSpec core) core.Y) =
      xmssNode (PublicHash.withPublicHash core answer) sk pk adrs z t := by
  simp [xmssNode, PublicHash.impl_withPublicHash]

/-- Canonical deterministic-handler parity for XMSS subtree computation. -/
@[simp]
theorem simulateQ_xmssNodeM (prims : Primitives p)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (z t : ℕ) :
    simulateQ (PublicHash.impl prims)
        (xmssNodeM prims.core sk pk adrs z t :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      xmssNode prims sk pk adrs z t := rfl

/-- A fixed deterministic answer table turns explicit XMSS root computation into the pure root
for the induced primitive bundle. -/
@[simp]
theorem simulateQ_xmssRootM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (xmssRootM core sk pk adrs : OracleComp (publicHashSpec core) core.Y) =
      xmssRoot (PublicHash.withPublicHash core answer) sk pk adrs := by
  simp [xmssRoot, PublicHash.impl_withPublicHash]

/-- Canonical deterministic-handler parity for XMSS roots. -/
@[simp]
theorem simulateQ_xmssRootM (prims : Primitives p)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (xmssRootM prims.core sk pk adrs :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      xmssRoot prims sk pk adrs := rfl

/-- A fixed deterministic answer table turns explicit XMSS signing into pure signing for the
induced primitive bundle. The same answer table interprets the WOTS+ signature and auth path. -/
@[simp]
theorem simulateQ_xmssSignM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    simulateQ answer
        (xmssSignM core msg sk pk adrs idx :
          OracleComp (publicHashSpec core) (XmssSig p core)) =
      xmssSign (PublicHash.withPublicHash core answer) msg sk pk adrs idx := by
  simp [xmssSign, PublicHash.impl_withPublicHash]

/-- Canonical deterministic-handler parity for XMSS signing. -/
@[simp]
theorem simulateQ_xmssSignM (prims : Primitives p)
    (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) (idx : ℕ) :
    simulateQ (PublicHash.impl prims)
        (xmssSignM prims.core msg sk pk adrs idx :
          OracleComp (publicHashSpec prims.core) (XmssSig p prims.core)) =
      xmssSign prims msg sk pk adrs idx := rfl

/-- A fixed deterministic answer table turns explicit XMSS root recovery into pure recovery for
the induced primitive bundle. -/
@[simp]
theorem simulateQ_xmssPkFromSigM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (idx : ℕ) (sig : XmssSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (xmssPkFromSigM core idx sig msg pk adrs :
          OracleComp (publicHashSpec core) core.Y) =
      xmssPkFromSig (PublicHash.withPublicHash core answer) idx sig msg pk adrs := by
  simp [xmssPkFromSig, PublicHash.impl_withPublicHash]

/-- Canonical deterministic-handler parity for XMSS root recovery. -/
@[simp]
theorem simulateQ_xmssPkFromSigM (prims : Primitives p)
    (idx : ℕ) (sig : XmssSig p prims) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (xmssPkFromSigM prims.core idx sig msg pk adrs :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      xmssPkFromSig prims idx sig msg pk adrs := rfl

/-- **XMSS correctness** (FIPS 205, Algorithms 9–11): root recovery from an honest signature at
leaf `idx < 2^{h'}` reproduces the XMSS tree root. Composes WOTS+ correctness with the Merkle
auth-path consistency lemma. -/
theorem xmssPkFromSig_xmssSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp) :
    xmssPkFromSig prims idx (xmssSign prims msg sk pk adrs idx) msg pk adrs
      = xmssRoot prims sk pk adrs := by
  rw [xmssPkFromSig_eq_climb, xmssSign_eq_pair, xmssRoot_eq_node,
    xmssNode_eq_merkleRoot]
  dsimp only
  rw [wotsPkFromSig_wotsSign]
  have key := PerfectMerkleTree.climb_authPath (xmssLeaf prims sk pk adrs)
    (xmssNodeHash prims pk adrs) idx p.hp
  rw [Nat.div_eq_of_lt hidx] at key
  simpa using key

/-- Functional XMSS completeness for one fixed total public-hash answer function shared by
signing, recovery, and root computation. This is a deterministic interpretation theorem; it does
not claim completeness for independently sampled free-oracle calls or install a lazy cache. -/
theorem simulateQ_xmssPkFromSigM_xmssSignM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp) :
    simulateQ answer (do
      let sig ← xmssSignM core msg sk pk adrs idx
      xmssPkFromSigM core idx sig msg pk adrs) =
    simulateQ answer (xmssRootM core sk pk adrs) := by
  simp only [simulateQ_bind, simulateQ_xmssSignM_withPublicHash,
    simulateQ_xmssPkFromSigM_withPublicHash, simulateQ_xmssRootM_withPublicHash]
  exact xmssPkFromSig_xmssSign (PublicHash.withPublicHash core answer)
    msg sk pk adrs idx hidx

/-- **XMSS binding.** A signature at leaf `idx < 2^{h'}` with a well-formed authentication path
whose recovered WOTS+ public key differs from the honest leaf, yet which recovers the honest XMSS
root, exhibits a collision of `H` at the `TREE` address of the ancestor of leaf `idx` at some
height `0 < h ≤ h'` — node `(h, idx / 2 ^ h)`: the honestly computed child pair at that node and
a distinct pair hash to the same value. The first endpoint is fixed by the honest tree and
determined by `(idx, h)` (a valid target for a multi-target target-collision reduction). -/
theorem xmssPkFromSig_binding (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idx : ℕ) (hidx : idx < 2 ^ p.hp)
    (sig : XmssSig p prims)
    (hroot : xmssPkFromSig prims idx sig msg pk adrs = xmssRoot prims sk pk adrs)
    (hne : xmssLeaf prims sk pk adrs idx
      ≠ wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx)) :
    ∃ (h : ℕ) (c : prims.Y × prims.Y), 0 < h ∧ h ≤ p.hp ∧
      (xmssNode prims sk pk adrs (h - 1) (2 * (idx / 2 ^ h)),
          xmssNode prims sk pk adrs (h - 1) (2 * (idx / 2 ^ h) + 1))
        ≠ c ∧
      prims.H pk (xmssNodeAdrs adrs h (idx / 2 ^ h))
          (xmssNode prims sk pk adrs (h - 1) (2 * (idx / 2 ^ h)))
          (xmssNode prims sk pk adrs (h - 1) (2 * (idx / 2 ^ h) + 1))
        = prims.H pk (xmssNodeAdrs adrs h (idx / 2 ^ h)) c.1 c.2 := by
  have hroot' : PerfectMerkleTree.climb (xmssNodeHash prims pk adrs) idx
      (wotsPkFromSig prims sig.wots msg pk (wotsLeafAdrs adrs idx)) sig.auth.toList
      = PerfectMerkleTree.merkleRoot (xmssLeaf prims sk pk adrs) (xmssNodeHash prims pk adrs)
          p.hp (idx / 2 ^ p.hp) := by
    rw [Nat.div_eq_of_lt hidx]
    simpa only [xmssPkFromSig_eq_climb, xmssRoot_eq_node, xmssNode_eq_merkleRoot] using hroot
  simpa only [xmssNode_eq_merkleRoot, xmssNodeHash_eq_h] using
    (PerfectMerkleTree.climb_binding (xmssLeaf prims sk pk adrs)
      (xmssNodeHash prims pk adrs) p.hp idx _ sig.auth.toList (by simp) hroot' hne)

end SLHDSA
