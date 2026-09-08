/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Xmss
public import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.Monadic
import VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed.QueryBound

/-!
# FORS (FIPS 205 §8)

The few-time forest signature: `k` Merkle trees of height `a`, with leaves `F(secret)` and the
`k` roots compressed by `T_k`. The canonical `*M` programs depend only on `CorePrimitives` and
issue every public hash through `HasQuery`; the pure API is their literal deterministic
`simulateQ` interpretation. Each tree is a `PerfectMerkleTree`
(`VCVio.CryptoFoundations.MerkleTree.Addressed.NatIndexed`) over global leaf indices. Provides
`forsSkGenCore`/`forsLeaf`/`forsRoot` (Algorithms 14–15), `forsSign` (Algorithm 16), `forsPkFromSig`
(Algorithm 17), and the correctness lemma `forsPkFromSig_forsSign`: recovery from an honest FORS
signature reproduces the FORS public key.

Because the FORS public key compresses the *whole-tree* roots (which are message-independent),
`forsPkFromSig (forsSign md) md = forsPkGen` holds for every digest `md`.

## References

- NIST FIPS 205, §8 (Algorithms 14–17)
-/

@[expose] public section


namespace SLHDSA

open OracleComp

variable {p : Params}

/-! ### FORS leaf indices -/

/-- The selected leaf index in FORS tree `i`: the `i`-th base-`2^a` digit of the digest. -/
def forsIdx (p : Params) (md : List Byte) (i : ℕ) : ℕ := (base2b md p.a p.k).getD i 0

theorem forsIdx_lt (p : Params) (md : List Byte) (i : ℕ) : forsIdx p md i < 2 ^ p.a := by
  unfold forsIdx
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i (base2b md p.a p.k).length with h | h
  · rw [List.getElem?_eq_getElem h]
    simpa using base2b_lt md p.a p.k _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none h]
    simp only [Option.getD_none]
    positivity

/-! ### FORS addresses, secret values, leaves, and tree roots -/

/-- Address for the FORS secret value at global leaf index `t` (type `FORS_PRF`). -/
def forsSkAdrs (adrs : Adrs) (t : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .forsPrf).setKeyPairAddress adrs.getKeyPairAddress).setTreeIndex t

/-- The FORS secret value at global leaf index `t` (FIPS 205 Algorithm 14), over the
implementation-independent context. -/
def forsSkGenCore (core : CorePrimitives p) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (t : ℕ) : core.Y :=
  core.PRF pk sk (forsSkAdrs adrs t)

/-- Address for the FORS-tree node at `(height z, global index t)` (type `FORS_TREE`). -/
def forsNodeAdrs (adrs : Adrs) (z t : ℕ) : Adrs :=
  let base := (adrs.setTypeAndClear .forsTree).setKeyPairAddress adrs.getKeyPairAddress
  (base.setTreeHeight z).setTreeIndex t

/-- Low-level callback-parametric FORS leaf computation. -/
def forsLeafWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (t : ℕ) : m core.Y :=
  hash (forsNodeAdrs adrs 0 t) (forsSkGenCore core sk pk adrs t)

/-- Low-level addressed internal-node callback. -/
def forsNodeHashWith {Y : Type} {m : Type → Type*}
    (nodeHash : Adrs → Y → Y → m Y) (adrs : Adrs)
    (z t : ℕ) (l r : Y) : m Y :=
  nodeHash (forsNodeAdrs adrs z t) l r

/-- Low-level callback-parametric root computation for FORS tree `i`. -/
def forsRootWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (i : ℕ) : m core.Y :=
  PerfectMerkleTree.merkleRootM (forsLeafWith core hash sk pk adrs)
    (forsNodeHashWith nodeHash adrs) p.a i

/-- Address compressing the `k` FORS roots into the FORS public key (type `FORS_ROOTS`). -/
def forsPkAdrs (adrs : Adrs) : Adrs :=
  (adrs.setTypeAndClear .forsRoots).setKeyPairAddress adrs.getKeyPairAddress

/-- One intrinsically shaped FORS tree signature: a revealed secret value and exactly `a`
authentication nodes. -/
structure ForsTreeSigCore (p : Params) (core : CorePrimitives p) where
  /-- Secret value selected by the message digest. -/
  sk : core.Y
  /-- The `a` sibling nodes, from the leaf level upward. -/
  auth : Vector core.Y p.a

/-- A FORS signature contains exactly one intrinsically shaped tree signature for each of the
`k` trees. -/
abbrev ForsSigCore (p : Params) (core : CorePrimitives p) :=
  Vector (ForsTreeSigCore p core) p.k

/-- Low-level callback-parametric FORS public-key generation. Roots are computed in increasing
tree order and compressed only after every root is available. -/
def forsPkGenWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) : m core.Y := do
  let roots ← Vector.ofFnM fun i : Fin p.k =>
    forsRootWith core hash nodeHash sk pk adrs i.val
  compress (forsPkAdrs adrs) roots.toList

/-- Low-level callback-parametric FORS signing. `intrinsicAuthPathM` evaluates only sibling
subtrees, so the selected leaf is revealed but never hashed by signing. Trees are processed in
increasing order. -/
def forsSignWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (md : List Byte) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) : m (ForsSigCore p core) :=
  Vector.ofFnM fun i : Fin p.k => do
    let idx := i.val * 2 ^ p.a + forsIdx p md i.val
    let path ← PerfectMerkleTree.intrinsicAuthPathM (forsLeafWith core hash sk pk adrs)
      (forsNodeHashWith nodeHash adrs) idx p.a
    return ⟨forsSkGenCore core sk pk adrs idx, path⟩

/-- Low-level callback-parametric FORS recovery. Each tree first hashes the revealed secret,
then climbs its authentication path; recovered roots are compressed in increasing tree order. -/
def forsPkFromSigWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (sig : ForsSigCore p core) (md : List Byte) (adrs : Adrs) : m core.Y := do
  let roots ← Vector.ofFnM fun i : Fin p.k => do
    let idx := i.val * 2 ^ p.a + forsIdx p md i.val
    let leaf ← hash (forsNodeAdrs adrs 0 idx) (sig[i.val]).sk
    PerfectMerkleTree.climbM (forsNodeHashWith nodeHash adrs) idx leaf (sig[i.val]).auth.toList
  compress (forsPkAdrs adrs) roots.toList

/-! ### Canonical oracle programs -/

/-- Canonical explicit-query FORS leaf computation. -/
def forsLeafM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (t : ℕ) : m core.Y :=
  forsLeafWith core (PublicHash.f core pk) sk pk adrs t

/-- Canonical explicit-query FORS internal-node computation. -/
def forsNodeHashM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] (pk : core.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : core.Y) : m core.Y :=
  forsNodeHashWith (PublicHash.h core pk) adrs z t l r

/-- Canonical explicit-query computation of one FORS tree root. -/
def forsRootM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (i : ℕ) : m core.Y :=
  forsRootWith core (PublicHash.f core pk) (PublicHash.h core pk) sk pk adrs i

/-- Canonical explicit-query FORS public-key generation. -/
def forsPkGenM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) : m core.Y :=
  forsPkGenWith core (PublicHash.f core pk) (PublicHash.h core pk)
    (PublicHash.tl core pk) sk pk adrs

/-- Canonical explicit-query FORS signing. -/
def forsSignM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] (md : List Byte) (sk : core.SkSeed)
    (pk : core.PkSeed) (adrs : Adrs) : m (ForsSigCore p core) :=
  forsSignWith core (PublicHash.f core pk) (PublicHash.h core pk) md sk pk adrs

/-- Canonical explicit-query FORS public-key recovery. -/
def forsPkFromSigM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] (sig : ForsSigCore p core) (md : List Byte)
    (pk : core.PkSeed) (adrs : Adrs) : m core.Y :=
  forsPkFromSigWith core (PublicHash.f core pk) (PublicHash.h core pk)
    (PublicHash.tl core pk) sig md adrs

/-! ### Pure deterministic interpretations -/

/-- Pure FORS leaf computation, defined as the deterministic interpretation of `forsLeafM`. -/
def forsLeaf (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (t : ℕ) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (forsLeafM prims.core sk pk adrs t : OracleComp (publicHashSpec prims.core) prims.Y)

/-- Pure FORS internal-node computation, defined as the interpretation of `forsNodeHashM`. -/
def forsNodeHash (prims : Primitives p) (pk : prims.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : prims.Y) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (forsNodeHashM prims.core pk adrs z t l r :
      OracleComp (publicHashSpec prims.core) prims.Y)

/-- Pure FORS tree-root computation, defined as the interpretation of `forsRootM`. -/
def forsRoot (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs)
    (i : ℕ) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (forsRootM prims.core sk pk adrs i : OracleComp (publicHashSpec prims.core) prims.Y)

/-- Pure FORS public-key generation, defined as the interpretation of `forsPkGenM`. -/
def forsPkGen (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  simulateQ (PublicHash.impl prims)
    (forsPkGenM prims.core sk pk adrs : OracleComp (publicHashSpec prims.core) prims.Y)

/-- Pure FORS signing, defined as the deterministic interpretation of `forsSignM`. -/
def forsSign (prims : Primitives p) (md : List Byte) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : ForsSigCore p prims.core :=
  simulateQ (PublicHash.impl prims)
    (forsSignM prims.core md sk pk adrs :
      OracleComp (publicHashSpec prims.core) (ForsSigCore p prims.core))

/-- Pure FORS public-key recovery, defined as the interpretation of `forsPkFromSigM`. -/
def forsPkFromSig (prims : Primitives p) (sig : ForsSigCore p prims.core) (md : List Byte)
    (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (forsPkFromSigM prims.core sig md pk adrs :
      OracleComp (publicHashSpec prims.core) prims.Y)

/-! ### Naturality -/

private theorem monadHom_ofFnM {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) {α : Type} {k : ℕ}
    (fm : Fin k → m α) (fn : Fin k → n α) (h : ∀ i, F (fm i) = fn i) :
    F (Vector.ofFnM fm) = Vector.ofFnM fn := by
  induction k with
  | zero => simp [F.mmap_pure]
  | succ k ih =>
      rw [Vector.ofFnM_succ, Vector.ofFnM_succ, F.mmap_bind]
      rw [ih (fun i => fm i.castSucc) (fun i => fn i.castSucc) (fun i => h i.castSucc)]
      congr 1
      funext xs
      rw [F.mmap_bind, h (Fin.last k)]
      simp [F.mmap_pure]

/-- A monad morphism commutes with FORS leaf production when it commutes with the leaf-hash
callback. -/
theorem forsLeafWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) :
    F (forsLeafWith core hashm sk pk adrs t) = forsLeafWith core hashn sk pk adrs t := by
  exact hhash _ _

/-- A monad morphism commutes with addressed FORS node hashing when it commutes with the node
callback. -/
theorem forsNodeHashWith_natural {Y : Type} {m n : Type → Type*}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n] (F : m →ᵐ n)
    (hashm : Adrs → Y → Y → m Y) (hashn : Adrs → Y → Y → n Y)
    (hhash : ∀ a l r, F (hashm a l r) = hashn a l r)
    (adrs : Adrs) (z t : ℕ) (l r : Y) :
    F (forsNodeHashWith hashm adrs z t l r) = forsNodeHashWith hashn adrs z t l r := by
  exact hhash _ _ _

/-- A monad morphism commutes with one FORS-tree root computation when it commutes with the leaf
and node callbacks. -/
theorem forsRootWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (i : ℕ) :
    F (forsRootWith core hashm nodeHashm sk pk adrs i) =
      forsRootWith core hashn nodeHashn sk pk adrs i := by
  exact PerfectMerkleTree.merkleRootM_natural F _ _ _ _
    (fun t => forsLeafWith_natural F core hashm hashn hhash sk pk adrs t)
    (fun z t l r => forsNodeHashWith_natural F nodeHashm nodeHashn hnode adrs z t l r) _ _

/-- A monad morphism commutes with FORS public-key generation when it commutes with all public
hash callbacks. -/
theorem forsPkGenWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y)
    (compressn : Adrs → List core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    F (forsPkGenWith core hashm nodeHashm compressm sk pk adrs) =
      forsPkGenWith core hashn nodeHashn compressn sk pk adrs := by
  simp [forsPkGenWith, F.mmap_bind,
    monadHom_ofFnM F _ _ (fun i => forsRootWith_natural F core hashm hashn nodeHashm nodeHashn
      hhash hnode sk pk adrs i.val), hcompress]

/-- A monad morphism commutes with FORS signing when it commutes with the leaf and node
callbacks. -/
theorem forsSignWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (md : List Byte) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    F (forsSignWith core hashm nodeHashm md sk pk adrs) =
      forsSignWith core hashn nodeHashn md sk pk adrs := by
  apply monadHom_ofFnM F
  intro i
  simp [PerfectMerkleTree.intrinsicAuthPathM_natural F _ _ _ _
    (fun t => forsLeafWith_natural F core hashm hashn hhash sk pk adrs t)
    (fun z t l r => forsNodeHashWith_natural F nodeHashm nodeHashn hnode adrs z t l r)]

/-- A monad morphism commutes with FORS recovery when it commutes with all public-hash
callbacks. -/
theorem forsPkFromSigWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (nodeHashm : Adrs → core.Y → core.Y → m core.Y)
    (nodeHashn : Adrs → core.Y → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y)
    (compressn : Adrs → List core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hnode : ∀ a l r, F (nodeHashm a l r) = nodeHashn a l r)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (sig : ForsSigCore p core) (md : List Byte) (adrs : Adrs) :
    F (forsPkFromSigWith core hashm nodeHashm compressm sig md adrs) =
      forsPkFromSigWith core hashn nodeHashn compressn sig md adrs := by
  have hroots : F (Vector.ofFnM fun i : Fin p.k => do
      let idx := i.val * 2 ^ p.a + forsIdx p md i.val
      let leaf ← hashm (forsNodeAdrs adrs 0 idx) (sig[i.val]).sk
      PerfectMerkleTree.climbM (forsNodeHashWith nodeHashm adrs) idx leaf
        (sig[i.val]).auth.toList) =
      (Vector.ofFnM fun i : Fin p.k => do
        let idx := i.val * 2 ^ p.a + forsIdx p md i.val
        let leaf ← hashn (forsNodeAdrs adrs 0 idx) (sig[i.val]).sk
        PerfectMerkleTree.climbM (forsNodeHashWith nodeHashn adrs) idx leaf
          (sig[i.val]).auth.toList) := by
    apply monadHom_ofFnM F
    intro i
    rw [F.mmap_bind, hhash]
    congr 1
    funext leaf
    exact PerfectMerkleTree.climbM_natural F _ _
      (fun z t l r => forsNodeHashWith_natural F nodeHashm nodeHashn hnode adrs z t l r) _ _ _
  simp [forsPkFromSigWith, F.mmap_bind, hroots, hcompress]

private theorem queryHom_f (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n) (pk : core.PkSeed) :
    ∀ a y, F.toMonadHom (PublicHash.f core pk a y) = PublicHash.f core pk a y := by
  intro a y
  change F.toMonadHom
      (query (spec := publicHashSpec core)
        (PublicHashQuery.thash pk (core.adrsToKey a) [y])) =
    query (spec := publicHashSpec core)
      (PublicHashQuery.thash pk (core.adrsToKey a) [y])
  exact HasQuery.map_query F _

private theorem queryHom_h (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n) (pk : core.PkSeed) :
    ∀ a l r, F.toMonadHom (PublicHash.h core pk a l r) = PublicHash.h core pk a l r := by
  intro a l r
  change F.toMonadHom
      (query (spec := publicHashSpec core)
        (PublicHashQuery.thash pk (core.adrsToKey a) [l, r])) =
    query (spec := publicHashSpec core)
      (PublicHashQuery.thash pk (core.adrsToKey a) [l, r])
  exact HasQuery.map_query F _

private theorem queryHom_tl (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [Monad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n) (pk : core.PkSeed) :
    ∀ a ys, F.toMonadHom (PublicHash.tl core pk a ys) = PublicHash.tl core pk a ys := by
  intro a ys
  change F.toMonadHom
      (query (spec := publicHashSpec core)
        (PublicHashQuery.thash pk (core.adrsToKey a) ys)) =
    query (spec := publicHashSpec core)
      (PublicHashQuery.thash pk (core.adrsToKey a) ys)
  exact HasQuery.map_query F _

/-- Query-preserving monad morphisms commute with canonical FORS leaf computation. -/
theorem forsLeafM_natural (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) :
    F.toMonadHom (forsLeafM core sk pk adrs t) = forsLeafM core sk pk adrs t :=
  forsLeafWith_natural F.toMonadHom core _ _ (queryHom_f core F pk) sk pk adrs t

/-- Query-preserving monad morphisms commute with canonical FORS internal-node computation. -/
theorem forsNodeHashM_natural (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) (l r : core.Y) :
    F.toMonadHom (forsNodeHashM core pk adrs z t l r) =
      forsNodeHashM core pk adrs z t l r :=
  forsNodeHashWith_natural F.toMonadHom _ _ (queryHom_h core F pk) adrs z t l r

/-- Query-preserving monad morphisms commute with one canonical FORS root computation. -/
theorem forsRootM_natural (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (i : ℕ) :
    F.toMonadHom (forsRootM core sk pk adrs i) = forsRootM core sk pk adrs i :=
  forsRootWith_natural F.toMonadHom core _ _ _ _
    (queryHom_f core F pk) (queryHom_h core F pk) sk pk adrs i

/-- Query-preserving monad morphisms commute with canonical FORS public-key generation. -/
theorem forsPkGenM_natural (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    F.toMonadHom (forsPkGenM core sk pk adrs) = forsPkGenM core sk pk adrs :=
  forsPkGenWith_natural F.toMonadHom core _ _ _ _ _ _
    (queryHom_f core F pk) (queryHom_h core F pk) (queryHom_tl core F pk) sk pk adrs

/-- Query-preserving monad morphisms commute with canonical FORS signing. -/
theorem forsSignM_natural (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (md : List Byte) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    F.toMonadHom (forsSignM core md sk pk adrs) = forsSignM core md sk pk adrs :=
  forsSignWith_natural F.toMonadHom core _ _ _ _
    (queryHom_f core F pk) (queryHom_h core F pk) md sk pk adrs

/-- Query-preserving monad morphisms commute with canonical FORS recovery. -/
theorem forsPkFromSigM_natural (core : CorePrimitives p) {m n : Type → Type*}
    [Monad m] [LawfulMonad m] [Monad n] [LawfulMonad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sig : ForsSigCore p core) (md : List Byte) (pk : core.PkSeed) (adrs : Adrs) :
    F.toMonadHom (forsPkFromSigM core sig md pk adrs) = forsPkFromSigM core sig md pk adrs :=
  forsPkFromSigWith_natural F.toMonadHom core _ _ _ _ _ _
    (queryHom_f core F pk) (queryHom_h core F pk) (queryHom_tl core F pk) sig md adrs

/-! ### Structural query bounds -/

private theorem isTotalQueryBound_ofFnM {ι α : Type} {spec : OracleSpec ι} {k : ℕ}
    (g : Fin k → OracleComp spec α) (budget : Fin k → ℕ)
    (h : ∀ i, IsTotalQueryBound (g i) (budget i)) :
    IsTotalQueryBound (Vector.ofFnM g) (∑ i, budget i) := by
  induction k with
  | zero =>
      rw [Vector.ofFnM_zero]
      trivial
  | succ k ih =>
      rw [Vector.ofFnM_succ, Fin.sum_univ_castSucc]
      apply isTotalQueryBound_bind
        (ih (fun i => g i.castSucc) (fun i => budget i.castSucc) (fun i => h i.castSucc))
      intro xs
      simpa using isTotalQueryBound_bind (n₂ := 0) (h (Fin.last k))
        (fun a => show IsTotalQueryBound (pure (xs.push a) : OracleComp spec _) 0 from trivial)

private theorem publicHash_f_isTotalQueryBound_one (core : CorePrimitives p)
    (pk : core.PkSeed) (adrs : Adrs) (x : core.Y) :
    IsTotalQueryBound
      (PublicHash.f core pk adrs x : OracleComp (publicHashSpec core) core.Y) 1 := by
  simp [PublicHash.f, IsTotalQueryBound]

private theorem publicHash_h_isTotalQueryBound_one (core : CorePrimitives p)
    (pk : core.PkSeed) (adrs : Adrs) (l r : core.Y) :
    IsTotalQueryBound
      (PublicHash.h core pk adrs l r : OracleComp (publicHashSpec core) core.Y) 1 := by
  simp [PublicHash.h, IsTotalQueryBound]

private theorem publicHash_tl_isTotalQueryBound_one (core : CorePrimitives p)
    (pk : core.PkSeed) (adrs : Adrs) (xs : List core.Y) :
    IsTotalQueryBound
      (PublicHash.tl core pk adrs xs : OracleComp (publicHashSpec core) core.Y) 1 := by
  simp [PublicHash.tl, IsTotalQueryBound]

/-- A FORS leaf is one explicit `F` query. -/
theorem forsLeafM_isTotalQueryBound (core : CorePrimitives p)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (t : ℕ) :
    IsTotalQueryBound
      (forsLeafM core sk pk adrs t : OracleComp (publicHashSpec core) core.Y) 1 :=
  publicHash_f_isTotalQueryBound_one core pk _ _

/-- A FORS internal node is one explicit `H` query. -/
theorem forsNodeHashM_isTotalQueryBound (core : CorePrimitives p)
    (pk : core.PkSeed) (adrs : Adrs) (z t : ℕ) (l r : core.Y) :
    IsTotalQueryBound
      (forsNodeHashM core pk adrs z t l r : OracleComp (publicHashSpec core) core.Y) 1 :=
  publicHash_h_isTotalQueryBound_one core pk _ _ _

/-- A height-`a` FORS root evaluates all `2^a` leaves and all `2^a - 1` internal nodes. -/
theorem forsRootM_isTotalQueryBound (core : CorePrimitives p)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (i : ℕ) :
    IsTotalQueryBound
      (forsRootM core sk pk adrs i : OracleComp (publicHashSpec core) core.Y)
      (2 ^ p.a + (2 ^ p.a - 1)) := by
  simpa [forsRootM, forsRootWith] using
    (PerfectMerkleTree.isTotalQueryBound_merkleRootM
      (forsLeafWith core (PublicHash.f core pk) sk pk adrs)
      (forsNodeHashWith (PublicHash.h core pk) adrs) 1 1 p.a i
      (fun t => publicHash_f_isTotalQueryBound_one core pk _ _)
      (fun z t l r => publicHash_h_isTotalQueryBound_one core pk _ l r))

/-- FORS public-key generation computes `k` complete roots, in order, and then makes one `T_k`
query. -/
theorem forsPkGenM_isTotalQueryBound (core : CorePrimitives p)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (forsPkGenM core sk pk adrs : OracleComp (publicHashSpec core) core.Y)
      (p.k * (2 ^ p.a + (2 ^ p.a - 1)) + 1) := by
  have hroots := isTotalQueryBound_ofFnM
    (fun i : Fin p.k =>
      (forsRootM core sk pk adrs i.val : OracleComp (publicHashSpec core) core.Y))
    (fun _ => 2 ^ p.a + (2 ^ p.a - 1))
    (fun i => forsRootM_isTotalQueryBound core sk pk adrs i.val)
  simpa [forsPkGenM, forsPkGenWith, forsRootM] using
    isTotalQueryBound_bind hroots fun roots =>
      publicHash_tl_isTotalQueryBound_one core pk (forsPkAdrs adrs) roots.toList

/-- FORS signing computes only sibling subtrees. Per tree this is exactly `2^a - 1` leaf
callbacks and `2^a - a - 1` internal-node callbacks; the selected leaf is not hashed. -/
theorem forsSignM_isTotalQueryBound (core : CorePrimitives p) (md : List Byte)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (forsSignM core md sk pk adrs :
        OracleComp (publicHashSpec core) (ForsSigCore p core))
      (p.k * ((2 ^ p.a - 1) + (2 ^ p.a - p.a - 1))) := by
  have hpaths := isTotalQueryBound_ofFnM
    (fun i : Fin p.k =>
      (do
        let idx := i.val * 2 ^ p.a + forsIdx p md i.val
        let path ← PerfectMerkleTree.intrinsicAuthPathM
          (forsLeafWith core (PublicHash.f core pk) sk pk adrs)
          (forsNodeHashWith (PublicHash.h core pk) adrs) idx p.a
        return ForsTreeSigCore.mk (forsSkGenCore core sk pk adrs idx) path :
          OracleComp (publicHashSpec core) (ForsTreeSigCore p core)))
    (fun _ => (2 ^ p.a - 1) + (2 ^ p.a - p.a - 1))
    (fun i => by
      have hpath : IsTotalQueryBound
          (PerfectMerkleTree.intrinsicAuthPathM
            (forsLeafWith core (PublicHash.f core pk) sk pk adrs)
            (forsNodeHashWith (PublicHash.h core pk) adrs)
            (i.val * 2 ^ p.a + forsIdx p md i.val) p.a :
            OracleComp (publicHashSpec core) (Vector core.Y p.a))
          ((2 ^ p.a - 1) + (2 ^ p.a - p.a - 1)) := by
        simpa using PerfectMerkleTree.isTotalQueryBound_intrinsicAuthPathM
          (forsLeafWith core (PublicHash.f core pk) sk pk adrs)
          (forsNodeHashWith (PublicHash.h core pk) adrs) 1 1
          (i.val * 2 ^ p.a + forsIdx p md i.val) p.a
          (fun t => publicHash_f_isTotalQueryBound_one core pk _ _)
          (fun z t l r => publicHash_h_isTotalQueryBound_one core pk _ l r)
      exact isTotalQueryBound_bind (n₂ := 0) hpath
        (fun path => show IsTotalQueryBound
          (pure (ForsTreeSigCore.mk (forsSkGenCore core sk pk adrs
            (i.val * 2 ^ p.a + forsIdx p md i.val)) path) :
            OracleComp (publicHashSpec core) _) 0 from trivial))
  simpa [forsSignM, forsSignWith] using hpaths

/-- Recovery from an arbitrary signature performs one `F` query and one `H` query per supplied
authentication-path entry in each tree, then one final `T_k` query. -/
theorem forsPkFromSigM_isTotalQueryBound (core : CorePrimitives p)
    (sig : ForsSigCore p core) (md : List Byte) (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (forsPkFromSigM core sig md pk adrs : OracleComp (publicHashSpec core) core.Y)
      (p.k * (p.a + 1) + 1) := by
  change IsTotalQueryBound (do
    let roots ← Vector.ofFnM fun i : Fin p.k => do
      let idx := i.val * 2 ^ p.a + forsIdx p md i.val
      let leaf ← PublicHash.f core pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).sk
      PerfectMerkleTree.climbM (forsNodeHashWith (PublicHash.h core pk) adrs)
        idx leaf (sig[i.val]).auth.toList
    PublicHash.tl core pk (forsPkAdrs adrs) roots.toList) _
  have hroots := isTotalQueryBound_ofFnM
    (fun i : Fin p.k =>
      (do
        let idx := i.val * 2 ^ p.a + forsIdx p md i.val
        let leaf ← PublicHash.f core pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).sk
        PerfectMerkleTree.climbM (forsNodeHashWith (PublicHash.h core pk) adrs)
          idx leaf (sig[i.val]).auth.toList : OracleComp (publicHashSpec core) core.Y))
    (fun _ => p.a + 1)
    (fun i => by
      let idx := i.val * 2 ^ p.a + forsIdx p md i.val
      have hbound := isTotalQueryBound_bind
        (publicHash_f_isTotalQueryBound_one core pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).sk)
        (fun leaf => by
          simpa using PerfectMerkleTree.isTotalQueryBound_climbM
            (forsNodeHashWith (PublicHash.h core pk) adrs) 1
            idx leaf (sig[i.val]).auth.toList
            (fun z t l r => publicHash_h_isTotalQueryBound_one core pk _ l r))
      simpa [idx, Nat.add_comm] using hbound)
  simpa using isTotalQueryBound_bind hroots fun roots =>
    publicHash_tl_isTotalQueryBound_one core pk (forsPkAdrs adrs) roots.toList

/-- Honest FORS signing followed by recovery stays within the full signing-and-recovery
schedule.  Signing computes only sibling subtrees; every generated authentication path has
exactly `a` entries, so recovery then performs one `F` and `a` `H` calls per tree followed by
one final `T_k` call.

This is a structural bound on calls in the free public-hash program.  Under a lazy cached random
oracle, repeated calls may hit the cache, so the theorem does not assert this many distinct cache
misses or fresh samples. -/
theorem forsSignM_then_forsPkFromSigM_isTotalQueryBound (core : CorePrimitives p)
    (md : List Byte) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound ((do
      let sig ← forsSignM core md sk pk adrs
      let forsPk ← forsPkFromSigM core sig md pk adrs
      return (sig, forsPk)) :
        OracleComp (publicHashSpec core) (ForsSigCore p core × core.Y))
      (p.k * ((2 ^ p.a - 1) + (2 ^ p.a - p.a - 1)) +
        (p.k * (p.a + 1) + 1)) := by
  exact isTotalQueryBound_bind
    (forsSignM_isTotalQueryBound core md sk pk adrs) fun sig =>
      isTotalQueryBound_bind (n₂ := 0)
        (forsPkFromSigM_isTotalQueryBound core sig md pk adrs)
        (fun forsPk => show IsTotalQueryBound
          (pure (sig, forsPk) :
            OracleComp (publicHashSpec core) (ForsSigCore p core × core.Y)) 0 from trivial)

/-! ### Pure API equations -/

private theorem simulateQ_ofFnM {ι α : Type} {spec : OracleSpec ι} {k : ℕ}
    (answer : QueryImpl spec Id) (g : Fin k → OracleComp spec α) :
    simulateQ answer (Vector.ofFnM g) = Vector.ofFn fun i => simulateQ answer (g i) := by
  calc
    simulateQ answer (Vector.ofFnM g) =
        Vector.ofFnM (fun i => simulateQ answer (g i)) :=
      monadHom_ofFnM (simulateQ' answer) g _ (fun _ => rfl)
    _ = Vector.ofFn fun i => simulateQ answer (g i) := Vector.idRun_ofFnM

@[simp] theorem forsLeaf_eq_f (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    forsLeaf prims sk pk adrs t =
      prims.F pk (forsNodeAdrs adrs 0 t) (forsSkGenCore prims.core sk pk adrs t) := by
  simp [forsLeaf, forsLeafM, forsLeafWith, PublicHash.f]
  rfl

@[simp] theorem forsNodeHash_eq_h (prims : Primitives p) (pk : prims.PkSeed)
    (adrs : Adrs) (z t : ℕ) (l r : prims.Y) :
    forsNodeHash prims pk adrs z t l r = prims.H pk (forsNodeAdrs adrs z t) l r := by
  simp [forsNodeHash, forsNodeHashM, forsNodeHashWith, PublicHash.h]
  rfl

@[simp] theorem forsRoot_eq_merkleRoot (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (i : ℕ) :
    forsRoot prims sk pk adrs i =
      PerfectMerkleTree.merkleRoot (forsLeaf prims sk pk adrs)
        (forsNodeHash prims pk adrs) p.a i := by
  unfold forsRoot forsRootM forsRootWith
  rw [PerfectMerkleTree.simulateQ_merkleRootM]
  rfl

@[simp] theorem forsPkGen_eq_tl (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    forsPkGen prims sk pk adrs = prims.Tl pk (forsPkAdrs adrs)
      (Vector.ofFn (fun i : Fin p.k => forsRoot prims sk pk adrs i.val)).toList := by
  simp only [forsPkGen, forsPkGenM, forsPkGenWith, simulateQ_bind, simulateQ_ofFnM,
    PublicHash.tl, simulateQ_HasQuery_query, PublicHash.impl]
  rfl

@[simp] theorem forsSign_eq_ofFn (prims : Primitives p) (md : List Byte)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    forsSign prims md sk pk adrs = Vector.ofFn fun i : Fin p.k =>
      let idx := i.val * 2 ^ p.a + forsIdx p md i.val
      ForsTreeSigCore.mk (forsSkGenCore prims.core sk pk adrs idx)
        (PerfectMerkleTree.intrinsicAuthPath (forsLeaf prims sk pk adrs)
          (forsNodeHash prims pk adrs) idx p.a) := by
  unfold forsSign forsSignM forsSignWith
  rw [simulateQ_ofFnM]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, simulateQ_bind, simulateQ_pure,
    PerfectMerkleTree.simulateQ_intrinsicAuthPathM]
  rfl

/-- Every authentication path produced by honest FORS signing has the FIPS-prescribed length
`a`. -/
@[simp] theorem forsSign_authPath_length (prims : Primitives p) (md : List Byte)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (i : Fin p.k) :
    ((forsSign prims md sk pk adrs)[i.val]).auth.toList.length = p.a := by
  simp

@[simp] theorem forsPkFromSig_eq_tl (prims : Primitives p) (sig : ForsSigCore p prims.core)
    (md : List Byte) (pk : prims.PkSeed) (adrs : Adrs) :
    forsPkFromSig prims sig md pk adrs = prims.Tl pk (forsPkAdrs adrs)
      (Vector.ofFn (fun i : Fin p.k =>
        let idx := i.val * 2 ^ p.a + forsIdx p md i.val
        PerfectMerkleTree.climb (forsNodeHash prims pk adrs) idx
          (prims.F pk (forsNodeAdrs adrs 0 idx) (sig[i.val]).sk)
          (sig[i.val]).auth.toList)).toList := by
  simp only [forsPkFromSig, forsPkFromSigM, forsPkFromSigWith, simulateQ_bind,
    simulateQ_ofFnM, PublicHash.tl, PublicHash.f, simulateQ_HasQuery_query,
    PublicHash.impl]
  apply congrArg (prims.Thash pk (prims.adrsToKey (forsPkAdrs adrs)))
  congr 1
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_ofFn, PerfectMerkleTree.simulateQ_climbM]
  rfl

/-! ### Deterministic interpretations -/

@[simp] theorem simulateQ_forsLeafM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (t : ℕ) :
    simulateQ answer
        (forsLeafM core sk pk adrs t : OracleComp (publicHashSpec core) core.Y) =
      forsLeaf (PublicHash.withPublicHash core answer) sk pk adrs t := by
  simp [forsLeaf, PublicHash.impl_withPublicHash]

@[simp] theorem simulateQ_forsLeafM (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (t : ℕ) :
    simulateQ (PublicHash.impl prims)
        (forsLeafM prims.core sk pk adrs t :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      forsLeaf prims sk pk adrs t := rfl

@[simp] theorem simulateQ_forsNodeHashM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (pk : core.PkSeed) (adrs : Adrs)
    (z t : ℕ) (l r : core.Y) :
    simulateQ answer
        (forsNodeHashM core pk adrs z t l r : OracleComp (publicHashSpec core) core.Y) =
      forsNodeHash (PublicHash.withPublicHash core answer) pk adrs z t l r := by
  simp [forsNodeHash, PublicHash.impl_withPublicHash]

@[simp] theorem simulateQ_forsNodeHashM (prims : Primitives p) (pk : prims.PkSeed)
    (adrs : Adrs) (z t : ℕ) (l r : prims.Y) :
    simulateQ (PublicHash.impl prims)
        (forsNodeHashM prims.core pk adrs z t l r :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      forsNodeHash prims pk adrs z t l r := rfl

@[simp] theorem simulateQ_forsRootM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (i : ℕ) :
    simulateQ answer
        (forsRootM core sk pk adrs i : OracleComp (publicHashSpec core) core.Y) =
      forsRoot (PublicHash.withPublicHash core answer) sk pk adrs i := by
  simp [forsRoot, PublicHash.impl_withPublicHash]

@[simp] theorem simulateQ_forsRootM (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (i : ℕ) :
    simulateQ (PublicHash.impl prims)
        (forsRootM prims.core sk pk adrs i :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      forsRoot prims sk pk adrs i := rfl

@[simp] theorem simulateQ_forsPkGenM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) :
    simulateQ answer
        (forsPkGenM core sk pk adrs : OracleComp (publicHashSpec core) core.Y) =
      forsPkGen (PublicHash.withPublicHash core answer) sk pk adrs := by
  simp [forsPkGen, PublicHash.impl_withPublicHash]

@[simp] theorem simulateQ_forsPkGenM (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (forsPkGenM prims.core sk pk adrs :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      forsPkGen prims sk pk adrs := rfl

@[simp] theorem simulateQ_forsSignM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (md : List Byte) (sk : core.SkSeed)
    (pk : core.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (forsSignM core md sk pk adrs :
          OracleComp (publicHashSpec core) (ForsSigCore p core)) =
      forsSign (PublicHash.withPublicHash core answer) md sk pk adrs := by
  simp [forsSign, PublicHash.impl_withPublicHash]

@[simp] theorem simulateQ_forsSignM (prims : Primitives p) (md : List Byte)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (forsSignM prims.core md sk pk adrs :
          OracleComp (publicHashSpec prims.core) (ForsSigCore p prims.core)) =
      forsSign prims md sk pk adrs := rfl

@[simp] theorem simulateQ_forsPkFromSigM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (sig : ForsSigCore p core)
    (md : List Byte) (pk : core.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (forsPkFromSigM core sig md pk adrs : OracleComp (publicHashSpec core) core.Y) =
      forsPkFromSig (PublicHash.withPublicHash core answer) sig md pk adrs := by
  simp [forsPkFromSig, PublicHash.impl_withPublicHash]

@[simp] theorem simulateQ_forsPkFromSigM (prims : Primitives p)
    (sig : ForsSigCore p prims.core)
    (md : List Byte) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (forsPkFromSigM prims.core sig md pk adrs :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      forsPkFromSig prims sig md pk adrs := rfl

/-! ### Correctness -/

/-- **FORS correctness** (FIPS 205, Algorithms 14–17): recovering the FORS public key from an
honest signature reproduces `forsPkGen`. Each tree's recovered root equals its true root by the
Merkle auth-path consistency lemma. -/
theorem forsPkFromSig_forsSign (prims : Primitives p) (md : List Byte) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    forsPkFromSig prims (forsSign prims md sk pk adrs) md pk adrs = forsPkGen prims sk pk adrs := by
  rw [forsPkFromSig_eq_tl, forsPkGen_eq_tl]
  apply congrArg (prims.Tl pk (forsPkAdrs adrs))
  congr 1
  apply Vector.ext
  intro i hi
  simp only [forsSign_eq_ofFn, Vector.getElem_ofFn]
  have ht : (i * 2 ^ p.a + forsIdx p md i) / 2 ^ p.a = i := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ p.a),
      Nat.div_eq_of_lt (forsIdx_lt p md i), Nat.zero_add]
  have key := PerfectMerkleTree.climb_authPath (forsLeaf prims sk pk adrs)
    (forsNodeHash prims pk adrs) (i * 2 ^ p.a + forsIdx p md i) p.a
  rw [ht] at key
  rw [PerfectMerkleTree.intrinsicAuthPath_toList]
  simpa only [forsLeaf_eq_f, forsRoot_eq_merkleRoot] using key

/-- Extensional FORS completeness for every fixed total public-hash answer table.

This is a stateless `QueryImpl ... Id` theorem. It deliberately fixes one answer function for
key generation, signing, and recovery; the lazy cached-random-oracle bridge belongs to the
security layer. -/
theorem simulateQ_forsPkFromSigM_forsSignM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (md : List Byte) (sk : core.SkSeed)
    (pk : core.PkSeed) (adrs : Adrs) :
    simulateQ answer (do
      let sig ← forsSignM core md sk pk adrs
      forsPkFromSigM core sig md pk adrs) =
    simulateQ answer (forsPkGenM core sk pk adrs) := by
  simp only [simulateQ_bind, simulateQ_forsSignM_withPublicHash,
    simulateQ_forsPkFromSigM_withPublicHash, simulateQ_forsPkGenM_withPublicHash]
  exact forsPkFromSig_forsSign (PublicHash.withPublicHash core answer) md sk pk adrs

end SLHDSA
