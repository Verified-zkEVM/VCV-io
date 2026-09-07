/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Oracle
public import HashSig.SLHDSA.WotsEncoding
public import VCVio.OracleComp.HasQuery.Morphism
public import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# WOTS+ (FIPS 205 §5)

The Winternitz one-time signature over the implementation-independent `CorePrimitives` context.
Each canonical `*M` algorithm issues public hashing through `HasQuery`; it cannot access a
concrete `Thash` or `Hmsg` implementation.  The pure algorithmic entry points are deterministic
interpretations of those canonical programs with `simulateQ (PublicHash.impl prims)`.

The lower-level `*With` combinators remain useful for naturality and composition proofs, but they
are implementation helpers rather than a second semantics.

The headline result is `wotsPkFromSig_wotsSign`: recovering the public key from an honest
signature reproduces `wotsPkGen`. Its only ingredient is the hash-chain composition law
`chain_compose`, proved by induction with no hash hypotheses — the deterministic core that
drives XMSS/hypertree correctness downstream.

## References

- NIST FIPS 205, §5 (Algorithms 5–8), §5.4 (the checksum, validated in `WotsChecksum`)
-/

@[expose] public section


namespace SLHDSA

open OracleComp
open WotsChecksum
open WotsEncoding

variable {p : Params}

/-- `0 < w = 2^lgw`. -/
theorem Params.w_pos (p : Params) : 0 < p.w := by
  unfold Params.w; positivity

/-! ### The hash chain (FIPS 205 Algorithm 5) -/

/-- Low-level callback-parametric implementation of the WOTS+ chain. -/
def chainWith {Y : Type} {m : Type → Type*} [Monad m]
    (hash : Adrs → Y → m Y) (adrs : Adrs) (x : Y) (i : ℕ) : ℕ → m Y
  | 0 => pure x
  | s + 1 => do
      let y ← chainWith hash adrs x i s
      hash (adrs.setHashAddress (i + s)) y

/-- Canonical explicit-public-hash WOTS+ chain program. -/
def chainM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] (pkSeed : core.PkSeed) (adrs : Adrs) (x : core.Y)
    (i s : ℕ) : m core.Y :=
  chainWith (PublicHash.f core pkSeed) adrs x i s

/-- `chain(X, i, s, PK.seed, ADRS)`: the deterministic interpretation of the canonical chain
program using a concrete primitive bundle. -/
def chain (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs) (x : prims.Y)
    (i s : ℕ) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (chainM prims.core pkSeed adrs x i s :
      OracleComp (publicHashSpec prims.core) prims.Y)

@[simp] theorem chain_zero (prims : Primitives p) (pkSeed : prims.PkSeed)
    (adrs : Adrs) (x : prims.Y) (i : ℕ) :
    chain prims pkSeed adrs x i 0 = x := rfl

@[simp] theorem chain_succ (prims : Primitives p) (pkSeed : prims.PkSeed)
    (adrs : Adrs) (x : prims.Y) (i s : ℕ) :
    chain prims pkSeed adrs x i (s + 1) =
      prims.F pkSeed (adrs.setHashAddress (i + s)) (chain prims pkSeed adrs x i s) := by
  simp only [chain, chainM, chainWith, simulateQ_bind, PublicHash.f,
    simulateQ_HasQuery_query, PublicHash.impl]
  rfl

/-- A monad morphism commutes with the callback-parametric WOTS+ chain when it commutes with the
hash callback. -/
theorem chainWith_natural {Y : Type} {m n : Type → Type*} [Monad m] [Monad n]
    (F : m →ᵐ n) (hashm : Adrs → Y → m Y) (hashn : Adrs → Y → n Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y) (adrs : Adrs) (x : Y) (i s : ℕ) :
    F (chainWith hashm adrs x i s) = chainWith hashn adrs x i s := by
  induction s with
  | zero => simp [chainWith, F.mmap_pure]
  | succ s ih => simp [chainWith, F.mmap_bind, ih, hhash]

/-- Query-preserving monad morphisms commute with the explicit-public-hash WOTS+ chain. -/
theorem chainM_natural (core : CorePrimitives p) {m n : Type → Type*} [Monad m] [Monad n]
    [HasQuery (publicHashSpec core) m] [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (pkSeed : core.PkSeed) (adrs : Adrs) (x : core.Y) (i s : ℕ) :
    F.toMonadHom (chainM core pkSeed adrs x i s) =
      chainM core pkSeed adrs x i s := by
  apply chainWith_natural F.toMonadHom
  intro a y
  change F.toMonadHom
      (query (spec := publicHashSpec core)
        (PublicHashQuery.thash pkSeed (core.adrsToKey a) [y])) =
    query (spec := publicHashSpec core)
      (PublicHashQuery.thash pkSeed (core.adrsToKey a) [y])
  exact HasQuery.map_query F _

/-- Hash-chain composition: chaining `a` steps then `b` more (from index `i + a`) equals
chaining `a + b` steps from `i`. The deterministic backbone of WOTS+ correctness. -/
theorem chain_compose (prims : Primitives p) (pkSeed : prims.PkSeed) (adrs : Adrs)
    (x : prims.Y) (i a b : ℕ) :
    chain prims pkSeed adrs (chain prims pkSeed adrs x i a) (i + a) b
      = chain prims pkSeed adrs x i (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
      rw [← Nat.add_assoc, chain_succ, chain_succ, ih, Nat.add_assoc]

/-! ### WOTS+ addresses -/

/-- Address for deriving the secret value of chain `i` (type `WOTS_PRF`, keypair preserved). -/
def wotsSkAdrs (adrs : Adrs) (i : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .wotsPrf).setKeyPairAddress adrs.getKeyPairAddress).setChainAddress i

/-- Base address for the `F`-steps of chain `i` (type `WOTS_HASH`, key-pair preserved,
chain address `i`). -/
def wotsChainAdrs (adrs : Adrs) (i : ℕ) : Adrs :=
  ((adrs.setTypeAndClear .wotsHash).setKeyPairAddress adrs.getKeyPairAddress).setChainAddress i

/-- Address for compressing the `len` chain ends into the WOTS public key (type `WOTS_PK`). -/
def wotsPkAdrs (adrs : Adrs) : Adrs :=
  (adrs.setTypeAndClear .wotsPk).setKeyPairAddress adrs.getKeyPairAddress

/-- A canonical narrow base address yields a canonical WOTS secret-key address whenever the
chain index fits its four-byte field. -/
theorem wotsSkAdrs_isCanonical (adrs : Adrs) (i : ℕ)
    (hbase : adrs.isCanonical = true) (hi : Adrs.Fits 4 i = true) :
    (wotsSkAdrs adrs i).isCanonical = true := by
  rcases Adrs.fits_of_isCanonical adrs hbase with
    ⟨hlayer, htree, _htype, hword1, _hword2, _hword3⟩
  simp [wotsSkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
    Adrs.setChainAddress, Adrs.getKeyPairAddress, Adrs.isCanonical,
    hlayer, htree, hword1, hi]
  norm_num [Adrs.Fits, AddrType.toCode]

/-- Every WOTS hash-step address is canonical when its chain and hash indices fit their
four-byte fields. -/
theorem wotsChainHashAdrs_isCanonical (adrs : Adrs) (i j : ℕ)
    (hbase : adrs.isCanonical = true) (hi : Adrs.Fits 4 i = true)
    (hj : Adrs.Fits 4 j = true) :
    ((wotsChainAdrs adrs i).setHashAddress j).isCanonical = true := by
  rcases Adrs.fits_of_isCanonical adrs hbase with
    ⟨hlayer, htree, _htype, hword1, _hword2, _hword3⟩
  simp [wotsChainAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
    Adrs.setChainAddress, Adrs.setHashAddress, Adrs.getKeyPairAddress,
    Adrs.isCanonical, hlayer, htree, hword1, hi, hj]
  norm_num [Adrs.Fits, AddrType.toCode]

/-- WOTS public-key compression preserves canonicality of a canonical base address. -/
theorem wotsPkAdrs_isCanonical (adrs : Adrs) (hbase : adrs.isCanonical = true) :
    (wotsPkAdrs adrs).isCanonical = true := by
  rcases Adrs.fits_of_isCanonical adrs hbase with
    ⟨hlayer, htree, _htype, hword1, _hword2, _hword3⟩
  simp [wotsPkAdrs, Adrs.setTypeAndClear, Adrs.setKeyPairAddress,
    Adrs.getKeyPairAddress, Adrs.isCanonical, hlayer, htree, hword1]
  norm_num [Adrs.Fits, AddrType.toCode]

/-! ### Message-to-digit derivation (FIPS 205 §5.2–5.4) -/

/-- The `len1` base-`w` message digits of the node being signed, computed from the
implementation-independent context. -/
def wotsMsgDigitsCore (core : CorePrimitives p) (msg : core.Y) : List ℕ :=
  base2b (core.yToBytes msg).toList p.lgw p.len1

/-- The full step-count list: message digits followed by the base-`w` checksum digits; length
`len`, computed from the implementation-independent context. -/
def chainLengthsCore (core : CorePrimitives p) (msg : core.Y) : List ℕ :=
  WotsEncoding.fullDigits p (wotsMsgDigitsCore core msg)

/-- The operational FIPS byte pipeline is exactly the mathematical checksum view. -/
theorem chainLengthsCore_eq_wotsFullDigits (valid : p.Valid) (core : CorePrimitives p)
    (msg : core.Y) :
    chainLengthsCore core msg =
      wotsFullDigits (wotsMsgDigitsCore core msg) p.w p.len1 p.len2 := by
  apply fullDigits_eq_wotsFullDigits valid
  · exact base2b_length _ _ _
  · intro d hd
    simpa only [Params.w] using
      base2b_lt (core.yToBytes msg).toList p.lgw p.len1 d hd

/-- The operational chain-length list has the intrinsic WOTS `len` width. -/
@[simp] theorem chainLengthsCore_length (core : CorePrimitives p) (msg : core.Y) :
    (chainLengthsCore core msg).length = p.len := by
  apply fullDigits_length
  exact base2b_length _ _ _

/-- Every entry of `chainLengthsCore` is a genuine base-`w` digit (`< w`). -/
theorem chainLengthsCore_mem_lt (core : CorePrimitives p) (msg : core.Y) :
    ∀ d ∈ chainLengthsCore core msg, d < p.w := by
  apply fullDigits_lt
  intro d hd
  simpa only [Params.w] using
    base2b_lt (core.yToBytes msg).toList p.lgw p.len1 d hd

/-- The step count of chain `i`: the `i`-th entry of `chainLengthsCore` (`0` past the end). -/
def chainStepsCore (core : CorePrimitives p) (msg : core.Y) (i : ℕ) : ℕ :=
  (chainLengthsCore core msg).getD i 0

theorem chainStepsCore_lt (core : CorePrimitives p) (msg : core.Y) (i : ℕ) :
    chainStepsCore core msg i < p.w := by
  unfold chainStepsCore
  rw [List.getD_eq_getElem?_getD]
  rcases lt_or_ge i (chainLengthsCore core msg).length with h | h
  · rw [List.getElem?_eq_getElem h]
    simpa using chainLengthsCore_mem_lt core msg _ (List.getElem_mem h)
  · rw [List.getElem?_eq_none h]
    simpa using Params.w_pos p

theorem chainStepsCore_le (core : CorePrimitives p) (msg : core.Y) (i : ℕ) :
    chainStepsCore core msg i ≤ p.w - 1 :=
  Nat.le_sub_one_of_lt (chainStepsCore_lt core msg i)

/-! ### Public-key generation, signing, and recovery -/

/-- A WOTS+ signature: the `len` chain values, length-indexed. -/
abbrev WotsSig (p : Params) (core : CorePrimitives p) := Vector core.Y p.len

/-- Low-level callback-parametric implementation of all WOTS+ public-key chain ends. -/
def wotsPkGenTopsWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) : m (Vector core.Y p.len) :=
  Vector.ofFnM fun i =>
    chainWith hash (wotsChainAdrs adrs i.val)
      (core.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (p.w - 1)

/-- Low-level callback-parametric implementation of WOTS+ public-key generation. -/
def wotsPkGenWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) : m core.Y := do
  let tops ← wotsPkGenTopsWith core hash sk pk adrs
  compress (wotsPkAdrs adrs) tops.toList

/-- Canonical explicit-public-hash program for the `len` WOTS+ public-key chain ends. -/
def wotsPkGenTopsM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) : m (Vector core.Y p.len) :=
  wotsPkGenTopsWith core (PublicHash.f core pk) sk pk adrs

/-- Canonical explicit-public-hash WOTS+ public-key generation program (FIPS 205 Algorithm 6). -/
def wotsPkGenM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) : m core.Y :=
  wotsPkGenWith core (PublicHash.f core pk) (PublicHash.tl core pk) sk pk adrs

/-- The deterministic interpretation of all WOTS+ public-key chain ends. -/
def wotsPkGenTops (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : Vector prims.Y p.len :=
  simulateQ (PublicHash.impl prims)
    (wotsPkGenTopsM prims.core sk pk adrs :
      OracleComp (publicHashSpec prims.core) (Vector prims.Y p.len))

/-- WOTS+ public-key generation (FIPS 205 Algorithm 6), interpreted deterministically. -/
def wotsPkGen (prims : Primitives p) (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    prims.Y :=
  simulateQ (PublicHash.impl prims)
    (wotsPkGenM prims.core sk pk adrs :
      OracleComp (publicHashSpec prims.core) prims.Y)

/-- Low-level callback-parametric implementation of WOTS+ signing. -/
def wotsSignWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) : m (WotsSig p core) :=
  Vector.ofFnM fun i =>
    chainWith hash (wotsChainAdrs adrs i.val)
      (core.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (chainStepsCore core msg i.val)

/-- Canonical explicit-public-hash WOTS+ signing program (FIPS 205 Algorithm 7). -/
def wotsSignM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) : m (WotsSig p core) :=
  wotsSignWith core (PublicHash.f core pk) msg sk pk adrs

/-- WOTS+ signing (FIPS 205 Algorithm 7), interpreted deterministically. -/
def wotsSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs) : WotsSig p prims.core :=
  simulateQ (PublicHash.impl prims)
    (wotsSignM prims.core msg sk pk adrs :
      OracleComp (publicHashSpec prims.core) (WotsSig p prims.core))

/-- Low-level callback-parametric implementation of recovered WOTS+ chain ends. -/
def wotsPkFromSigTopsWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (sig : WotsSig p core) (msg : core.Y) (adrs : Adrs) : m (Vector core.Y p.len) :=
  Vector.ofFnM fun i =>
    chainWith hash (wotsChainAdrs adrs i.val) sig[i.val] (chainStepsCore core msg i.val)
      (p.w - 1 - chainStepsCore core msg i.val)

/-- Low-level callback-parametric implementation of WOTS+ public-key recovery. -/
def wotsPkFromSigWith (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (sig : WotsSig p core) (msg : core.Y) (adrs : Adrs) : m core.Y := do
  let tops ← wotsPkFromSigTopsWith core hash sig msg adrs
  compress (wotsPkAdrs adrs) tops.toList

/-- Canonical explicit-public-hash program for the `len` chain ends recovered from a signature. -/
def wotsPkFromSigTopsM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (sig : WotsSig p core) (msg : core.Y) (pk : core.PkSeed)
    (adrs : Adrs) : m (Vector core.Y p.len) :=
  wotsPkFromSigTopsWith core (PublicHash.f core pk) sig msg adrs

/-- Canonical explicit-public-hash WOTS+ public-key recovery program. -/
def wotsPkFromSigM (core : CorePrimitives p) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (sig : WotsSig p core) (msg : core.Y) (pk : core.PkSeed)
    (adrs : Adrs) : m core.Y :=
  wotsPkFromSigWith core (PublicHash.f core pk) (PublicHash.tl core pk)
    sig msg adrs

/-- The deterministic interpretation of recovered WOTS+ chain ends. -/
def wotsPkFromSigTops (prims : Primitives p) (sig : WotsSig p prims.core) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : Vector prims.Y p.len :=
  simulateQ (PublicHash.impl prims)
    (wotsPkFromSigTopsM prims.core sig msg pk adrs :
      OracleComp (publicHashSpec prims.core) (Vector prims.Y p.len))

/-- WOTS+ public-key recovery from a signature (FIPS 205 Algorithm 8), interpreted
deterministically. -/
def wotsPkFromSig (prims : Primitives p) (sig : WotsSig p prims.core) (msg : prims.Y)
    (pk : prims.PkSeed) (adrs : Adrs) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (wotsPkFromSigM prims.core sig msg pk adrs :
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

/-- A monad morphism commutes with WOTS+ public-key chain generation when it commutes with the
hash callback. -/
theorem wotsPkGenTopsWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    F (wotsPkGenTopsWith core hashm sk pk adrs) =
      wotsPkGenTopsWith core hashn sk pk adrs := by
  apply monadHom_ofFnM F
  intro i
  exact chainWith_natural F hashm hashn hhash _ _ _ _

/-- A monad morphism commutes with WOTS+ public-key generation when it commutes with the public
hash and compression callbacks. -/
theorem wotsPkGenWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y)
    (compressn : Adrs → List core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    F (wotsPkGenWith core hashm compressm sk pk adrs) =
      wotsPkGenWith core hashn compressn sk pk adrs := by
  simp [wotsPkGenWith, F.mmap_bind,
    wotsPkGenTopsWith_natural F core hashm hashn hhash, hcompress]

/-- A monad morphism commutes with WOTS+ signing when it commutes with the hash callback. -/
theorem wotsSignWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    F (wotsSignWith core hashm msg sk pk adrs) =
      wotsSignWith core hashn msg sk pk adrs := by
  apply monadHom_ofFnM F
  intro i
  exact chainWith_natural F hashm hashn hhash _ _ _ _

/-- A monad morphism commutes with WOTS+ recovery-chain generation when it commutes with the
hash callback. -/
theorem wotsPkFromSigTopsWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (sig : WotsSig p core) (msg : core.Y) (adrs : Adrs) :
    F (wotsPkFromSigTopsWith core hashm sig msg adrs) =
      wotsPkFromSigTopsWith core hashn sig msg adrs := by
  apply monadHom_ofFnM F
  intro i
  exact chainWith_natural F hashm hashn hhash _ _ _ _

/-- A monad morphism commutes with WOTS+ public-key recovery when it commutes with the public
hash and compression callbacks. -/
theorem wotsPkFromSigWith_natural {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] (F : m →ᵐ n) (core : CorePrimitives p)
    (hashm : Adrs → core.Y → m core.Y) (hashn : Adrs → core.Y → n core.Y)
    (compressm : Adrs → List core.Y → m core.Y)
    (compressn : Adrs → List core.Y → n core.Y)
    (hhash : ∀ a y, F (hashm a y) = hashn a y)
    (hcompress : ∀ a ys, F (compressm a ys) = compressn a ys)
    (sig : WotsSig p core) (msg : core.Y) (adrs : Adrs) :
    F (wotsPkFromSigWith core hashm compressm sig msg adrs) =
      wotsPkFromSigWith core hashn compressn sig msg adrs := by
  simp [wotsPkFromSigWith, F.mmap_bind,
    wotsPkFromSigTopsWith_natural F core hashm hashn hhash, hcompress]

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

/-- Query-preserving monad morphisms commute with explicit WOTS+ public-key chain generation. -/
theorem wotsPkGenTopsM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    F.toMonadHom (wotsPkGenTopsM core sk pk adrs) = wotsPkGenTopsM core sk pk adrs :=
  wotsPkGenTopsWith_natural F.toMonadHom core _ _ (queryHom_f core F pk) sk pk adrs

/-- Query-preserving monad morphisms commute with explicit WOTS+ public-key generation. -/
theorem wotsPkGenM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    F.toMonadHom (wotsPkGenM core sk pk adrs) = wotsPkGenM core sk pk adrs :=
  wotsPkGenWith_natural F.toMonadHom core _ _ _ _
    (queryHom_f core F pk) (queryHom_tl core F pk) sk pk adrs

/-- Query-preserving monad morphisms commute with explicit WOTS+ signing. -/
theorem wotsSignM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) :
    F.toMonadHom (wotsSignM core msg sk pk adrs) = wotsSignM core msg sk pk adrs :=
  wotsSignWith_natural F.toMonadHom core _ _ (queryHom_f core F pk) msg sk pk adrs

/-- Query-preserving monad morphisms commute with explicit WOTS+ recovery-chain generation. -/
theorem wotsPkFromSigTopsM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sig : WotsSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) :
    F.toMonadHom (wotsPkFromSigTopsM core sig msg pk adrs) =
      wotsPkFromSigTopsM core sig msg pk adrs :=
  wotsPkFromSigTopsWith_natural F.toMonadHom core _ _ (queryHom_f core F pk) sig msg adrs

/-- Query-preserving monad morphisms commute with explicit WOTS+ public-key recovery. -/
theorem wotsPkFromSigM_natural (core : CorePrimitives p)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sig : WotsSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) :
    F.toMonadHom (wotsPkFromSigM core sig msg pk adrs) =
      wotsPkFromSigM core sig msg pk adrs :=
  wotsPkFromSigWith_natural F.toMonadHom core _ _ _ _
    (queryHom_f core F pk) (queryHom_tl core F pk) sig msg adrs

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
      rw [Vector.ofFnM_succ]
      rw [Fin.sum_univ_castSucc]
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

private theorem publicHash_tl_isTotalQueryBound_one (core : CorePrimitives p)
    (pk : core.PkSeed) (adrs : Adrs) (xs : List core.Y) :
    IsTotalQueryBound
      (PublicHash.tl core pk adrs xs : OracleComp (publicHashSpec core) core.Y) 1 := by
  simp [PublicHash.tl, IsTotalQueryBound]

/-- An explicit WOTS+ chain of length `s` makes at most `s` public-hash queries. -/
theorem chainM_isTotalQueryBound (core : CorePrimitives p) (pk : core.PkSeed)
    (adrs : Adrs) (x : core.Y) (i s : ℕ) :
    IsTotalQueryBound
      (chainM core pk adrs x i s : OracleComp (publicHashSpec core) core.Y) s := by
  induction s with
  | zero => trivial
  | succ s ih =>
      change IsTotalQueryBound
        (chainM core pk adrs x i s >>= fun y =>
          PublicHash.f core pk (adrs.setHashAddress (i + s)) y) (s + 1)
      exact isTotalQueryBound_bind ih fun y =>
        publicHash_f_isTotalQueryBound_one core pk _ y

/-- WOTS+ public-key chain generation makes at most `len * (w - 1)` public-hash queries. -/
theorem wotsPkGenTopsM_isTotalQueryBound (core : CorePrimitives p)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (wotsPkGenTopsM core sk pk adrs :
        OracleComp (publicHashSpec core) (Vector core.Y p.len))
      (p.len * (p.w - 1)) := by
  simpa [wotsPkGenTopsM, wotsPkGenTopsWith, chainM] using
    (isTotalQueryBound_ofFnM
      (fun i : Fin p.len =>
        chainM core pk (wotsChainAdrs adrs i.val)
          (core.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (p.w - 1))
      (fun _ => p.w - 1)
      (fun i => chainM_isTotalQueryBound core pk (wotsChainAdrs adrs i.val)
        (core.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (p.w - 1)))

/-- WOTS+ public-key generation adds one `T_l` query after generating all chain tops. -/
theorem wotsPkGenM_isTotalQueryBound (core : CorePrimitives p)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (wotsPkGenM core sk pk adrs : OracleComp (publicHashSpec core) core.Y)
      (p.len * (p.w - 1) + 1) := by
  exact isTotalQueryBound_bind (wotsPkGenTopsM_isTotalQueryBound core sk pk adrs)
    fun tops => publicHash_tl_isTotalQueryBound_one core pk (wotsPkAdrs adrs) tops.toList

/-- WOTS+ signing is bounded by one query for every message-selected chain step. -/
theorem wotsSignM_isTotalQueryBound (core : CorePrimitives p) (msg : core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (wotsSignM core msg sk pk adrs :
        OracleComp (publicHashSpec core) (WotsSig p core))
      (∑ i : Fin p.len, chainStepsCore core msg i.val) := by
  exact isTotalQueryBound_ofFnM _ _ fun i =>
    chainM_isTotalQueryBound core pk (wotsChainAdrs adrs i.val)
      (core.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (chainStepsCore core msg i.val)

/-- WOTS+ recovery-chain generation is bounded by the complementary number of chain queries. -/
theorem wotsPkFromSigTopsM_isTotalQueryBound (core : CorePrimitives p)
    (sig : WotsSig p core) (msg : core.Y) (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (wotsPkFromSigTopsM core sig msg pk adrs :
        OracleComp (publicHashSpec core) (Vector core.Y p.len))
      (∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) := by
  exact isTotalQueryBound_ofFnM _ _ fun i =>
    chainM_isTotalQueryBound core pk (wotsChainAdrs adrs i.val) sig[i.val]
      (chainStepsCore core msg i.val) (p.w - 1 - chainStepsCore core msg i.val)

/-- WOTS+ public-key recovery adds one `T_l` query after completing the chains. -/
theorem wotsPkFromSigM_isTotalQueryBound (core : CorePrimitives p)
    (sig : WotsSig p core) (msg : core.Y) (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound
      (wotsPkFromSigM core sig msg pk adrs : OracleComp (publicHashSpec core) core.Y)
      ((∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) + 1) := by
  exact isTotalQueryBound_bind
    (wotsPkFromSigTopsM_isTotalQueryBound core sig msg pk adrs)
    fun tops => publicHash_tl_isTotalQueryBound_one core pk (wotsPkAdrs adrs) tops.toList

/-- Signing followed by recovery is bounded by one full pass over every WOTS+ chain plus the
final `T_l` compression query. -/
theorem wotsSignM_then_wotsPkFromSigM_isTotalQueryBound (core : CorePrimitives p)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) :
    IsTotalQueryBound ((do
      let sig ← wotsSignM core msg sk pk adrs
      wotsPkFromSigM core sig msg pk adrs) :
        OracleComp (publicHashSpec core) core.Y)
      (p.len * (p.w - 1) + 1) := by
  have hbound := isTotalQueryBound_bind
    (wotsSignM_isTotalQueryBound core msg sk pk adrs)
    (fun sig => wotsPkFromSigM_isTotalQueryBound core sig msg pk adrs)
  have hsum :
      (∑ i : Fin p.len, chainStepsCore core msg i.val) +
          (∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) =
        p.len * (p.w - 1) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [Nat.add_sub_of_le (chainStepsCore_le core msg _)]
    simp
  simpa [← Nat.add_assoc, hsum] using hbound

/-! ### Pure interpretations -/

/-- Interpreting an `ofFnM` traversal pointwise commutes with the free-monad handler. -/
private theorem simulateQ_ofFnM {ι α : Type} {spec : OracleSpec ι} {k : ℕ}
    (answer : QueryImpl spec Id) (g : Fin k → OracleComp spec α) :
    simulateQ answer (Vector.ofFnM g) = Vector.ofFn fun i => simulateQ answer (g i) := by
  calc
    simulateQ answer (Vector.ofFnM g) =
        Vector.ofFnM (fun i => simulateQ answer (g i)) :=
      monadHom_ofFnM (simulateQ' answer) g _ (fun _ => rfl)
    _ = Vector.ofFn fun i => simulateQ answer (g i) := Vector.idRun_ofFnM

@[simp]
theorem wotsPkGenTops_eq_ofFn (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkGenTops prims sk pk adrs = Vector.ofFn fun i : Fin p.len =>
      chain prims pk (wotsChainAdrs adrs i.val)
        (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0 (p.w - 1) := by
  unfold wotsPkGenTops wotsPkGenTopsM wotsPkGenTopsWith
  rw [simulateQ_ofFnM]
  rfl

@[simp]
theorem wotsSign_eq_ofFn (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    wotsSign prims msg sk pk adrs = Vector.ofFn fun i : Fin p.len =>
      chain prims pk (wotsChainAdrs adrs i.val)
        (prims.PRF pk sk (wotsSkAdrs adrs i.val)) 0
          (chainStepsCore prims.core msg i.val) := by
  unfold wotsSign wotsSignM wotsSignWith
  rw [simulateQ_ofFnM]
  rfl

@[simp]
theorem wotsPkFromSigTops_eq_ofFn (prims : Primitives p) (sig : WotsSig p prims.core)
    (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkFromSigTops prims sig msg pk adrs = Vector.ofFn fun i : Fin p.len =>
      chain prims pk (wotsChainAdrs adrs i.val) sig[i.val]
        (chainStepsCore prims.core msg i.val)
        (p.w - 1 - chainStepsCore prims.core msg i.val) := by
  unfold wotsPkFromSigTops wotsPkFromSigTopsM wotsPkFromSigTopsWith
  rw [simulateQ_ofFnM]
  rfl

@[simp]
theorem wotsPkGen_eq_tl (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkGen prims sk pk adrs =
      prims.Tl pk (wotsPkAdrs adrs) (wotsPkGenTops prims sk pk adrs).toList := by
  simp only [wotsPkGen, wotsPkGenM, wotsPkGenWith, simulateQ_bind,
    PublicHash.tl, simulateQ_HasQuery_query, PublicHash.impl]
  rfl

@[simp]
theorem wotsPkFromSig_eq_tl (prims : Primitives p) (sig : WotsSig p prims.core)
    (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkFromSig prims sig msg pk adrs =
      prims.Tl pk (wotsPkAdrs adrs) (wotsPkFromSigTops prims sig msg pk adrs).toList := by
  simp only [wotsPkFromSig, wotsPkFromSigM, wotsPkFromSigWith, simulateQ_bind,
    PublicHash.tl, simulateQ_HasQuery_query, PublicHash.impl]
  rfl

/-! ### Deterministic interpretations -/

/-- Any deterministic public-hash handler turns the canonical chain program into the pure chain
for the induced primitive bundle. -/
@[simp] theorem simulateQ_chainM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (pkSeed : core.PkSeed) (adrs : Adrs)
    (x : core.Y) (i s : ℕ) :
    simulateQ answer
        (chainM core pkSeed adrs x i s : OracleComp (publicHashSpec core) core.Y) =
      chain (PublicHash.withPublicHash core answer) pkSeed adrs x i s := by
  simp [chain, PublicHash.impl_withPublicHash]

/-- The canonical concrete handler recovers the pure WOTS+ chain by definition. -/
@[simp] theorem simulateQ_chainM (prims : Primitives p) (pkSeed : prims.PkSeed)
    (adrs : Adrs) (x : prims.Y) (i s : ℕ) :
    simulateQ (PublicHash.impl prims)
        (chainM prims.core pkSeed adrs x i s :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      chain prims pkSeed adrs x i s := rfl

@[simp] theorem simulateQ_wotsPkGenTopsM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) :
    simulateQ answer
        (wotsPkGenTopsM core sk pk adrs :
          OracleComp (publicHashSpec core) (Vector core.Y p.len)) =
      wotsPkGenTops (PublicHash.withPublicHash core answer) sk pk adrs := by
  simp [wotsPkGenTops, PublicHash.impl_withPublicHash]

@[simp] theorem simulateQ_wotsPkGenTopsM (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkGenTopsM prims.core sk pk adrs :
          OracleComp (publicHashSpec prims.core) (Vector prims.Y p.len)) =
      wotsPkGenTops prims sk pk adrs := rfl

@[simp] theorem simulateQ_wotsPkGenM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) :
    simulateQ answer
        (wotsPkGenM core sk pk adrs : OracleComp (publicHashSpec core) core.Y) =
      wotsPkGen (PublicHash.withPublicHash core answer) sk pk adrs := by
  simp [wotsPkGen, PublicHash.impl_withPublicHash]

@[simp] theorem simulateQ_wotsPkGenM (prims : Primitives p) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkGenM prims.core sk pk adrs :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      wotsPkGen prims sk pk adrs := rfl

@[simp] theorem simulateQ_wotsSignM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (msg : core.Y) (sk : core.SkSeed)
    (pk : core.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (wotsSignM core msg sk pk adrs :
          OracleComp (publicHashSpec core) (WotsSig p core)) =
      wotsSign (PublicHash.withPublicHash core answer) msg sk pk adrs := by
  simp [wotsSign, PublicHash.impl_withPublicHash]

@[simp] theorem simulateQ_wotsSignM (prims : Primitives p) (msg : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsSignM prims.core msg sk pk adrs :
          OracleComp (publicHashSpec prims.core) (WotsSig p prims.core)) =
      wotsSign prims msg sk pk adrs := rfl

@[simp] theorem simulateQ_wotsPkFromSigTopsM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (sig : WotsSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (wotsPkFromSigTopsM core sig msg pk adrs :
          OracleComp (publicHashSpec core) (Vector core.Y p.len)) =
      wotsPkFromSigTops (PublicHash.withPublicHash core answer) sig msg pk adrs := by
  simp [wotsPkFromSigTops, PublicHash.impl_withPublicHash]

@[simp] theorem simulateQ_wotsPkFromSigTopsM (prims : Primitives p)
    (sig : WotsSig p prims.core) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkFromSigTopsM prims.core sig msg pk adrs :
          OracleComp (publicHashSpec prims.core) (Vector prims.Y p.len)) =
      wotsPkFromSigTops prims sig msg pk adrs := rfl

@[simp] theorem simulateQ_wotsPkFromSigM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (sig : WotsSig p core) (msg : core.Y)
    (pk : core.PkSeed) (adrs : Adrs) :
    simulateQ answer
        (wotsPkFromSigM core sig msg pk adrs : OracleComp (publicHashSpec core) core.Y) =
      wotsPkFromSig (PublicHash.withPublicHash core answer) sig msg pk adrs := by
  simp [wotsPkFromSig, PublicHash.impl_withPublicHash]

@[simp] theorem simulateQ_wotsPkFromSigM (prims : Primitives p)
    (sig : WotsSig p prims.core) (msg : prims.Y) (pk : prims.PkSeed) (adrs : Adrs) :
    simulateQ (PublicHash.impl prims)
        (wotsPkFromSigM prims.core sig msg pk adrs :
          OracleComp (publicHashSpec prims.core) prims.Y) =
      wotsPkFromSig prims sig msg pk adrs := rfl

/-! ### Correctness -/

/-- Recovering the chain ends from an honest signature reproduces the public-key chain ends. -/
theorem wotsPkFromSigTops_wotsSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkFromSigTops prims (wotsSign prims msg sk pk adrs) msg pk adrs
      = wotsPkGenTops prims sk pk adrs := by
  apply Vector.ext
  intro i hi
  simp only [wotsPkFromSigTops_eq_ofFn, wotsPkGenTops_eq_ofFn, wotsSign_eq_ofFn,
    Vector.getElem_ofFn]
  have hc := chain_compose prims pk (wotsChainAdrs adrs i)
    (prims.PRF pk sk (wotsSkAdrs adrs i)) 0 (chainStepsCore prims.core msg i)
    (p.w - 1 - chainStepsCore prims.core msg i)
  rw [Nat.zero_add] at hc
  rw [hc, Nat.add_sub_cancel' (chainStepsCore_le prims.core msg i)]

/-- **WOTS+ correctness** (FIPS 205, Algorithms 6–8): recovering the public key from an honest
signature reproduces `wotsPkGen`. -/
theorem wotsPkFromSig_wotsSign (prims : Primitives p) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) :
    wotsPkFromSig prims (wotsSign prims msg sk pk adrs) msg pk adrs
      = wotsPkGen prims sk pk adrs := by
  rw [wotsPkFromSig_eq_tl, wotsPkGen_eq_tl]
  rw [wotsPkFromSigTops_wotsSign]

/-- Extensional WOTS+ completeness for every fixed total public-hash answer table.

This is a stateless `QueryImpl ... Id` theorem. It does not by itself establish completeness for
the lazy cached random-oracle handler; the full-table/lazy-oracle bridge is a separate obligation
for the security layer. -/
theorem simulateQ_wotsPkFromSigM_wotsSignM_withPublicHash (core : CorePrimitives p)
    (answer : QueryImpl (publicHashSpec core) Id) (msg : core.Y) (sk : core.SkSeed)
    (pk : core.PkSeed) (adrs : Adrs) :
    simulateQ answer (do
      let sig ← wotsSignM core msg sk pk adrs
      wotsPkFromSigM core sig msg pk adrs) =
    simulateQ answer (wotsPkGenM core sk pk adrs) := by
  simp only [simulateQ_bind, simulateQ_wotsSignM_withPublicHash,
    simulateQ_wotsPkFromSigM_withPublicHash, simulateQ_wotsPkGenM_withPublicHash]
  exact wotsPkFromSig_wotsSign (PublicHash.withPublicHash core answer) msg sk pk adrs

end SLHDSA
