/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Quang Dao
-/

module
public import HashSig.SLHDSA.Fors

/-!
# Hypertree (FIPS 205 §7)

Hypertree signatures are represented canonically as exactly `d` intrinsically shaped XMSS
signatures.  The executable algorithms here are explicit single-layer wrappers requiring a proof
that `d = 1`.  For the SLH-DSA-SHA2-128-24 parameter set, Algorithms 12–13 then collapse to one
XMSS layer. The `*M` algorithms in this file depend only on `CorePrimitives` and issue every
public hash through `HasQuery`. The established pure API is defined as the literal `simulateQ`
interpretation of those programs.

The `*With` definitions expose the thin callback-parametric composition with XMSS. The
`htPkFromSigM` recovery function is the computational core of verification; keeping it visible
makes the exact extractor- and reduction-facing computation inspectable before the final Boolean
comparison in `htVerifyM`.

No multi-layer signature is synthesized by duplicating that one layer.

## References

- NIST FIPS 205, §7 (Algorithms 12–13)
-/

@[expose] public section


namespace SLHDSA

open OracleComp

variable {p : Params}

/-- A hypertree signature contains exactly one intrinsically shaped XMSS signature per layer. -/
abbrev HtSigCore (p : Params) (core : CorePrimitives p) := Vector (XmssSigCore p core) p.d

namespace HtSigCore

variable {core : CorePrimitives p}

/-- Package the only XMSS signature of a proven single-layer parameter set. -/
def singleLayer (_hd : p.d = 1) (sig : XmssSigCore p core) : HtSigCore p core :=
  Vector.ofFn fun _ => sig

/-- Project the only XMSS signature of a proven single-layer parameter set. -/
def getSingleLayer (hd : p.d = 1) (sig : HtSigCore p core) : XmssSigCore p core :=
  sig[0]'(by omega)

@[simp]
theorem getSingleLayer_singleLayer (hd : p.d = 1) (sig : XmssSigCore p core) :
    getSingleLayer hd (singleLayer hd sig) = sig := by
  simp [getSingleLayer, singleLayer]

/-- Every intrinsically shaped hypertree signature of a proven single-layer parameter set is
the canonical singleton wrapper of its only XMSS signature. -/
@[simp]
theorem singleLayer_getSingleLayer (hd : p.d = 1) (sig : HtSigCore p core) :
    singleLayer hd (getSingleLayer hd sig) = sig := by
  let zero : Fin p.d := ⟨0, by omega⟩
  apply Vector.ext
  intro i hi
  have hizero : i = zero.val := by omega
  subst i
  simp [singleLayer, getSingleLayer, zero]

/-- Intrinsically shaped hypertree signatures at depth one are equivalent to one XMSS
signature.  This is the compatibility boundary used by the reduced-profile algorithms; it does
not define behavior for a multi-layer signature. -/
def singleLayerEquiv (hd : p.d = 1) : HtSigCore p core ≃ XmssSigCore p core where
  toFun := getSingleLayer hd
  invFun := singleLayer hd
  left_inv := singleLayer_getSingleLayer hd
  right_inv := getSingleLayer_singleLayer hd

end HtSigCore

/-- Address of the single hypertree layer (layer `0`, tree `idxTree`). -/
def htAdrs (adrs : Adrs) (idxTree : ℕ) : Adrs :=
  (adrs.setLayerAddress 0).setTreeAddress idxTree

/-! ### Low-level callback-parametric helpers -/

/-- Callback-parametric hypertree signing for `d = 1`. -/
def htSignWith (core : CorePrimitives p) (hd : p.d = 1) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) : m (HtSigCore p core) := do
  let sig ← xmssSignWith core hash compress nodeHash msg sk pk (htAdrs adrs idxTree) idxLeaf
  return HtSigCore.singleLayer hd sig

/-- Callback-parametric hypertree root generation for `d = 1`. -/
def htRootWith (core : CorePrimitives p) (_hd : p.d = 1) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idxTree : ℕ) : m core.Y :=
  xmssRootWith core hash compress nodeHash sk pk (htAdrs adrs idxTree)

/-- Callback-parametric recovery of the root authenticated by a `d = 1` hypertree signature. -/
def htPkFromSigWith (core : CorePrimitives p) (hd : p.d = 1) {m : Type → Type*} [Monad m]
    (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (msg : core.Y) (sig : HtSigCore p core) (adrs : Adrs)
    (idxTree idxLeaf : ℕ) : m core.Y :=
  xmssPkFromSigWith core hash compress nodeHash idxLeaf (HtSigCore.getSingleLayer hd sig) msg
    (htAdrs adrs idxTree)

/-! ### Canonical explicit-public-hash programs -/

/-- Canonical explicit-public-hash hypertree signing for `d = 1`. -/
def htSignM (core : CorePrimitives p) (hd : p.d = 1) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) : m (HtSigCore p core) :=
  htSignWith core hd (PublicHash.f core pk) (PublicHash.tl core pk)
    (PublicHash.h core pk) msg sk pk adrs idxTree idxLeaf

/-- Canonical explicit-public-hash hypertree root generation for `d = 1`. -/
def htRootM (core : CorePrimitives p) (hd : p.d = 1) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idxTree : ℕ) : m core.Y :=
  htRootWith core hd (PublicHash.f core pk) (PublicHash.tl core pk)
    (PublicHash.h core pk) sk pk adrs idxTree

/-- Canonical explicit-public-hash recovery of the root authenticated by a hypertree signature. -/
def htPkFromSigM (core : CorePrimitives p) (hd : p.d = 1) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sig : HtSigCore p core) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) : m core.Y :=
  htPkFromSigWith core hd (PublicHash.f core pk) (PublicHash.tl core pk)
    (PublicHash.h core pk) msg sig adrs idxTree idxLeaf

/-- Canonical explicit-public-hash hypertree verification. The only non-oracle step is the final
comparison with the claimed root. -/
def htVerifyM (core : CorePrimitives p) (hd : p.d = 1) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] [DecidableEq core.Y]
    (msg : core.Y) (sig : HtSigCore p core) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) (pkRoot : core.Y) : m Bool := do
  let recovered ← htPkFromSigM core hd msg sig pk adrs idxTree idxLeaf
  return decide (recovered = pkRoot)

/-! ### Naturality -/

/-- Query-preserving monad morphisms commute with `d = 1` hypertree signing. -/
theorem htSignM_natural (core : CorePrimitives p) (hd : p.d = 1)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    F.toMonadHom (htSignM core hd msg sk pk adrs idxTree idxLeaf) =
      htSignM core hd msg sk pk adrs idxTree idxLeaf := by
  change F.toMonadHom (do
    let sig ← xmssSignM core msg sk pk (htAdrs adrs idxTree) idxLeaf
    return HtSigCore.singleLayer hd sig) = (do
      let sig ← xmssSignM core msg sk pk (htAdrs adrs idxTree) idxLeaf
      return HtSigCore.singleLayer hd sig)
  rw [F.mmap_bind, xmssSignM_natural core F]
  simp

/-- Query-preserving monad morphisms commute with `d = 1` hypertree root generation. -/
theorem htRootM_natural (core : CorePrimitives p) (hd : p.d = 1)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idxTree : ℕ) :
    F.toMonadHom (htRootM core hd sk pk adrs idxTree) =
      htRootM core hd sk pk adrs idxTree := by
  exact xmssRootM_natural core F sk pk (htAdrs adrs idxTree)

/-- Query-preserving monad morphisms commute with `d = 1` hypertree root recovery. -/
theorem htPkFromSigM_natural (core : CorePrimitives p) (hd : p.d = 1)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : core.Y) (sig : HtSigCore p core) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    F.toMonadHom (htPkFromSigM core hd msg sig pk adrs idxTree idxLeaf) =
      htPkFromSigM core hd msg sig pk adrs idxTree idxLeaf := by
  exact xmssPkFromSigM_natural core F idxLeaf (HtSigCore.getSingleLayer hd sig) msg pk
    (htAdrs adrs idxTree)

/-- Query-preserving monad morphisms commute with `d = 1` hypertree verification, including
the pure final comparison after oracle-parametric root recovery. -/
theorem htVerifyM_natural (core : CorePrimitives p) (hd : p.d = 1)
    {m n : Type → Type*} [Monad m] [LawfulMonad m]
    [Monad n] [LawfulMonad n] [HasQuery (publicHashSpec core) m]
    [HasQuery (publicHashSpec core) n] [DecidableEq core.Y]
    (F : HasQuery.QueryHom (publicHashSpec core) m n)
    (msg : core.Y) (sig : HtSigCore p core) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) (pkRoot : core.Y) :
    F.toMonadHom (htVerifyM core hd msg sig pk adrs idxTree idxLeaf pkRoot) =
      htVerifyM core hd msg sig pk adrs idxTree idxLeaf pkRoot := by
  simp [htVerifyM, htPkFromSigM_natural core hd F]

/-! ### Structural query bounds -/

/-- The single-layer hypertree root has exactly the inherited XMSS structural upper bound. -/
theorem htRootM_isTotalQueryBound (core : CorePrimitives p) (hd : p.d = 1)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idxTree : ℕ) :
    IsTotalQueryBound
      (htRootM core hd sk pk adrs idxTree : OracleComp (publicHashSpec core) core.Y)
      (xmssNodeQueryBound p p.hp) :=
  xmssRootM_isTotalQueryBound core sk pk (htAdrs adrs idxTree)

/-- Hypertree signing inherits the XMSS authentication-path and WOTS+ chain budget. -/
theorem htSignM_isTotalQueryBound (core : CorePrimitives p) (hd : p.d = 1)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    IsTotalQueryBound
      (htSignM core hd msg sk pk adrs idxTree idxLeaf :
        OracleComp (publicHashSpec core) (HtSigCore p core))
      ((∑ i : Fin p.len, chainStepsCore core msg i.val) +
        xmssAuthPathQueryBound p p.hp) :=
by
  change IsTotalQueryBound (do
    let sig ← xmssSignM core msg sk pk (htAdrs adrs idxTree) idxLeaf
    return HtSigCore.singleLayer hd sig) _
  simpa using isTotalQueryBound_bind (n₂ := 0)
    (xmssSignM_isTotalQueryBound core msg sk pk (htAdrs adrs idxTree) idxLeaf)
    (fun sig => show IsTotalQueryBound
      (pure (HtSigCore.singleLayer hd sig) : OracleComp (publicHashSpec core) _) 0 from trivial)

/-- Hypertree root recovery inherits the complementary WOTS+ and supplied-path budget. -/
theorem htPkFromSigM_isTotalQueryBound (core : CorePrimitives p) (hd : p.d = 1)
    (msg : core.Y) (sig : HtSigCore p core) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    IsTotalQueryBound
      (htPkFromSigM core hd msg sig pk adrs idxTree idxLeaf :
        OracleComp (publicHashSpec core) core.Y)
      ((∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) +
        1 + p.hp) :=
  xmssPkFromSigM_isTotalQueryBound core idxLeaf (HtSigCore.getSingleLayer hd sig) msg pk
    (htAdrs adrs idxTree)

/-- The final Boolean comparison adds no oracle query to the inherited recovery budget. -/
theorem htVerifyM_isTotalQueryBound (core : CorePrimitives p) (hd : p.d = 1)
    [DecidableEq core.Y]
    (msg : core.Y) (sig : HtSigCore p core) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) (pkRoot : core.Y) :
    IsTotalQueryBound
      (htVerifyM core hd msg sig pk adrs idxTree idxLeaf pkRoot :
        OracleComp (publicHashSpec core) Bool)
      ((∑ i : Fin p.len, (p.w - 1 - chainStepsCore core msg i.val)) +
        1 + p.hp) := by
  have hbound := isTotalQueryBound_bind
    (htPkFromSigM_isTotalQueryBound core hd msg sig pk adrs idxTree idxLeaf) fun recovered =>
      show IsTotalQueryBound
        (pure (decide (recovered = pkRoot)) : OracleComp (publicHashSpec core) Bool) 0 from trivial
  simpa [htVerifyM] using hbound

/-! ### Pure deterministic interpretations -/

/-- Pure hypertree signing is the deterministic interpretation of `htSignM`. -/
def htSign (prims : Primitives p) (hd : p.d = 1) (msg : prims.Y) (sk : prims.SkSeed)
    (pk : prims.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) : HtSigCore p prims.core :=
  simulateQ (PublicHash.impl prims)
    (htSignM prims.core hd msg sk pk adrs idxTree idxLeaf :
      OracleComp (publicHashSpec prims.core) (HtSigCore p prims.core))

/-- Pure hypertree root generation is the deterministic interpretation of `htRootM`. -/
def htRoot (prims : Primitives p) (hd : p.d = 1) (sk : prims.SkSeed) (pk : prims.PkSeed)
    (adrs : Adrs)
    (idxTree : ℕ) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (htRootM prims.core hd sk pk adrs idxTree :
      OracleComp (publicHashSpec prims.core) prims.Y)

/-- Pure recovery is the deterministic interpretation of `htPkFromSigM`. -/
def htPkFromSig (prims : Primitives p) (hd : p.d = 1) (msg : prims.Y)
    (sig : HtSigCore p prims.core)
    (pk : prims.PkSeed) (adrs : Adrs) (idxTree idxLeaf : ℕ) : prims.Y :=
  simulateQ (PublicHash.impl prims)
    (htPkFromSigM prims.core hd msg sig pk adrs idxTree idxLeaf :
      OracleComp (publicHashSpec prims.core) prims.Y)

/-- Pure verification is the deterministic interpretation of `htVerifyM`. -/
def htVerify (prims : Primitives p) (hd : p.d = 1) [DecidableEq prims.Y] (msg : prims.Y)
    (sig : HtSigCore p prims.core) (pk : prims.PkSeed) (adrs : Adrs)
    (idxTree idxLeaf : ℕ) (pkRoot : prims.Y) : Bool :=
  simulateQ (PublicHash.impl prims)
    (htVerifyM prims.core hd msg sig pk adrs idxTree idxLeaf pkRoot :
      OracleComp (publicHashSpec prims.core) Bool)

/-! ### Pure API equations -/

@[simp]
theorem htSign_eq_xmssSign (prims : Primitives p) (hd : p.d = 1) (msg : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    htSign prims hd msg sk pk adrs idxTree idxLeaf =
      HtSigCore.singleLayer hd (xmssSign prims msg sk pk (htAdrs adrs idxTree) idxLeaf) := by
  unfold htSign htSignM htSignWith
  simp only [simulateQ_bind, simulateQ_pure]
  change (do
    let x ← simulateQ (PublicHash.impl prims)
      (xmssSignM prims.core msg sk pk (htAdrs adrs idxTree) idxLeaf)
    pure (HtSigCore.singleLayer hd x)) = _
  rw [simulateQ_xmssSignM]
  simp
  rfl

@[simp]
theorem htRoot_eq_xmssRoot (prims : Primitives p) (hd : p.d = 1) (sk : prims.SkSeed)
    (pk : prims.PkSeed) (adrs : Adrs) (idxTree : ℕ) :
    htRoot prims hd sk pk adrs idxTree = xmssRoot prims sk pk (htAdrs adrs idxTree) := by
  rfl

@[simp]
theorem htPkFromSig_eq_xmssPkFromSig (prims : Primitives p) (hd : p.d = 1) (msg : prims.Y)
    (sig : HtSigCore p prims.core) (pk : prims.PkSeed) (adrs : Adrs)
    (idxTree idxLeaf : ℕ) :
    htPkFromSig prims hd msg sig pk adrs idxTree idxLeaf =
      xmssPkFromSig prims idxLeaf (HtSigCore.getSingleLayer hd sig) msg pk
        (htAdrs adrs idxTree) := by
  rfl

@[simp]
theorem htVerify_eq_decide (prims : Primitives p) (hd : p.d = 1) [DecidableEq prims.Y]
    (msg : prims.Y) (sig : HtSigCore p prims.core) (pk : prims.PkSeed) (adrs : Adrs)
    (idxTree idxLeaf : ℕ) (pkRoot : prims.Y) :
    htVerify prims hd msg sig pk adrs idxTree idxLeaf pkRoot =
      decide (xmssPkFromSig prims idxLeaf (HtSigCore.getSingleLayer hd sig) msg pk
        (htAdrs adrs idxTree) = pkRoot) := by
  unfold htVerify htVerifyM
  simp only [simulateQ_bind, simulateQ_pure]
  change decide
    (simulateQ (PublicHash.impl prims)
      (xmssPkFromSigM prims.core idxLeaf (HtSigCore.getSingleLayer hd sig) msg pk
        (htAdrs adrs idxTree)) = pkRoot) = _
  rw [simulateQ_xmssPkFromSigM]

/-! ### Deterministic interpretations -/

@[simp]
theorem simulateQ_htSignM_withPublicHash (core : CorePrimitives p) (hd : p.d = 1)
    (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    simulateQ answer
        (htSignM core hd msg sk pk adrs idxTree idxLeaf :
          OracleComp (publicHashSpec core) (HtSigCore p core)) =
      htSign (PublicHash.withPublicHash core answer) hd msg sk pk adrs idxTree idxLeaf := by
  simp [htSign, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_htRootM_withPublicHash (core : CorePrimitives p) (hd : p.d = 1)
    (answer : QueryImpl (publicHashSpec core) Id)
    (sk : core.SkSeed) (pk : core.PkSeed) (adrs : Adrs) (idxTree : ℕ) :
    simulateQ answer
        (htRootM core hd sk pk adrs idxTree : OracleComp (publicHashSpec core) core.Y) =
      htRoot (PublicHash.withPublicHash core answer) hd sk pk adrs idxTree := by
  simp [htRoot, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_htPkFromSigM_withPublicHash (core : CorePrimitives p) (hd : p.d = 1)
    (answer : QueryImpl (publicHashSpec core) Id)
    (msg : core.Y) (sig : HtSigCore p core) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) :
    simulateQ answer
        (htPkFromSigM core hd msg sig pk adrs idxTree idxLeaf :
          OracleComp (publicHashSpec core) core.Y) =
      htPkFromSig (PublicHash.withPublicHash core answer) hd msg sig pk adrs idxTree idxLeaf := by
  simp [htPkFromSig, PublicHash.impl_withPublicHash]

@[simp]
theorem simulateQ_htVerifyM_withPublicHash (core : CorePrimitives p) (hd : p.d = 1)
    (answer : QueryImpl (publicHashSpec core) Id) [DecidableEq core.Y]
    (msg : core.Y) (sig : HtSigCore p core) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) (pkRoot : core.Y) :
    simulateQ answer
        (htVerifyM core hd msg sig pk adrs idxTree idxLeaf pkRoot :
          OracleComp (publicHashSpec core) Bool) =
      htVerify (PublicHash.withPublicHash core answer) hd msg sig pk adrs idxTree idxLeaf
        pkRoot := by
  simp [htVerify, PublicHash.impl_withPublicHash]

/-! ### Correctness -/

/-- Hypertree correctness for `d = 1`: verification of an honest signature against the
key-generation root succeeds. -/
theorem htVerify_htSign (prims : Primitives p) (hd : p.d = 1) [DecidableEq prims.Y]
    (msg : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (adrs : Adrs) (idxTree idxLeaf : ℕ)
    (hidx : idxLeaf < 2 ^ p.hp) :
    htVerify prims hd msg (htSign prims hd msg sk pk adrs idxTree idxLeaf) pk adrs
        idxTree idxLeaf (htRoot prims hd sk pk adrs idxTree) = true := by
  rw [htVerify_eq_decide, htSign_eq_xmssSign, HtSigCore.getSingleLayer_singleLayer,
    htRoot_eq_xmssRoot,
    xmssPkFromSig_xmssSign prims msg sk pk (htAdrs adrs idxTree) idxLeaf hidx]
  simp

/-- Fixed-answer completeness of the canonical hypertree programs. Signing, recovery, and root
generation are interpreted by one shared deterministic public-hash answer function. This theorem
does not install a lazy random-oracle cache; that experiment-level interpretation is separate. -/
theorem simulateQ_htVerifyM_htSignM_withPublicHash (core : CorePrimitives p) (hd : p.d = 1)
    (answer : QueryImpl (publicHashSpec core) Id) [DecidableEq core.Y]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (adrs : Adrs) (idxTree idxLeaf : ℕ) (hidx : idxLeaf < 2 ^ p.hp) :
    simulateQ answer (do
      let sig ← htSignM core hd msg sk pk adrs idxTree idxLeaf
      let root ← htRootM core hd sk pk adrs idxTree
      htVerifyM core hd msg sig pk adrs idxTree idxLeaf root) = true := by
  simp only [simulateQ_bind, simulateQ_htSignM_withPublicHash core hd,
    simulateQ_htRootM_withPublicHash core hd, simulateQ_htVerifyM_withPublicHash core hd]
  exact htVerify_htSign (PublicHash.withPublicHash core answer) hd
    msg sk pk adrs idxTree idxLeaf hidx

end SLHDSA
