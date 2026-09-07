/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import HashSig.SLHDSA.HypertreeGeneral.QueryBound

/-!
# General-hypertree schedule canaries

These examples pin the two boundary depths at which Algorithm 12 is easiest to implement
incorrectly: the discarded recovery at `d = 1`, and the absence of a discarded recovery after the
top signature when `d = 2`.  A named FIPS 205 `d = 7` profile also fixes the multi-layer branch,
top address, output width, and closed query budget.
-/

public section

namespace SLHDSA.GeneralHypertreeTest

open GeneralHypertree

variable (vp : ValidatedParams) (core : CorePrimitives vp.params)
variable {m : Type → Type*} [Monad m] [LawfulMonad m]

/-- The signature width is intrinsic and cannot differ from the hypertree depth. -/
example (sig : Signature vp core) : sig.toArray.size = vp.params.d := sig.size_toArray

/-- The canonical one-layer signer still performs FIPS Algorithm 12's unconditional layer-zero
recovery, even though the recovered value does not affect the returned singleton signature. -/
example [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (pos : LayerPosition vp) (hremaining : pos.layer.val + 1 = vp.params.d) :
    signFromPositionM vp core sk pk true pos 1 hremaining msg = ((do
      let sig ← xmssSignM core msg sk pk pos.toAdrs pos.leaf.val
      let _ ← xmssPkFromSigM core pos.leaf.val sig msg pk pos.toAdrs
      return #v[sig]) : m (Vector (XmssSig vp.params core) 1)) := by
  simp [signFromPositionM, signFromPositionWith, xmssSignM, xmssPkFromSigM]

/-- With two layers, the first signature is recovered and signed by the top XMSS tree, while the
top signature is returned without a second discarded recovery. -/
example [HasQuery (publicHashSpec core) m]
    (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (pos : LayerPosition vp) (hremaining : pos.layer.val + 2 = vp.params.d) :
    signFromPositionM vp core sk pk false pos 2 hremaining msg = ((do
      let sig0 ← xmssSignM core msg sk pk pos.toAdrs pos.leaf.val
      let root0 ← xmssPkFromSigM core pos.leaf.val sig0 msg pk pos.toAdrs
      let next := pos.next (by omega)
      let sig1 ← xmssSignM core root0 sk pk next.toAdrs next.leaf.val
      return (#v[sig1]).insertIdx 0 sig0) : m (Vector (XmssSig vp.params core) 2)) := by
  simp [signFromPositionM, signFromPositionWith, xmssSignM, xmssPkFromSigM]

/-- General root generation always addresses layer `d - 1`, tree zero. -/
example (hash : Adrs → core.Y → m core.Y)
    (compress : Adrs → List core.Y → m core.Y)
    (nodeHash : Adrs → core.Y → core.Y → m core.Y)
    (sk : core.SkSeed) (pk : core.PkSeed) :
    rootWith vp core hash compress nodeHash sk pk =
      xmssRootWith core hash compress nodeHash sk pk
        (layerAdrs (vp.params.d - 1) 0) := by
  rfl

/-- The public arbitrary-depth correctness theorem has no depth side condition beyond validated
parameters. -/
example (prims : Primitives vp.params) (msg : prims.Y)
    (sk : prims.SkSeed) (pk : prims.PkSeed) (parts : DigestParts vp.params) :
    pkFromSig vp prims msg (sign vp prims msg sk pk parts) pk parts = root vp prims sk pk := by
  exact pkFromSig_sign vp prims msg sk pk parts

/-! ## Named FIPS multi-layer canaries -/

def sha2_128sVp : ValidatedParams :=
  FipsParameterSet.SLHDSA_SHA2_128s.validatedParams

/-- The named SHA2-128s profile takes the real multi-layer branch and returns seven XMSS
components in increasing layer order. -/
example (core : CorePrimitives sha2_128sVp.params) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] (msg : core.Y) (sk : core.SkSeed) (pk : core.PkSeed)
    (parts : DigestParts sha2_128sVp.params) :
    (signM sha2_128sVp core msg sk pk parts : m (HtSigCore sha2_128sVp.params core)) =
      signFromPositionM sha2_128sVp core sk pk false
        (LayerPosition.initial sha2_128sVp parts) 7 (by rfl) msg := by
  rfl

/-- The value FIPS 205 Algorithm 18 publishes as `PK.root` for SHA2-128s is the XMSS root at
layer six, tree zero. -/
example (core : CorePrimitives sha2_128sVp.params) {m : Type → Type*} [Monad m]
    [HasQuery (publicHashSpec core) m] (sk : core.SkSeed) (pk : core.PkSeed) :
    (rootM sha2_128sVp core sk pk : m core.Y) =
      xmssRootM core sk pk (layerAdrs 6 0) := by
  rfl

/-- The closed SHA2-128s signing budget contains six sign-and-recover cycles followed by one top
signature without a discarded recovery. -/
example : signQueryBound sha2_128sVp.params =
    6 * xmssCycleQueryBound sha2_128sVp.params + xmssSignQueryBound sha2_128sVp.params := by
  rfl

end SLHDSA.GeneralHypertreeTest
