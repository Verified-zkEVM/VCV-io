/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny
-/

module
public import HashSig.SLHDSA.Codec
public import HashSig.SLHDSA.Concrete.FIPS
public import HashSig.SLHDSA.Concrete.Instance
public import HashSig.SLHDSA.GeneralScheme

/-!
# FIPS 205 wire codecs for the approved concrete bundles

This module instantiates the strict structured wire codecs of `HashSig.SLHDSA.Codec` at the
concrete SHA2 and SHAKE primitive bundles of `HashSig.SLHDSA.Concrete.FIPS`. Every carrier of
both families is definitionally `Bytes p.n`, so each atomic codec is the identity byte codec,
and that identity is a stated theorem on all four carriers rather than an unexamined
definitional accident: a permuted or otherwise noncanonical atomic codec cannot satisfy the
`*_equiv` lemmas below.

`approvedWireCodec` dispatches the pinned family codec for each of the twelve approved
parameter sets, and `encodeApprovedSignature` / `decodeApprovedSignature` (with the analogous
key surfaces) expose the FIPS 205 byte boundary of the actual approved bundles: the bytes they
produce are, by the layout theorems of `HashSig.SLHDSA.Codec`, the normative
`R || SIG_FORS || SIG_HT` wire of a real SLH-DSA signature over `approvedPrimitives`.

## References

- NIST FIPS 205, Section 9.2, Figures 16 and 17, Algorithms 18--22
-/

@[expose] public section

namespace SLHDSA.Concrete

open SLHDSA

/-! ## Pinned atomic codecs for the concrete families -/

/-- The atomic wire codec of the SHA2 bundle: every carrier of `sha2Primitives` is
definitionally `Bytes p.n`, and each field is the identity byte codec. -/
def sha2WireCodec (p : Params) : CoreWireCodec p (sha2Primitives p).core where
  pkSeed := WireCodec.bytes p.n
  skSeed := WireCodec.bytes p.n
  skPrf := WireCodec.bytes p.n
  y := WireCodec.bytes p.n
  y_toBytes := fun _ => rfl

/-- The atomic wire codec of the SHAKE256 bundle: every carrier of `shakePrimitives` is
definitionally `Bytes p.n`, and each field is the identity byte codec. -/
def shakeWireCodec (p : Params) : CoreWireCodec p (shakePrimitives p).core where
  pkSeed := WireCodec.bytes p.n
  skSeed := WireCodec.bytes p.n
  skPrf := WireCodec.bytes p.n
  y := WireCodec.bytes p.n
  y_toBytes := fun _ => rfl

/-! ## Seed-carrier coherence

The `CoreWireCodec` structure imposes byte coherence (`y_toBytes`) only on the node carrier
`Y`. On the pinned concrete instances the three seed carriers are byte vectors as well, and
the lemmas below state that each codec serializes a seed as exactly its own bytes. -/

/-- The pinned SHA2 codec serializes `PK.seed` as exactly its own bytes. -/
@[simp] theorem sha2WireCodec_pkSeed_equiv (p : Params) (seed : Bytes p.n) :
    (sha2WireCodec p).pkSeed.equiv seed = seed := rfl

/-- The pinned SHA2 codec serializes `SK.seed` as exactly its own bytes. -/
@[simp] theorem sha2WireCodec_skSeed_equiv (p : Params) (seed : Bytes p.n) :
    (sha2WireCodec p).skSeed.equiv seed = seed := rfl

/-- The pinned SHA2 codec serializes `SK.prf` as exactly its own bytes. -/
@[simp] theorem sha2WireCodec_skPrf_equiv (p : Params) (seed : Bytes p.n) :
    (sha2WireCodec p).skPrf.equiv seed = seed := rfl

/-- The pinned SHA2 codec serializes a node as exactly its own bytes. -/
@[simp] theorem sha2WireCodec_y_equiv (p : Params) (value : Bytes p.n) :
    (sha2WireCodec p).y.equiv value = value := rfl

/-- The pinned SHAKE codec serializes `PK.seed` as exactly its own bytes. -/
@[simp] theorem shakeWireCodec_pkSeed_equiv (p : Params) (seed : Bytes p.n) :
    (shakeWireCodec p).pkSeed.equiv seed = seed := rfl

/-- The pinned SHAKE codec serializes `SK.seed` as exactly its own bytes. -/
@[simp] theorem shakeWireCodec_skSeed_equiv (p : Params) (seed : Bytes p.n) :
    (shakeWireCodec p).skSeed.equiv seed = seed := rfl

/-- The pinned SHAKE codec serializes `SK.prf` as exactly its own bytes. -/
@[simp] theorem shakeWireCodec_skPrf_equiv (p : Params) (seed : Bytes p.n) :
    (shakeWireCodec p).skPrf.equiv seed = seed := rfl

/-- The pinned SHAKE codec serializes a node as exactly its own bytes. -/
@[simp] theorem shakeWireCodec_y_equiv (p : Params) (value : Bytes p.n) :
    (shakeWireCodec p).y.equiv value = value := rfl

/-! ## The approved dispatch -/

/-- The atomic wire codec of the exact FIPS primitive bundle selected by
`approvedPrimitives`, dispatching the pinned family codec per approved parameter set. -/
def approvedWireCodec :
    (set : FipsParameterSet) → CoreWireCodec set.params (approvedPrimitives set).core
  | .SLHDSA_SHA2_128s | .SLHDSA_SHA2_128f | .SLHDSA_SHA2_192s | .SLHDSA_SHA2_192f
  | .SLHDSA_SHA2_256s | .SLHDSA_SHA2_256f => sha2WireCodec _
  | .SLHDSA_SHAKE_128s | .SLHDSA_SHAKE_128f | .SLHDSA_SHAKE_192s | .SLHDSA_SHAKE_192f
  | .SLHDSA_SHAKE_256s | .SLHDSA_SHAKE_256f => shakeWireCodec _

/-- On every SHA2 parameter set, the approved dispatch is the pinned SHA2 codec. The equation
is heterogeneous because the carrier index reduces only after case analysis on the set. -/
theorem approvedWireCodec_sha2 (set : FipsParameterSet) (h : set.hashFamily = .sha2) :
    HEq (approvedWireCodec set) (sha2WireCodec set.params) := by
  cases set <;> first | rfl | exact absurd h (by decide)

/-- On every SHAKE parameter set, the approved dispatch is the pinned SHAKE codec. The
equation is heterogeneous because the carrier index reduces only after case analysis. -/
theorem approvedWireCodec_shake (set : FipsParameterSet) (h : set.hashFamily = .shake) :
    HEq (approvedWireCodec set) (shakeWireCodec set.params) := by
  cases set <;> first | rfl | exact absurd h (by decide)

/-- On every approved bundle, the node codec serializes a node as exactly the bytes the hash
pipeline consumes through `CorePrimitives.yToBytes`. -/
theorem approvedWireCodec_y_equiv (set : FipsParameterSet)
    (value : (approvedPrimitives set).core.Y) :
    (approvedWireCodec set).y.equiv value = (approvedPrimitives set).core.yToBytes value :=
  (approvedWireCodec set).y_toBytes value

/-! ## Approved byte surfaces

Checked encode/decode entry points for keys and signatures of the actual approved bundles.
The bytes below are the FIPS 205 wire encodings of real SLH-DSA values: the layout theorems
of `HashSig.SLHDSA.Codec` pin every component offset of these encoders. -/

/-- Encode a public key of the approved bundle as its FIPS `PK.seed || PK.root` wire. -/
def encodeApprovedPublicKey (set : FipsParameterSet)
    (key : PublicKeyCore (approvedPrimitives set).core) : List Byte :=
  encodePublicKey (approvedWireCodec set) key

/-- Decode an approved-bundle public key, rejecting every length other than `2n`. -/
def decodeApprovedPublicKey (set : FipsParameterSet) (raw : List Byte) :
    Except CodecError (PublicKeyCore (approvedPrimitives set).core) :=
  decodePublicKey (approvedWireCodec set) raw

/-- Encode a secret key of the approved bundle as its FIPS
`SK.seed || SK.prf || PK.seed || PK.root` wire. -/
def encodeApprovedSecretKey (set : FipsParameterSet)
    (key : SecretKeyCore (approvedPrimitives set).core) : List Byte :=
  encodeSecretKey (approvedWireCodec set) key

/-- Decode an approved-bundle secret key, rejecting every length other than `4n`. -/
def decodeApprovedSecretKey (set : FipsParameterSet) (raw : List Byte) :
    Except CodecError (SecretKeyCore (approvedPrimitives set).core) :=
  decodeSecretKey (approvedWireCodec set) raw

/-- Encode a signature of the approved bundle as its FIPS `R || SIG_FORS || SIG_HT` wire.
This is the exported byte boundary for signatures produced by the general scheme over
`approvedPrimitives`. -/
def encodeApprovedSignature (set : FipsParameterSet)
    (signature :
      GeneralScheme.SignatureCore set.validatedParams (approvedPrimitives set).core) :
    List Byte :=
  encodeSignature set.validatedParams (approvedWireCodec set) signature

/-- Decode an approved-bundle signature, rejecting short, long, or partially consumed
input. -/
def decodeApprovedSignature (set : FipsParameterSet) (raw : List Byte) :
    Except CodecError
      (GeneralScheme.SignatureCore set.validatedParams (approvedPrimitives set).core) :=
  SLHDSA.decodeSignature set.validatedParams (approvedWireCodec set) raw

/-- The approved public-key wire always has exactly the FIPS width `2n`. -/
@[simp] theorem encodeApprovedPublicKey_length (set : FipsParameterSet)
    (key : PublicKeyCore (approvedPrimitives set).core) :
    (encodeApprovedPublicKey set key).length = set.params.publicKeyBytes :=
  encodePublicKey_length (approvedWireCodec set) key

/-- The approved secret-key wire always has exactly the FIPS width `4n`. -/
@[simp] theorem encodeApprovedSecretKey_length (set : FipsParameterSet)
    (key : SecretKeyCore (approvedPrimitives set).core) :
    (encodeApprovedSecretKey set key).length = set.params.secretKeyBytes :=
  encodeSecretKey_length (approvedWireCodec set) key

/-- The approved signature wire always has exactly the FIPS Table 2 signature width. -/
@[simp] theorem encodeApprovedSignature_length (set : FipsParameterSet)
    (signature :
      GeneralScheme.SignatureCore set.validatedParams (approvedPrimitives set).core) :
    (encodeApprovedSignature set signature).length = set.params.signatureBytes :=
  encodeSignature_length set.validatedParams (approvedWireCodec set) signature

/-- Decoding the approved public-key wire recovers exactly the encoded key. -/
@[simp] theorem decodeApprovedPublicKey_encode (set : FipsParameterSet)
    (key : PublicKeyCore (approvedPrimitives set).core) :
    decodeApprovedPublicKey set (encodeApprovedPublicKey set key) = .ok key :=
  decodePublicKey_encode (approvedWireCodec set) key

/-- Decoding the approved secret-key wire recovers exactly the encoded key. -/
@[simp] theorem decodeApprovedSecretKey_encode (set : FipsParameterSet)
    (key : SecretKeyCore (approvedPrimitives set).core) :
    decodeApprovedSecretKey set (encodeApprovedSecretKey set key) = .ok key :=
  decodeSecretKey_encode (approvedWireCodec set) key

/-- Decoding the approved signature wire recovers exactly the encoded signature. -/
@[simp] theorem decodeApprovedSignature_encode (set : FipsParameterSet)
    (signature :
      GeneralScheme.SignatureCore set.validatedParams (approvedPrimitives set).core) :
    decodeApprovedSignature set (encodeApprovedSignature set signature) = .ok signature :=
  SLHDSA.decodeSignature_encode set.validatedParams (approvedWireCodec set) signature

/-! ## Agreement with the legacy SLH-DSA-SHA2-128-24 decoder

`SLHDSA.Concrete.decodeSignature` (`HashSig.SLHDSA.Concrete.Instance`) predates the strict
codec: it reads the 3856-byte SLH-DSA-SHA2-128-24 wire at hard-coded offsets, without a width
check. The theorems below reconcile the two byte boundaries: on every canonical wire — in
particular on every input the strict checked decoder accepts — the legacy decoder produces
exactly the same structured signature, so main hosts one FIPS byte layout, stated once. -/

/-- The validated SLH-DSA-SHA2-128-24 parameter bundle, with a reducible `params` projection so
codec statements over `sha128_24Vp.params` unify with the concrete bundle's `slhdsaSha2_128_24`
index at every transparency level. -/
@[reducible] def sha128_24Vp : ValidatedParams :=
  ⟨slhdsaSha2_128_24, LimitedParameterSet.params_valid .SLHDSA_SHA2_128_24⟩

/-- The atomic wire codec of the concrete SLH-DSA-SHA2-128-24 bundle: every carrier of
`shaPrimitives` is definitionally `Bytes 16`, and each field is the identity byte codec. -/
def shaWireCodec : CoreWireCodec slhdsaSha2_128_24 shaPrimitives.core where
  pkSeed := WireCodec.bytes 16
  skSeed := WireCodec.bytes 16
  skPrf := WireCodec.bytes 16
  y := WireCodec.bytes 16
  y_toBytes := fun _ => rfl

/-- The pinned SHA2-128-24 codec serializes `PK.seed` as exactly its own bytes. -/
@[simp] theorem shaWireCodec_pkSeed_equiv (seed : Bytes 16) :
    shaWireCodec.pkSeed.equiv seed = seed := rfl

/-- The pinned SHA2-128-24 codec serializes `SK.seed` as exactly its own bytes. -/
@[simp] theorem shaWireCodec_skSeed_equiv (seed : Bytes 16) :
    shaWireCodec.skSeed.equiv seed = seed := rfl

/-- The pinned SHA2-128-24 codec serializes `SK.prf` as exactly its own bytes. -/
@[simp] theorem shaWireCodec_skPrf_equiv (seed : Bytes 16) :
    shaWireCodec.skPrf.equiv seed = seed := rfl

/-- The pinned SHA2-128-24 codec serializes a node as exactly its own bytes. -/
@[simp] theorem shaWireCodec_y_equiv (value : Bytes 16) :
    shaWireCodec.y.equiv value = value := rfl

/-- Reading 16 bytes at `off'` from a canonical wire recovers the component whose strict slice
sits at the equal offset `off`. -/
private theorem baSliceToB16_of_slice {raw : List Byte} {v : Bytes 16} {off : ℕ} (off' : ℕ)
    (hoff : off' = off) (hslice : (raw.drop off).take 16 = WireCodec.encode shaWireCodec.y v)
    (hfit : off' + 16 ≤ raw.length) :
    baSliceToB16 (ByteArray.mk raw.toArray) off' = v := by
  subst hoff
  have hslice' : (raw.drop off').take 16 = v.toList := hslice
  apply Vector.ext
  intro i hi
  have hidx : off' + i < raw.length := by omega
  have htake : i < ((raw.drop off').take 16).length := by
    simp only [List.length_take, List.length_drop]
    omega
  have hv : v[i] = raw[off' + i]'hidx := by
    have h := (List.getElem_of_eq hslice' htake).symm
    simpa using h
  simp only [baSliceToB16, Vector.getElem_ofFn]
  have hsize : off' + i < (ByteArray.mk raw.toArray).size := by
    simpa [ByteArray.size] using hidx
  rw [getElem!_pos (ByteArray.mk raw.toArray) (off' + i) hsize]
  exact ((show (ByteArray.mk raw.toArray)[off' + i]'hsize = raw[off' + i]'hidx from rfl)).trans
    hv.symm

private theorem forsTreeExt {x y : ForsTreeSigCore slhdsaSha2_128_24 shaPrimitives.core}
    (h1 : x.sk = y.sk) (h2 : x.auth = y.auth) : x = y := by
  cases x
  cases y
  simp only [ForsTreeSigCore.mk.injEq]
  exact ⟨h1, h2⟩

private theorem xmssExt {x y : XmssSigCore slhdsaSha2_128_24 shaPrimitives.core}
    (h1 : x.wots = y.wots) (h2 : x.auth = y.auth) : x = y := by
  cases x
  cases y
  simp only [XmssSigCore.mk.injEq]
  exact ⟨h1, h2⟩

private theorem forsSecret_off (i : ℕ) :
    16 + i * 400 = WireLayout.forsSecretOffset slhdsaSha2_128_24 i := by
  change 16 + i * 400 = 16 + i * ((1 + 24) * 16)
  ring

private theorem forsAuth_off (i j : ℕ) :
    16 + i * 400 + 16 + j * 16 = WireLayout.forsAuthOffset slhdsaSha2_128_24 i j := by
  change 16 + i * 400 + 16 + j * 16 = 16 + i * ((1 + 24) * 16) + (1 + j) * 16
  ring

private theorem wots_off (c : ℕ) :
    2416 + c * 16 = WireLayout.wotsOffset slhdsaSha2_128_24 0 c := by
  change 2416 + c * 16 = 16 + 6 * ((1 + 24) * 16) + 0 * ((68 + 22) * 16) + c * 16
  ring

private theorem xmssAuth_off (j : ℕ) :
    2416 + 1088 + j * 16 = WireLayout.xmssAuthOffset slhdsaSha2_128_24 0 j := by
  change 2416 + 1088 + j * 16
      = 16 + 6 * ((1 + 24) * 16) + 0 * ((68 + 22) * 16) + (68 + j) * 16
  ring

/-- **Strict-encode / legacy-decode identity.** Decoding a canonical strict SLH-DSA-SHA2-128-24
signature wire with the legacy fixed-offset decoder recovers exactly the encoded signature, so
the legacy byte layout agrees with the strict FIPS codec on every well-formed wire. -/
theorem decodeSignature_encodeSignature
    (sig : SignatureCore slhdsaSha2_128_24 shaPrimitives.core) :
    Concrete.decodeSignature
      (ByteArray.mk (SLHDSA.encodeSignature sha128_24Vp shaWireCodec sig).toArray) = sig := by
  have hlen : (SLHDSA.encodeSignature sha128_24Vp shaWireCodec sig).length = 3856 :=
    SLHDSA.encodeSignature_length sha128_24Vp shaWireCodec sig
  unfold Concrete.decodeSignature
  conv_rhs => rw [show sig = (⟨sig.randomness, sig.fors, sig.hypertree⟩ :
    SignatureCore slhdsaSha2_128_24 shaPrimitives.core) from rfl]
  simp only []
  congr 1
  · exact baSliceToB16_of_slice 0 rfl
      (SLHDSA.encodeSignature_randomness_slice sha128_24Vp shaWireCodec sig) (by omega)
  · apply Vector.ext
    intro i hi
    have hi6 : i < 6 := hi
    refine (Vector.getElem_ofFn hi6).trans ?_
    refine forsTreeExt ?_ ?_
    · exact baSliceToB16_of_slice _ (forsSecret_off i)
        (SLHDSA.encodeSignature_forsSecret_slice sha128_24Vp shaWireCodec sig ⟨i, hi6⟩)
        (by omega)
    · apply Vector.ext
      intro j hj
      have hj24 : j < 24 := hj
      refine (Vector.getElem_ofFn hj24).trans ?_
      exact baSliceToB16_of_slice _ (forsAuth_off i j)
        (SLHDSA.encodeSignature_forsAuth_slice sha128_24Vp shaWireCodec sig ⟨i, hi6⟩
          ⟨j, hj24⟩)
        (by omega)
  · refine Eq.trans (congrArg (HtSigCore.singleLayer shaParams_d_eq_one) (xmssExt ?_ ?_))
      (HtSigCore.singleLayer_getSingleLayer shaParams_d_eq_one sig.hypertree)
    · apply Vector.ext
      intro c hc
      have hc68 : c < 68 := hc
      refine (Vector.getElem_ofFn hc68).trans ?_
      exact baSliceToB16_of_slice _ (wots_off c)
        (SLHDSA.encodeSignature_wots_slice sha128_24Vp shaWireCodec sig ⟨0, by decide⟩
          ⟨c, hc68⟩)
        (by omega)
    · apply Vector.ext
      intro j hj
      have hj22 : j < 22 := hj
      refine (Vector.getElem_ofFn hj22).trans ?_
      exact baSliceToB16_of_slice _ (xmssAuth_off j)
        (SLHDSA.encodeSignature_xmssAuth_slice sha128_24Vp shaWireCodec sig ⟨0, by decide⟩
          ⟨j, hj22⟩)
        (by omega)

/-- Whenever the strict checked decoder accepts a byte string, the legacy fixed-offset
SLH-DSA-SHA2-128-24 decoder produces exactly the same structured signature. -/
theorem decodeSignature_eq_of_strict_ok {raw : List Byte}
    {sig : SignatureCore slhdsaSha2_128_24 shaPrimitives.core}
    (h : SLHDSA.decodeSignature sha128_24Vp shaWireCodec raw = .ok sig) :
    Concrete.decodeSignature (ByteArray.mk raw.toArray) = sig := by
  rw [(SLHDSA.decodeSignature_eq_ok_iff sha128_24Vp shaWireCodec raw sig).mp h]
  exact decodeSignature_encodeSignature sig

end SLHDSA.Concrete
