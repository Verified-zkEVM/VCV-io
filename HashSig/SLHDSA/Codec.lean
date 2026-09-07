/-
Copyright (c) 2026 Nicolas Consigny. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Consigny, Quang Dao
-/

module
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Prod
public import HashSig.SLHDSA.Encoding
public import HashSig.SLHDSA.FipsParams
public import HashSig.SLHDSA.Scheme

/-!
# Strict structured SLH-DSA wire codecs

This module owns the FIPS 205 byte boundary for the canonical structured public keys, secret
keys, and signatures. An abstract primitive context supplies bijections between each atomic
carrier and exactly `n` bytes. The codecs compose those bijections in the normative order

`PK.seed || PK.root`,
`SK.seed || SK.prf || PK.seed || PK.root`, and
`R || k * (FORS.sk || FORS.auth[a]) || d * (WOTS[len] || XMSS.auth[h'])`.

Malformed input is rejected once, at the exact total width, before the resulting intrinsically
shaped value reaches the proof-level algorithms. No unchecked indexing or default padding is
used by the decoder.

## References

- NIST FIPS 205, Figures 15–17
- NIST FIPS 205, Algorithms 18--20
-/

@[expose] public section

namespace SLHDSA

/-! ## Compositional exact-width codecs -/

/-- A bijection between a semantic value and exactly `width` bytes. -/
structure WireCodec (α : Type) (width : ℕ) where
  /-- The canonical fixed-width byte representation. -/
  equiv : α ≃ Bytes width

namespace WireCodec

/-- Array-backed vectors are equivalent to functions on their intrinsic finite index. -/
def vectorEquivFin (α : Type) (n : ℕ) : Vector α n ≃ (Fin n → α) where
  toFun := fun xs i => xs[i.val]
  invFun := fun f => Vector.ofFn f
  left_inv := by intro xs; exact Vector.ofFn_getElem
  right_inv := by intro f; funext i; simp

/-- Concatenation is a bijection between two fixed-width byte strings and their combined wire. -/
def appendBytesEquiv (m n : ℕ) : Bytes m × Bytes n ≃ Bytes (m + n) :=
  (Equiv.prodCongr (vectorEquivFin Byte m) (vectorEquivFin Byte n)).trans
    ((Fin.appendEquiv m n).trans (vectorEquivFin Byte (m + n)).symm)

/-- Reinterpret a fixed-width byte string across a proved equality of widths. -/
def castBytesEquiv {m n : ℕ} (h : m = n) : Bytes m ≃ Bytes n where
  toFun := Vector.cast h
  invFun := Vector.cast h.symm
  left_inv := by subst h; intro bytes; rfl
  right_inv := by subst h; intro bytes; rfl

/-- Split a nonempty vector into its first element and remaining elements. -/
def headTailEquiv (α : Type) (count : ℕ) : Vector α (count + 1) ≃ α × Vector α count where
  toFun values := (values[0], Vector.ofFn fun i => values[i.val + 1])
  invFun fields := Vector.ofFn fun i =>
    if h : i.val = 0 then fields.1 else fields.2[i.val - 1]'(by omega)
  left_inv := by
    intro values
    apply Vector.ext
    intro i hi
    by_cases h : i = 0
    · subst i
      simp
    · have hi_pos : 0 < i := Nat.pos_of_ne_zero h
      have hidx : i - 1 + 1 = i := Nat.sub_add_cancel hi_pos
      simp [h, hidx]
  right_inv := by
    intro fields
    apply Prod.ext
    · simp
    · apply Vector.ext
      intro i hi
      simp

/-- Flatten canonically encoded elements recursively in increasing vector-index order.
The recursion ensures that encoding computes each component once, instead of reconstructing an
entire component for every output byte. -/
def repeatBytesEquiv {α : Type} {width : ℕ} (element : α ≃ Bytes width) :
    (count : ℕ) → Vector α count ≃ Bytes (count * width)
  | 0 =>
      { toFun := fun _ => (#v[] : Bytes 0).cast (by simp)
        invFun := fun _ => (Vector.ofFn Fin.elim0 : Vector α 0)
        left_inv := by intro values; apply Vector.ext; omega
        right_inv := by intro bytes; apply Vector.ext; omega }
  | count + 1 =>
      (headTailEquiv α count).trans <|
        (Equiv.prodCongr element (repeatBytesEquiv element count)).trans <|
          (appendBytesEquiv width (count * width)).trans <|
            castBytesEquiv (by ring)

/-- The identity codec for a byte carrier already known to have the required width. -/
def bytes (width : ℕ) : WireCodec (Bytes width) width := ⟨Equiv.refl _⟩

/-- Transport the semantic side of a codec through an equivalence. -/
def precompose {α β : Type} {width : ℕ} (e : α ≃ β) (codec : WireCodec β width) :
    WireCodec α width :=
  ⟨e.trans codec.equiv⟩

/-- Concatenate two canonical codecs. -/
def product {α β : Type} {leftWidth rightWidth : ℕ}
    (left : WireCodec α leftWidth) (right : WireCodec β rightWidth) :
    WireCodec (α × β) (leftWidth + rightWidth) :=
  ⟨(Equiv.prodCongr left.equiv right.equiv).trans
    (appendBytesEquiv leftWidth rightWidth)⟩

/-- Flatten a fixed-size vector of canonically encoded elements. -/
def vector {α : Type} {width : ℕ} (element : WireCodec α width) (count : ℕ) :
    WireCodec (Vector α count) (count * width) :=
  ⟨repeatBytesEquiv element.equiv count⟩

/-- Transport the wire side of a codec through a proved equality of widths. -/
def castWidth {α : Type} {m n : ℕ} (codec : WireCodec α m) (h : m = n) :
    WireCodec α n :=
  ⟨codec.equiv.trans (castBytesEquiv h)⟩

/-- Encode a value to its canonical byte list. -/
def encode {α : Type} {width : ℕ} (codec : WireCodec α width) (value : α) : List Byte :=
  (codec.equiv value).toList

/-- Reject a non-exact input, then decode all bytes into the semantic value. -/
def decode {α : Type} {width : ℕ} (codec : WireCodec α width) (raw : List Byte) :
    Except CodecError α :=
  (decodeExact width raw).map codec.equiv.symm

@[simp] theorem decode_encode {α : Type} {width : ℕ} (codec : WireCodec α width)
    (value : α) : codec.decode (codec.encode value) = .ok value := by
  unfold decode encode
  change Except.map _ (decodeExact width (encodeExact (codec.equiv value))) = _
  rw [decodeExact_encode]
  exact congrArg Except.ok (codec.equiv.symm_apply_apply value)

@[simp] theorem encode_length {α : Type} {width : ℕ} (codec : WireCodec α width)
    (value : α) : (codec.encode value).length = width := by
  simp [encode]

/-- Canonical encodings are injective. -/
theorem encode_injective {α : Type} {width : ℕ} (codec : WireCodec α width) :
    Function.Injective codec.encode := by
  intro left right h
  apply codec.equiv.injective
  apply Vector.toList_inj.mp
  exact h

/-- Every non-exact input is rejected before the semantic equivalence is applied. -/
theorem decode_eq_error_of_length_ne {α : Type} {width : ℕ} (codec : WireCodec α width)
    (raw : List Byte) (h : raw.length ≠ width) :
    codec.decode raw = .error (.invalidLength width raw.length) := by
  rw [decode, decodeExact_eq_error_of_length_ne width raw h]
  rfl

/-- Decoder success is exactly canonical full consumption of the supplied input. -/
theorem decode_eq_ok_iff {α : Type} {width : ℕ} (codec : WireCodec α width)
    (raw : List Byte) (value : α) :
    codec.decode raw = .ok value ↔ raw = codec.encode value := by
  constructor
  · intro h
    unfold decode at h
    cases hbytes : decodeExact width raw with
    | error error =>
        rw [hbytes] at h
        cases h
    | ok bytes =>
        simp only [hbytes, Except.map, Except.ok.injEq] at h
        rw [decodeExact_eq_ok_iff] at hbytes
        rw [hbytes, ← h]
        simp [encode]
  · intro h
    subst raw
    exact decode_encode codec value

/-! ### Encoding normal forms

These lemmas expose the exact byte order every combinator emits, so the structured codecs
below can be pinned to the explicit FIPS 205 offsets of `WireLayout`.
-/

/-- Concatenating two exact-width byte strings appends their byte lists in order. -/
theorem toList_appendBytesEquiv {m n : ℕ} (left : Bytes m) (right : Bytes n) :
    (appendBytesEquiv m n (left, right)).toList = left.toList ++ right.toList := by
  change (Vector.ofFn (Fin.append (fun i => left[i.val]) fun i => right[i.val])).toList = _
  rw [Vector.toList_ofFn, List.ofFn_fin_append]
  conv_rhs => rw [← Vector.ofFn_getElem (xs := left), ← Vector.ofFn_getElem (xs := right),
    Vector.toList_ofFn, Vector.toList_ofFn]

/-- Width casts reinterpret the length index and leave the underlying bytes unchanged. -/
theorem toList_castBytesEquiv {m n : ℕ} (h : m = n) (bytes : Bytes m) :
    (castBytesEquiv h bytes).toList = bytes.toList := rfl

/-- Flattening exact-width encodings emits each element's bytes in increasing index order. -/
theorem toList_repeatBytesEquiv {α : Type} {width : ℕ} (element : α ≃ Bytes width) :
    ∀ (count : ℕ) (values : Vector α count),
      (repeatBytesEquiv element count values).toList
        = (List.ofFn fun i : Fin count => (element values[i.val]).toList).flatten
  | 0, _ => by simp [repeatBytesEquiv]
  | count + 1, values => by
      change (castBytesEquiv (by ring : width + count * width = (count + 1) * width)
        (appendBytesEquiv width (count * width)
          (element values[0], repeatBytesEquiv element count
            (Vector.ofFn fun i => values[i.val + 1])))).toList = _
      rw [toList_castBytesEquiv, toList_appendBytesEquiv,
        toList_repeatBytesEquiv element count, List.ofFn_succ, List.flatten_cons]
      congr 1
      refine congrArg List.flatten (congrArg List.ofFn (funext fun i => ?_))
      simp

/-- Transporting the semantic side of a codec encodes the transported value. -/
@[simp] theorem encode_precompose {α β : Type} {width : ℕ} (e : α ≃ β)
    (codec : WireCodec β width) (value : α) :
    (precompose e codec).encode value = codec.encode (e value) := rfl

/-- Width casts do not change the encoded byte list. -/
@[simp] theorem encode_castWidth {α : Type} {m n : ℕ} (codec : WireCodec α m) (h : m = n)
    (value : α) : (castWidth codec h).encode value = codec.encode value :=
  toList_castBytesEquiv h (codec.equiv value)

/-- A product codec emits the left field's bytes, then the right field's bytes. -/
@[simp] theorem encode_product {α β : Type} {leftWidth rightWidth : ℕ}
    (left : WireCodec α leftWidth) (right : WireCodec β rightWidth) (a : α) (b : β) :
    (product left right).encode (a, b) = left.encode a ++ right.encode b :=
  toList_appendBytesEquiv (left.equiv a) (right.equiv b)

/-- A vector codec emits each element's bytes in increasing index order. -/
@[simp] theorem encode_vector {α : Type} {width : ℕ} (element : WireCodec α width)
    (count : ℕ) (values : Vector α count) :
    (vector element count).encode values
      = (List.ofFn fun i : Fin count => element.encode values[i.val]).flatten :=
  toList_repeatBytesEquiv element.equiv count values

end WireCodec

/-! ## Atomic primitive-carrier boundary -/

/-- Exact `n`-byte codecs for every carrier that appears in an SLH-DSA key or signature.
Concrete SHA2 and SHAKE suites instantiate this structure with byte-vector identity codecs. -/
structure CoreWireCodec (p : Params) (core : CorePrimitives p) where
  /-- Codec for `PK.seed`. -/
  pkSeed : WireCodec core.PkSeed p.n
  /-- Codec for `SK.seed`. -/
  skSeed : WireCodec core.SkSeed p.n
  /-- Codec for `SK.prf`. -/
  skPrf : WireCodec core.SkPrf p.n
  /-- Codec for randomizers, WOTS values, FORS values, and tree nodes. -/
  y : WireCodec core.Y p.n
  /-- The node codec agrees with the scheme's own byte view of `Y`: a node's wire bytes are
  exactly the bytes the hash pipeline consumes through `CorePrimitives.yToBytes`. Without this
  coherence a permuted node codec would satisfy every structural round-trip theorem while
  serializing signatures whose bytes disagree with what verification hashes. -/
  y_toBytes : ∀ value : core.Y, y.equiv value = core.yToBytes value

/-! ## FIPS component widths and offsets -/

namespace WireLayout

/-- One FORS tree signature contains one secret node and `a` authentication nodes. -/
def forsTreeBytes (p : Params) : ℕ := (1 + p.a) * p.n

/-- The complete FORS signature contains exactly `k` tree signatures. -/
def forsBytes (p : Params) : ℕ := p.k * forsTreeBytes p

/-- One hypertree layer contains `len` WOTS values and `h'` authentication nodes. -/
def xmssBytes (p : Params) : ℕ := (p.len + p.hp) * p.n

/-- The complete hypertree signature contains exactly `d` XMSS signatures. -/
def hypertreeBytes (p : Params) : ℕ := p.d * xmssBytes p

/-- Byte offset of the message randomizer `R`. -/
def randomnessOffset (_p : Params) : ℕ := 0

/-- Byte offset of the complete FORS signature. -/
def forsOffset (p : Params) : ℕ := p.n

/-- Byte offset of FORS tree signature `tree`. -/
def forsTreeOffset (p : Params) (tree : ℕ) : ℕ := forsOffset p + tree * forsTreeBytes p

/-- Byte offset of the revealed secret in FORS tree `tree`. -/
def forsSecretOffset (p : Params) (tree : ℕ) : ℕ := forsTreeOffset p tree

/-- Byte offset of authentication node `node` in FORS tree `tree`. -/
def forsAuthOffset (p : Params) (tree node : ℕ) : ℕ :=
  forsTreeOffset p tree + (1 + node) * p.n

/-- Byte offset of the complete hypertree signature. -/
def hypertreeOffset (p : Params) : ℕ := forsOffset p + forsBytes p

/-- Byte offset of XMSS signature `layer`. -/
def xmssOffset (p : Params) (layer : ℕ) : ℕ :=
  hypertreeOffset p + layer * xmssBytes p

/-- Byte offset of WOTS chain value `chain` at hypertree `layer`. -/
def wotsOffset (p : Params) (layer chain : ℕ) : ℕ :=
  xmssOffset p layer + chain * p.n

/-- Byte offset of authentication node `node` at hypertree `layer`. -/
def xmssAuthOffset (p : Params) (layer node : ℕ) : ℕ :=
  xmssOffset p layer + (p.len + node) * p.n

/-- For valid parameters, the structured component widths cover exactly the FIPS signature. -/
theorem total_eq_signatureBytes (vp : ValidatedParams) :
    vp.params.n + (forsBytes vp.params + hypertreeBytes vp.params) =
      vp.params.signatureBytes := by
  simp only [Params.signatureBytes, forsBytes, forsTreeBytes, hypertreeBytes, xmssBytes]
  rw [show vp.params.h = vp.params.d * vp.params.hp from vp.valid.h_eq_layers]
  ring

end WireLayout

/-! ## Structured key and signature codecs -/

def publicKeyFieldsEquiv {p : Params} {core : CorePrimitives p} :
    PublicKeyCore core ≃ core.PkSeed × core.Y where
  toFun key := (key.pkSeed, key.pkRoot)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv := by intro key; cases key; rfl
  right_inv := by intro fields; cases fields; rfl

def secretKeyFieldsEquiv {p : Params} {core : CorePrimitives p} :
    SecretKeyCore core ≃ core.SkSeed × (core.SkPrf × (core.PkSeed × core.Y)) where
  toFun key := (key.skSeed, key.skPrf, key.pkSeed, key.pkRoot)
  invFun fields := ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩
  left_inv := by intro key; cases key; rfl
  right_inv := by intro fields; rcases fields with ⟨_, _, _, _⟩; rfl

def forsTreeFieldsEquiv {p : Params} {core : CorePrimitives p} :
    ForsTreeSigCore p core ≃ core.Y × Vector core.Y p.a where
  toFun signature := (signature.sk, signature.auth)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv := by intro signature; cases signature; rfl
  right_inv := by intro fields; cases fields; rfl

def xmssFieldsEquiv {p : Params} {core : CorePrimitives p} :
    XmssSigCore p core ≃ Vector core.Y p.len × Vector core.Y p.hp where
  toFun signature := (signature.wots, signature.auth)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv := by intro signature; cases signature; rfl
  right_inv := by intro fields; cases fields; rfl

def signatureFieldsEquiv {p : Params} {core : CorePrimitives p} :
    SignatureCore p core ≃ core.Y × (ForsSigCore p core × HtSigCore p core) where
  toFun signature := (signature.randomness, signature.fors, signature.hypertree)
  invFun fields := ⟨fields.1, fields.2.1, fields.2.2⟩
  left_inv := by intro signature; cases signature; rfl
  right_inv := by intro fields; rcases fields with ⟨_, _, _⟩; rfl

theorem publicKeyWidth (p : Params) : p.n + p.n = p.publicKeyBytes := by
  simp only [Params.publicKeyBytes]
  omega

theorem secretKeyWidth (p : Params) :
    p.n + (p.n + (p.n + p.n)) = p.secretKeyBytes := by
  simp only [Params.secretKeyBytes]
  omega

theorem forsTreeWidth (p : Params) :
    p.n + p.a * p.n = WireLayout.forsTreeBytes p := by
  simp [WireLayout.forsTreeBytes]
  ring

theorem xmssWidth (p : Params) :
    p.len * p.n + p.hp * p.n = WireLayout.xmssBytes p := by
  simp [WireLayout.xmssBytes]
  ring

/-- Strict codec for `PK.seed || PK.root`. -/
def publicKeyCodec {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core) :
    WireCodec (PublicKeyCore core) p.publicKeyBytes :=
  WireCodec.castWidth
    (WireCodec.precompose publicKeyFieldsEquiv (WireCodec.product atomic.pkSeed atomic.y))
    (publicKeyWidth p)

/-- Strict codec for `SK.seed || SK.prf || PK.seed || PK.root`. -/
def secretKeyCodec {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core) :
    WireCodec (SecretKeyCore core) p.secretKeyBytes :=
  WireCodec.castWidth
    (WireCodec.precompose secretKeyFieldsEquiv
      (WireCodec.product atomic.skSeed
        (WireCodec.product atomic.skPrf (WireCodec.product atomic.pkSeed atomic.y))))
    (secretKeyWidth p)

/-- Strict codec for one `FORS.sk || FORS.auth[a]` tree signature. -/
def forsTreeCodec {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core) :
    WireCodec (ForsTreeSigCore p core) (WireLayout.forsTreeBytes p) :=
  WireCodec.castWidth
    (WireCodec.precompose forsTreeFieldsEquiv
      (WireCodec.product atomic.y (WireCodec.vector atomic.y p.a)))
    (forsTreeWidth p)

/-- Strict codec for all `k` FORS tree signatures in increasing tree order. -/
def forsCodec {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core) :
    WireCodec (ForsSigCore p core) (WireLayout.forsBytes p) :=
  WireCodec.vector (forsTreeCodec atomic) p.k

/-- Strict codec for one `WOTS[len] || XMSS.auth[h']` signature. -/
def xmssCodec {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core) :
    WireCodec (XmssSigCore p core) (WireLayout.xmssBytes p) :=
  WireCodec.castWidth
    (WireCodec.precompose xmssFieldsEquiv
      (WireCodec.product (WireCodec.vector atomic.y p.len)
        (WireCodec.vector atomic.y p.hp)))
    (xmssWidth p)

/-- Strict codec for all `d` XMSS signatures in increasing hypertree-layer order. -/
def hypertreeCodec {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core) :
    WireCodec (HtSigCore p core) (WireLayout.hypertreeBytes p) :=
  WireCodec.vector (xmssCodec atomic) p.d

/-- Strict FIPS Figure 17 codec for the canonical structured signature. -/
def signatureCodec (vp : ValidatedParams) {core : CorePrimitives vp.params}
    (atomic : CoreWireCodec vp.params core) :
    WireCodec (SignatureCore vp.params core) vp.params.signatureBytes :=
  WireCodec.castWidth
    (WireCodec.precompose signatureFieldsEquiv
      (WireCodec.product atomic.y
        (WireCodec.product (forsCodec atomic) (hypertreeCodec atomic))))
    (WireLayout.total_eq_signatureBytes vp)

/-! ## Public checked byte interfaces -/

/-- Encode a canonical structured public key. -/
def encodePublicKey {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core)
    (key : PublicKeyCore core) : List Byte :=
  (publicKeyCodec atomic).encode key

/-- Decode a public key, rejecting every length other than `2n`. -/
def decodePublicKey {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core)
    (raw : List Byte) : Except CodecError (PublicKeyCore core) :=
  (publicKeyCodec atomic).decode raw

/-- Encode a canonical structured secret key. -/
def encodeSecretKey {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core)
    (key : SecretKeyCore core) : List Byte :=
  (secretKeyCodec atomic).encode key

/-- Decode a secret key, rejecting every length other than `4n`. -/
def decodeSecretKey {p : Params} {core : CorePrimitives p} (atomic : CoreWireCodec p core)
    (raw : List Byte) : Except CodecError (SecretKeyCore core) :=
  (secretKeyCodec atomic).decode raw

/-- Encode the canonical structured `R || SIG_FORS || SIG_HT` signature. -/
def encodeSignature (vp : ValidatedParams) {core : CorePrimitives vp.params}
    (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) : List Byte :=
  (signatureCodec vp atomic).encode signature

/-- Decode a complete signature, rejecting short, long, or partially consumed input. -/
def decodeSignature (vp : ValidatedParams) {core : CorePrimitives vp.params}
    (atomic : CoreWireCodec vp.params core) (raw : List Byte) :
    Except CodecError (SignatureCore vp.params core) :=
  (signatureCodec vp atomic).decode raw

@[simp] theorem decodePublicKey_encode {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (key : PublicKeyCore core) :
    decodePublicKey atomic (encodePublicKey atomic key) = .ok key := by
  exact WireCodec.decode_encode _ _

@[simp] theorem decodeSecretKey_encode {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (key : SecretKeyCore core) :
    decodeSecretKey atomic (encodeSecretKey atomic key) = .ok key := by
  exact WireCodec.decode_encode _ _

@[simp] theorem decodeSignature_encode (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) :
    decodeSignature vp atomic (encodeSignature vp atomic signature) = .ok signature := by
  exact WireCodec.decode_encode _ _

/-- Public-key decoding succeeds exactly when the entire input is the canonical encoding. -/
theorem decodePublicKey_eq_ok_iff {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (raw : List Byte) (key : PublicKeyCore core) :
    decodePublicKey atomic raw = .ok key ↔ raw = encodePublicKey atomic key := by
  exact WireCodec.decode_eq_ok_iff _ _ _

/-- Secret-key decoding succeeds exactly when the entire input is the canonical encoding. -/
theorem decodeSecretKey_eq_ok_iff {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (raw : List Byte) (key : SecretKeyCore core) :
    decodeSecretKey atomic raw = .ok key ↔ raw = encodeSecretKey atomic key := by
  exact WireCodec.decode_eq_ok_iff _ _ _

/-- Signature decoding succeeds exactly when the entire input is the canonical encoding. -/
theorem decodeSignature_eq_ok_iff (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (raw : List Byte) (signature : SignatureCore vp.params core) :
    decodeSignature vp atomic raw = .ok signature ↔
      raw = encodeSignature vp atomic signature := by
  exact WireCodec.decode_eq_ok_iff _ _ _

/-- Canonical structured public-key encoding is injective. -/
theorem encodePublicKey_injective {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) : Function.Injective (encodePublicKey atomic) :=
  WireCodec.encode_injective _

/-- Canonical structured secret-key encoding is injective. -/
theorem encodeSecretKey_injective {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) : Function.Injective (encodeSecretKey atomic) :=
  WireCodec.encode_injective _

/-- Canonical structured signature encoding is injective. -/
theorem encodeSignature_injective (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core) :
    Function.Injective (encodeSignature vp atomic) :=
  WireCodec.encode_injective _

@[simp] theorem encodePublicKey_length {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (key : PublicKeyCore core) :
    (encodePublicKey atomic key).length = p.publicKeyBytes := by
  exact WireCodec.encode_length _ _

@[simp] theorem encodeSecretKey_length {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (key : SecretKeyCore core) :
    (encodeSecretKey atomic key).length = p.secretKeyBytes := by
  exact WireCodec.encode_length _ _

@[simp] theorem encodeSignature_length (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) :
    (encodeSignature vp atomic signature).length = vp.params.signatureBytes := by
  exact WireCodec.encode_length _ _

/-! ## Layout pinning

The theorems below tie every `WireLayout` offset to the exact bytes `encodeSignature` emits:
dropping an offset and taking the component width recovers precisely that component's
canonical encoding. Reordering a fields equivalence, permuting a structure codec, or
mislabeling an offset therefore breaks a proof in this section.
-/

/-- Taking the width of an exact-width prefix recovers exactly that prefix. -/
private theorem take_width_append {α : Type} {width : ℕ} {left : List α}
    (h : left.length = width) (right : List α) : (left ++ right).take width = left := by
  subst h
  exact List.take_left ..

/-- Dropping an exact-width prefix plus `extra` drops `extra` items of the remainder. -/
private theorem drop_width_add_append {α : Type} {width : ℕ} {left : List α}
    (h : left.length = width) (right : List α) (extra : ℕ) :
    (left ++ right).drop (width + extra) = right.drop extra := by
  subst h
  exact List.drop_length_add_append extra

/-- Slicing a flattened sequence of fixed-width blocks at a block boundary recovers exactly
that block, independently of any suffix appended after the blocks. -/
theorem take_drop_flatten_ofFn_append {α : Type} {width : ℕ} :
    ∀ {count : ℕ} (blocks : Fin count → List α), (∀ i, (blocks i).length = width) →
      ∀ (suffix : List α) (i : Fin count),
        (((List.ofFn blocks).flatten ++ suffix).drop (i.val * width)).take width = blocks i := by
  intro count
  induction count with
  | zero => exact fun _ _ _ i => i.elim0
  | succ count ih =>
      intro blocks hwidth suffix i
      rw [List.ofFn_succ, List.flatten_cons, List.append_assoc]
      cases i using Fin.cases with
      | zero =>
          simp only [Fin.val_zero, Nat.zero_mul, List.drop_zero]
          exact take_width_append (hwidth 0) _
      | succ j =>
          rw [show (Fin.succ j).val * width = width + j.val * width by
            rw [Fin.val_succ, Nat.add_mul, Nat.one_mul, Nat.add_comm]]
          rw [drop_width_add_append (hwidth 0)]
          exact ih (fun i => blocks i.succ) (fun i => hwidth i.succ) suffix j

/-- Slicing a flattened sequence of fixed-width blocks at a block boundary recovers exactly
that block. -/
theorem take_drop_flatten_ofFn {α : Type} {width count : ℕ} (blocks : Fin count → List α)
    (hwidth : ∀ i, (blocks i).length = width) (i : Fin count) :
    ((List.ofFn blocks).flatten.drop (i.val * width)).take width = blocks i := by
  simpa using take_drop_flatten_ofFn_append blocks hwidth [] i

/-- A slice that stays inside one block of a wire can be read off the block itself. -/
theorem take_drop_add_of_take_drop {α : Type} {outer : List α} {offset width : ℕ}
    {block : List α} (hblock : (outer.drop offset).take width = block)
    {inner size : ℕ} (hfit : inner + size ≤ width) :
    (outer.drop (offset + inner)).take size = (block.drop inner).take size := by
  subst hblock
  rw [← List.drop_drop, List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

/-- A prefix of one block of a wire is the corresponding prefix of the block itself. -/
private theorem take_of_take_drop {α : Type} {outer : List α} {offset width : ℕ}
    {block : List α} (hblock : (outer.drop offset).take width = block)
    {size : ℕ} (hsize : size ≤ width) :
    (outer.drop offset).take size = block.take size := by
  rw [← hblock, List.take_take, Nat.min_eq_left hsize]

/-- Block-fit arithmetic: block `i` of `j` fixed-width blocks ends within the `j` blocks. -/
private theorem mul_add_le_mul {i j n : ℕ} (h : i < j) : i * n + n ≤ j * n := by
  calc i * n + n = (i + 1) * n := by ring
    _ ≤ j * n := Nat.mul_le_mul_right n h

/-! ### Wire normal forms -/

/-- The public-key wire is `PK.seed || PK.root` (FIPS 205 Figure 16; Algorithm 18). -/
theorem encodePublicKey_eq {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (key : PublicKeyCore core) :
    encodePublicKey atomic key
      = atomic.pkSeed.encode key.pkSeed ++ atomic.y.encode key.pkRoot := by
  simp [encodePublicKey, publicKeyCodec, publicKeyFieldsEquiv]

/-- The secret-key wire is `SK.seed || SK.prf || PK.seed || PK.root` (FIPS 205 Figure 15;
Algorithm 18 line 4). -/
theorem encodeSecretKey_eq {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (key : SecretKeyCore core) :
    encodeSecretKey atomic key
      = atomic.skSeed.encode key.skSeed ++ atomic.skPrf.encode key.skPrf
          ++ atomic.pkSeed.encode key.pkSeed ++ atomic.y.encode key.pkRoot := by
  simp [encodeSecretKey, secretKeyCodec, secretKeyFieldsEquiv]

/-- One FORS tree signature encodes its revealed secret, then its authentication path. -/
theorem forsTreeCodec_encode_eq {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (signature : ForsTreeSigCore p core) :
    (forsTreeCodec atomic).encode signature
      = atomic.y.encode signature.sk
          ++ (List.ofFn fun node : Fin p.a =>
              atomic.y.encode signature.auth[node.val]).flatten := by
  simp [forsTreeCodec, forsTreeFieldsEquiv]

/-- The FORS signature encodes its `k` tree signatures in increasing tree order. -/
theorem forsCodec_encode_eq {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (signature : ForsSigCore p core) :
    (forsCodec atomic).encode signature
      = (List.ofFn fun tree : Fin p.k =>
          (forsTreeCodec atomic).encode signature[tree.val]).flatten :=
  WireCodec.encode_vector (forsTreeCodec atomic) p.k signature

/-- One XMSS signature encodes its WOTS chain values, then its authentication path. -/
theorem xmssCodec_encode_eq {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (signature : XmssSigCore p core) :
    (xmssCodec atomic).encode signature
      = (List.ofFn fun chain : Fin p.len =>
            atomic.y.encode signature.wots[chain.val]).flatten
          ++ (List.ofFn fun node : Fin p.hp =>
              atomic.y.encode signature.auth[node.val]).flatten := by
  simp [xmssCodec, xmssFieldsEquiv]

/-- The hypertree signature encodes its `d` XMSS signatures in increasing layer order. -/
theorem hypertreeCodec_encode_eq {p : Params} {core : CorePrimitives p}
    (atomic : CoreWireCodec p core) (signature : HtSigCore p core) :
    (hypertreeCodec atomic).encode signature
      = (List.ofFn fun layer : Fin p.d =>
          (xmssCodec atomic).encode signature[layer.val]).flatten :=
  WireCodec.encode_vector (xmssCodec atomic) p.d signature

/-- The signature wire is `R || SIG_FORS || SIG_HT` (FIPS 205 Figure 17). -/
theorem encodeSignature_eq_append (vp : ValidatedParams) {core : CorePrimitives vp.params}
    (atomic : CoreWireCodec vp.params core) (signature : SignatureCore vp.params core) :
    encodeSignature vp atomic signature
      = atomic.y.encode signature.randomness
          ++ ((forsCodec atomic).encode signature.fors
            ++ (hypertreeCodec atomic).encode signature.hypertree) := by
  simp [encodeSignature, signatureCodec, signatureFieldsEquiv]

/-- FIPS 205 Figure 17 wire normal form: a signature serializes as the randomizer, then the
`k` FORS tree signatures (each a revealed secret followed by its `a` authentication nodes),
then the `d` XMSS signatures (each `len` WOTS values followed by `h'` authentication nodes),
all in increasing index order. -/
theorem encodeSignature_eq (vp : ValidatedParams) {core : CorePrimitives vp.params}
    (atomic : CoreWireCodec vp.params core) (signature : SignatureCore vp.params core) :
    encodeSignature vp atomic signature
      = atomic.y.encode signature.randomness
          ++ ((List.ofFn fun tree : Fin vp.params.k =>
                atomic.y.encode signature.fors[tree.val].sk
                  ++ (List.ofFn fun node : Fin vp.params.a =>
                      atomic.y.encode signature.fors[tree.val].auth[node.val]).flatten).flatten
            ++ (List.ofFn fun layer : Fin vp.params.d =>
                (List.ofFn fun chain : Fin vp.params.len =>
                    atomic.y.encode signature.hypertree[layer.val].wots[chain.val]).flatten
                  ++ (List.ofFn fun node : Fin vp.params.hp =>
                      atomic.y.encode
                        signature.hypertree[layer.val].auth[node.val]).flatten).flatten) := by
  rw [encodeSignature_eq_append, forsCodec_encode_eq, hypertreeCodec_encode_eq]
  simp only [forsTreeCodec_encode_eq, xmssCodec_encode_eq]

/-! ### Offset pinning -/

/-- Dropping the randomizer width plus `extra` bytes lands `extra` bytes into
`SIG_FORS || SIG_HT`. -/
private theorem drop_encodeSignature_add (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) (extra : ℕ) :
    (encodeSignature vp atomic signature).drop (vp.params.n + extra)
      = ((forsCodec atomic).encode signature.fors
          ++ (hypertreeCodec atomic).encode signature.hypertree).drop extra := by
  rw [encodeSignature_eq_append]
  exact drop_width_add_append (WireCodec.encode_length _ _) _ extra

/-- Dropping the FORS width plus `extra` bytes lands `extra` bytes into `SIG_HT`. -/
private theorem drop_forsHypertree_add (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) (extra : ℕ) :
    ((forsCodec atomic).encode signature.fors
        ++ (hypertreeCodec atomic).encode signature.hypertree).drop
          (WireLayout.forsBytes vp.params + extra)
      = ((hypertreeCodec atomic).encode signature.hypertree).drop extra :=
  drop_width_add_append (WireCodec.encode_length _ _) _ extra

/-- The signature bytes at `randomnessOffset` are exactly the encoded randomizer `R`. -/
theorem encodeSignature_randomness_slice (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) :
    ((encodeSignature vp atomic signature).drop
        (WireLayout.randomnessOffset vp.params)).take vp.params.n
      = atomic.y.encode signature.randomness := by
  rw [WireLayout.randomnessOffset, List.drop_zero, encodeSignature_eq_append]
  exact take_width_append (WireCodec.encode_length _ _) _

/-- The signature bytes at `forsTreeOffset tree` are exactly the encoding of FORS tree
signature `tree`. -/
theorem encodeSignature_forsTree_slice (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) (tree : Fin vp.params.k) :
    ((encodeSignature vp atomic signature).drop
        (WireLayout.forsTreeOffset vp.params tree.val)).take
          (WireLayout.forsTreeBytes vp.params)
      = (forsTreeCodec atomic).encode signature.fors[tree.val] := by
  rw [WireLayout.forsTreeOffset, WireLayout.forsOffset, drop_encodeSignature_add,
    forsCodec_encode_eq]
  exact take_drop_flatten_ofFn_append _ (fun i => WireCodec.encode_length _ _) _ tree

/-- The signature bytes at `forsSecretOffset tree` are exactly the encoded secret value
revealed in FORS tree `tree`. -/
theorem encodeSignature_forsSecret_slice (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) (tree : Fin vp.params.k) :
    ((encodeSignature vp atomic signature).drop
        (WireLayout.forsSecretOffset vp.params tree.val)).take vp.params.n
      = atomic.y.encode signature.fors[tree.val].sk := by
  have hn : vp.params.n ≤ WireLayout.forsTreeBytes vp.params := by
    rw [WireLayout.forsTreeBytes, Nat.add_mul, Nat.one_mul]
    exact Nat.le_add_right _ _
  rw [WireLayout.forsSecretOffset,
    take_of_take_drop (encodeSignature_forsTree_slice vp atomic signature tree) hn,
    forsTreeCodec_encode_eq]
  exact take_width_append (WireCodec.encode_length _ _) _

/-- The signature bytes at `forsAuthOffset tree node` are exactly the encoded authentication
node `node` of FORS tree `tree`. -/
theorem encodeSignature_forsAuth_slice (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) (tree : Fin vp.params.k)
    (node : Fin vp.params.a) :
    ((encodeSignature vp atomic signature).drop
        (WireLayout.forsAuthOffset vp.params tree.val node.val)).take vp.params.n
      = atomic.y.encode signature.fors[tree.val].auth[node.val] := by
  have hfit : (1 + node.val) * vp.params.n + vp.params.n
      ≤ WireLayout.forsTreeBytes vp.params := by
    rw [WireLayout.forsTreeBytes]
    exact mul_add_le_mul (by omega)
  rw [WireLayout.forsAuthOffset,
    take_drop_add_of_take_drop (encodeSignature_forsTree_slice vp atomic signature tree) hfit,
    forsTreeCodec_encode_eq,
    show (1 + node.val) * vp.params.n = vp.params.n + node.val * vp.params.n by ring,
    drop_width_add_append (WireCodec.encode_length _ _),
    take_drop_flatten_ofFn _ (fun i => WireCodec.encode_length _ _) node]

/-- The signature bytes at `xmssOffset layer` are exactly the encoding of the XMSS signature
at hypertree layer `layer`. -/
theorem encodeSignature_xmss_slice (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) (layer : Fin vp.params.d) :
    ((encodeSignature vp atomic signature).drop
        (WireLayout.xmssOffset vp.params layer.val)).take (WireLayout.xmssBytes vp.params)
      = (xmssCodec atomic).encode signature.hypertree[layer.val] := by
  rw [WireLayout.xmssOffset, WireLayout.hypertreeOffset, WireLayout.forsOffset,
    Nat.add_assoc, drop_encodeSignature_add, drop_forsHypertree_add,
    hypertreeCodec_encode_eq]
  exact take_drop_flatten_ofFn _ (fun i => WireCodec.encode_length _ _) layer

/-- The signature bytes at `wotsOffset layer chain` are exactly the encoded WOTS chain value
`chain` at hypertree layer `layer`. -/
theorem encodeSignature_wots_slice (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) (layer : Fin vp.params.d)
    (chain : Fin vp.params.len) :
    ((encodeSignature vp atomic signature).drop
        (WireLayout.wotsOffset vp.params layer.val chain.val)).take vp.params.n
      = atomic.y.encode signature.hypertree[layer.val].wots[chain.val] := by
  have hfit : chain.val * vp.params.n + vp.params.n ≤ WireLayout.xmssBytes vp.params := by
    rw [WireLayout.xmssBytes]
    exact mul_add_le_mul (by omega)
  rw [WireLayout.wotsOffset,
    take_drop_add_of_take_drop (encodeSignature_xmss_slice vp atomic signature layer) hfit,
    xmssCodec_encode_eq,
    take_drop_flatten_ofFn_append _ (fun i => WireCodec.encode_length _ _) _ chain]

/-- The signature bytes at `xmssAuthOffset layer node` are exactly the encoded authentication
node `node` of the XMSS signature at hypertree layer `layer`. -/
theorem encodeSignature_xmssAuth_slice (vp : ValidatedParams)
    {core : CorePrimitives vp.params} (atomic : CoreWireCodec vp.params core)
    (signature : SignatureCore vp.params core) (layer : Fin vp.params.d)
    (node : Fin vp.params.hp) :
    ((encodeSignature vp atomic signature).drop
        (WireLayout.xmssAuthOffset vp.params layer.val node.val)).take vp.params.n
      = atomic.y.encode signature.hypertree[layer.val].auth[node.val] := by
  have hfit : (vp.params.len + node.val) * vp.params.n + vp.params.n
      ≤ WireLayout.xmssBytes vp.params := by
    rw [WireLayout.xmssBytes]
    exact mul_add_le_mul (by omega)
  have hwots : (List.ofFn fun chain : Fin vp.params.len =>
      atomic.y.encode signature.hypertree[layer.val].wots[chain.val]).flatten.length
        = vp.params.len * vp.params.n := by
    rw [← WireCodec.encode_vector]
    exact WireCodec.encode_length _ _
  rw [WireLayout.xmssAuthOffset,
    take_drop_add_of_take_drop (encodeSignature_xmss_slice vp atomic signature layer) hfit,
    xmssCodec_encode_eq,
    show (vp.params.len + node.val) * vp.params.n
      = vp.params.len * vp.params.n + node.val * vp.params.n by ring,
    drop_width_add_append hwots,
    take_drop_flatten_ofFn _ (fun i => WireCodec.encode_length _ _) node]

end SLHDSA
