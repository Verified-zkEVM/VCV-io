/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import LatticeCrypto.Falcon.Concrete.FloatLike
import LatticeCrypto.Falcon.Concrete.GMTable
import LatticeCrypto.Falcon.Concrete.SamplerZ

/-!
# FFT, FPoly Operations, and ffSampling for Falcon

Port of c-fn-dsa's `sign_fpoly.c` (FFT/iFFT/polynomial operations) and
`sign_sampler.c` (`ffsamp_fft` routines). All operations are generic over
`FloatLike F`. The precomputed twiddle factor table `gmRaw` stores IEEE-754
double bit patterns as `UInt64`; they are converted to `F` via
`FloatLike.ofRawFPR`.

## Data Layout

Polynomials of degree `n = 2^logn` are stored as `Array F` of size `n`, with
the first `n/2` entries as real parts and the last `n/2` as imaginary parts
(split representation used by the negacyclic FFT).

The `ffsamp` functions use a flat buffer layout matching the C reference,
organized into regions indexed by multiples of `qn = n/4`.
-/

set_option autoImplicit false

namespace Falcon.Concrete.FFTOps

open Falcon.Concrete.GMTable
open Falcon.Concrete.SamplerZ

section Generic

variable {F : Type} [FloatLike F]

instance : Inhabited F := ⟨FloatLike.zero⟩

/-! ## Helpers -/

@[inline] private def gmLoad (idx : Nat) : F :=
  FloatLike.ofRawFPR (gmRaw.getD idx 0)

@[inline] private def invSigmaLoad (logn : Nat) : F :=
  FloatLike.ofRawFPR (invSigmaRaw.getD logn 0)

@[inline] private def fZero : F := FloatLike.zero

/-! ## FFT -/

def fpolyFFT (logn : Nat) (f : Array F) : Array F := Id.run do
  if logn ≤ 1 then return f
  let hn := 1 <<< (logn - 1)
  let mut ff := f
  let mut t := hn
  for lm in [1:logn] do
    let m := 1 <<< lm
    let hm := m >>> 1
    let ht := t >>> 1
    let mut j0 := 0
    for i in [0:hm] do
      let s_re : F := gmLoad (((m + i) <<< 1) + 0)
      let s_im : F := gmLoad (((m + i) <<< 1) + 1)
      for j in [0:ht] do
        let j1 := j0 + j
        let j2 := j1 + ht
        let x_re := ff[j1]!
        let x_im := ff[j1 + hn]!
        let y_re := ff[j2]!
        let y_im := ff[j2 + hn]!
        let z_re := FloatLike.sub (FloatLike.mul y_re s_re) (FloatLike.mul y_im s_im)
        let z_im := FloatLike.add (FloatLike.mul y_im s_re) (FloatLike.mul y_re s_im)
        ff := ff.set! j1 (FloatLike.add x_re z_re)
        ff := ff.set! (j1 + hn) (FloatLike.add x_im z_im)
        ff := ff.set! j2 (FloatLike.sub x_re z_re)
        ff := ff.set! (j2 + hn) (FloatLike.sub x_im z_im)
      j0 := j0 + t
    t := ht
  return ff

/-! ## Inverse FFT -/

def fpolyIFFT (logn : Nat) (f : Array F) : Array F := Id.run do
  if logn ≤ 1 then return f
  let n := 1 <<< logn
  let hn := n >>> 1
  let mut ff := f
  let mut t := 1
  for lm in [1:logn] do
    let hm := 1 <<< (logn - lm)
    let dt := t <<< 1
    let mut j0 := 0
    for i in [0:hm >>> 1] do
      let s_re : F := gmLoad (((hm + i) <<< 1) + 0)
      let ns_im : F := FloatLike.neg (gmLoad (F := F) (((hm + i) <<< 1) + 1))
      for j in [0:t] do
        let j1 := j0 + j
        let j2 := j1 + t
        let x_re := ff[j1]!
        let x_im := ff[j1 + hn]!
        let y_re := ff[j2]!
        let y_im := ff[j2 + hn]!
        ff := ff.set! j1 (FloatLike.add x_re y_re)
        ff := ff.set! (j1 + hn) (FloatLike.add x_im y_im)
        let u_re := FloatLike.sub x_re y_re
        let u_im := FloatLike.sub x_im y_im
        ff := ff.set! j2 (FloatLike.sub (FloatLike.mul u_re s_re) (FloatLike.mul u_im ns_im))
        ff := ff.set! (j2 + hn) (FloatLike.add (FloatLike.mul u_im s_re) (FloatLike.mul u_re ns_im))
      j0 := j0 + dt
    t := dt
  let scaleExp : Int32 := (0 : Int32) - (51 : Int32) - logn.toUInt32.toInt32
  let scale : F := FloatLike.scaled (4503599627370496 : Int64) scaleExp
  for i in [0:n] do
    ff := ff.set! i (FloatLike.mul ff[i]! scale)
  return ff

/-! ## FPoly arithmetic -/

def fpolySetSmall (logn : Nat) (f : Array Int32) : Array F := Id.run do
  let n := 1 <<< logn
  let mut d : Array F := Array.replicate n fZero
  for i in [0:n] do
    d := d.set! i (FloatLike.ofInt32 (f.getD i 0))
  return d

def fpolyAdd (logn : Nat) (a b : Array F) : Array F := Id.run do
  let n := 1 <<< logn
  let mut aa := a
  for i in [0:n] do
    aa := aa.set! i (FloatLike.add aa[i]! (b.getD i fZero))
  return aa

def fpolySub (logn : Nat) (a b : Array F) : Array F := Id.run do
  let n := 1 <<< logn
  let mut aa := a
  for i in [0:n] do
    aa := aa.set! i (FloatLike.sub aa[i]! (b.getD i fZero))
  return aa

def fpolyNeg (logn : Nat) (a : Array F) : Array F := Id.run do
  let n := 1 <<< logn
  let mut aa := a
  for i in [0:n] do
    aa := aa.set! i (FloatLike.neg aa[i]!)
  return aa

def fpolyMulFFT (logn : Nat) (a b : Array F) : Array F := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut aa := a
  for i in [0:hn] do
    let a_re := aa[i]!
    let a_im := aa[i + hn]!
    let b_re := b.getD i fZero
    let b_im := b.getD (i + hn) fZero
    aa := aa.set! i (FloatLike.sub (FloatLike.mul a_re b_re) (FloatLike.mul a_im b_im))
    aa := aa.set! (i + hn) (FloatLike.add (FloatLike.mul a_re b_im) (FloatLike.mul a_im b_re))
  return aa

def fpolyMulConst (logn : Nat) (a : Array F) (x : F) : Array F := Id.run do
  let n := 1 <<< logn
  let mut aa := a
  for i in [0:n] do
    aa := aa.set! i (FloatLike.mul aa[i]! x)
  return aa

/-! ## LDL decomposition in FFT domain -/

def fpolyLDLFFT (logn : Nat) (g00 g01 g11 : Array F) : Array F × Array F := Id.run do
  let hn := 1 <<< (logn - 1)
  let mut gg01 := g01
  let mut gg11 := g11
  for i in [0:hn] do
    let g00_re := g00.getD i fZero
    let g01_re := gg01[i]!
    let g01_im := gg01[i + hn]!
    let g11_re := gg11[i]!
    let inv_g00_re := FloatLike.inv g00_re
    let mu_re := FloatLike.mul g01_re inv_g00_re
    let mu_im := FloatLike.mul g01_im inv_g00_re
    let zo_re := FloatLike.add (FloatLike.mul mu_re g01_re) (FloatLike.mul mu_im g01_im)
    gg11 := gg11.set! i (FloatLike.sub g11_re zo_re)
    gg01 := gg01.set! i mu_re
    gg01 := gg01.set! (i + hn) (FloatLike.neg mu_im)
  return (gg01, gg11)

/-! ## Split / Merge in FFT domain -/

def fpolySplitFFT (logn : Nat) (f : Array F) : Array F × Array F := Id.run do
  let hn := 1 <<< (logn - 1)
  let qn := hn >>> 1
  if logn ≤ 1 then
    return (#[f.getD 0 fZero], #[f.getD hn fZero])
  let h : F := FloatLike.half
  let mut f0 : Array F := Array.replicate hn fZero
  let mut f1 : Array F := Array.replicate hn fZero
  for i in [0:qn] do
    let a_re := f.getD ((i <<< 1) + 0) fZero
    let a_im := f.getD ((i <<< 1) + 0 + hn) fZero
    let b_re := f.getD ((i <<< 1) + 1) fZero
    let b_im := f.getD ((i <<< 1) + 1 + hn) fZero
    let t_re := FloatLike.add a_re b_re
    let t_im := FloatLike.add a_im b_im
    let u_re := FloatLike.sub a_re b_re
    let u_im := FloatLike.sub a_im b_im
    f0 := f0.set! i (FloatLike.mul t_re h)
    f0 := f0.set! (i + qn) (FloatLike.mul t_im h)
    let s_re : F := gmLoad (((i + hn) <<< 1) + 0)
    let s_im : F := gmLoad (((i + hn) <<< 1) + 1)
    let v_re := FloatLike.add (FloatLike.mul u_re s_re) (FloatLike.mul u_im s_im)
    let v_im := FloatLike.sub (FloatLike.mul u_im s_re) (FloatLike.mul u_re s_im)
    f1 := f1.set! i (FloatLike.mul v_re h)
    f1 := f1.set! (i + qn) (FloatLike.mul v_im h)
  return (f0, f1)

def fpolySplitSelfadjFFT (logn : Nat) (f : Array F) : Array F × Array F := Id.run do
  let hn := 1 <<< (logn - 1)
  let qn := hn >>> 1
  if logn ≤ 1 then
    return (#[f.getD 0 fZero], #[fZero])
  let h : F := FloatLike.half
  let mut f0 : Array F := Array.replicate hn fZero
  let mut f1 : Array F := Array.replicate hn fZero
  for i in [0:qn] do
    let a_re := f.getD ((i <<< 1) + 0) fZero
    let b_re := f.getD ((i <<< 1) + 1) fZero
    let t_re := FloatLike.add a_re b_re
    let u_re := FloatLike.mul (FloatLike.sub a_re b_re) h
    f0 := f0.set! i (FloatLike.mul t_re h)
    f0 := f0.set! (i + qn) fZero
    let s_re : F := gmLoad (((i + hn) <<< 1) + 0)
    let s_im : F := gmLoad (((i + hn) <<< 1) + 1)
    f1 := f1.set! i (FloatLike.mul u_re s_re)
    f1 := f1.set! (i + qn) (FloatLike.mul u_re (FloatLike.neg s_im))
  return (f0, f1)

def fpolyMergeFFT (logn : Nat) (f0 f1 : Array F) : Array F := Id.run do
  let hn := 1 <<< (logn - 1)
  let qn := hn >>> 1
  if logn ≤ 1 then
    return #[f0.getD 0 fZero, f1.getD 0 fZero]
  let n := 1 <<< logn
  let mut f : Array F := Array.replicate n fZero
  for i in [0:qn] do
    let a_re := f0.getD i fZero
    let a_im := f0.getD (i + qn) fZero
    let b_re := f1.getD i fZero
    let b_im := f1.getD (i + qn) fZero
    let s_re : F := gmLoad (((i + hn) <<< 1) + 0)
    let s_im : F := gmLoad (((i + hn) <<< 1) + 1)
    let c_re := FloatLike.sub (FloatLike.mul b_re s_re) (FloatLike.mul b_im s_im)
    let c_im := FloatLike.add (FloatLike.mul b_re s_im) (FloatLike.mul b_im s_re)
    f := f.set! ((i <<< 1) + 0) (FloatLike.add a_re c_re)
    f := f.set! ((i <<< 1) + 1) (FloatLike.sub a_re c_re)
    f := f.set! ((i <<< 1) + 0 + hn) (FloatLike.add a_im c_im)
    f := f.set! ((i <<< 1) + 1 + hn) (FloatLike.sub a_im c_im)
  return f

/-! ## Gram matrix in FFT domain -/

def fpolyGramFFT (logn : Nat) (b00 b01 b10 b11 : Array F) :
    Array F × Array F × Array F := Id.run do
  let hn := 1 <<< (logn - 1)
  let n := 1 <<< logn
  let mut g00 : Array F := Array.replicate n fZero
  let mut g01 : Array F := Array.replicate n fZero
  let mut g11 : Array F := Array.replicate n fZero
  for i in [0:hn] do
    let b00r := b00.getD i fZero
    let b00i := b00.getD (i + hn) fZero
    let b01r := b01.getD i fZero
    let b01i := b01.getD (i + hn) fZero
    let b10r := b10.getD i fZero
    let b10i := b10.getD (i + hn) fZero
    let b11r := b11.getD i fZero
    let b11i := b11.getD (i + hn) fZero
    g00 := g00.set! i (FloatLike.add
      (FloatLike.add (FloatLike.sqr b00r) (FloatLike.sqr b00i))
      (FloatLike.add (FloatLike.sqr b01r) (FloatLike.sqr b01i)))
    g00 := g00.set! (i + hn) fZero
    let ur := FloatLike.add (FloatLike.mul b00r b10r) (FloatLike.mul b00i b10i)
    let ui := FloatLike.sub (FloatLike.mul b00i b10r) (FloatLike.mul b00r b10i)
    let vr := FloatLike.add (FloatLike.mul b01r b11r) (FloatLike.mul b01i b11i)
    let vi := FloatLike.sub (FloatLike.mul b01i b11r) (FloatLike.mul b01r b11i)
    g01 := g01.set! i (FloatLike.add ur vr)
    g01 := g01.set! (i + hn) (FloatLike.add ui vi)
    g11 := g11.set! i (FloatLike.add
      (FloatLike.add (FloatLike.sqr b10r) (FloatLike.sqr b10i))
      (FloatLike.add (FloatLike.sqr b11r) (FloatLike.sqr b11i)))
    g11 := g11.set! (i + hn) fZero
  return (g00, g01, g11)

/-! ## Apply lattice basis -/

private def invQ : F := FloatLike.scaled (6004310871091074 : Int64) (-66 : Int32)
private def minusInvQ : F := FloatLike.scaled (-6004310871091074 : Int64) (-66 : Int32)

def fpolyApplyBasis (logn : Nat) (b01 b11 : Array F) (hm : Array UInt16) :
    Array F × Array F := Id.run do
  let n := 1 <<< logn
  let mut t0 : Array F := Array.replicate n fZero
  for i in [0:n] do
    t0 := t0.set! i (FloatLike.ofInt32 (hm.getD i 0).toUInt32.toInt32)
  t0 := fpolyFFT logn t0
  let nb01 := fpolyMulFFT logn b01 t0
  t0 := fpolyMulFFT logn t0 b11
  let t1 := fpolyMulConst logn nb01 (minusInvQ (F := F))
  t0 := fpolyMulConst logn t0 (invQ (F := F))
  return (t0, t1)

/-! ## Flat-buffer helpers for ffSampling

These operate directly on the flat buffer with offset arithmetic to avoid
unnecessary array copies. The `@[inline]` ensures the callee's `set!`
sees unique ownership of the array. -/

@[inline] private def bufExtract (buf : Array F) (off len : Nat) : Array F :=
  (Array.range len).map fun i => buf.getD (off + i) fZero

@[inline] private def bufWrite (buf : Array F) (off : Nat) (data : Array F) : Array F :=
  (Array.range data.size).foldl (init := buf) fun b i =>
    if off + i < b.size then b.set! (off + i) (data.getD i fZero) else b

@[inline] private def bufCopy (buf : Array F) (dstOff srcOff len : Nat) : Array F :=
  let saved := bufExtract buf srcOff len
  (Array.range len).foldl (init := buf) fun b i =>
    if dstOff + i < b.size then b.set! (dstOff + i) (saved.getD i fZero) else b

@[inline] private def bufAdd (buf : Array F) (logn aOff bOff : Nat) : Array F :=
  let n := 1 <<< logn
  (Array.range n).foldl (init := buf) fun b i =>
    b.set! (aOff + i) (FloatLike.add (b.getD (aOff + i) fZero) (b.getD (bOff + i) fZero))

@[inline] private def bufSub (buf : Array F) (logn aOff bOff : Nat) : Array F :=
  let n := 1 <<< logn
  (Array.range n).foldl (init := buf) fun b i =>
    b.set! (aOff + i) (FloatLike.sub (b.getD (aOff + i) fZero) (b.getD (bOff + i) fZero))

@[inline] private def bufMulFFT (buf : Array F) (logn aOff bOff : Nat) : Array F :=
  let hn := 1 <<< (logn - 1)
  (Array.range hn).foldl (init := buf) fun b i =>
    let ar := b.getD (aOff + i) fZero
    let ai := b.getD (aOff + i + hn) fZero
    let br := b.getD (bOff + i) fZero
    let bi := b.getD (bOff + i + hn) fZero
    let b := b.set! (aOff + i)
      (FloatLike.sub (FloatLike.mul ar br) (FloatLike.mul ai bi))
    b.set! (aOff + i + hn)
      (FloatLike.add (FloatLike.mul ar bi) (FloatLike.mul ai br))

/-! ## ffSampling -/

private def ffsampFFTDeepest (origLogn : Nat) (state : PRNGState) (tmp : Array F) :
    Array F × PRNGState := Id.run do
  let g00_re := tmp.getD 6 fZero
  let g01_re := tmp.getD 4 fZero
  let g01_im := tmp.getD 5 fZero
  let g11_re := tmp.getD 7 fZero
  let inv_g00 := FloatLike.inv g00_re
  let mu_re := FloatLike.mul g01_re inv_g00
  let mu_im := FloatLike.mul g01_im inv_g00
  let zo_re := FloatLike.add (FloatLike.mul mu_re g01_re) (FloatLike.mul mu_im g01_im)
  let d00_re := g00_re
  let l01_re := mu_re
  let l01_im := FloatLike.neg mu_im
  let d11_re := FloatLike.sub g11_re zo_re
  let w0 := tmp.getD 2 fZero
  let w1 := tmp.getD 3 fZero
  let leaf_r := FloatLike.mul (FloatLike.sqrt d11_re) (invSigmaLoad (F := F) origLogn)
  let (y0i, st1) := samplerZ origLogn state w0 leaf_r
  let (y1i, st2) := samplerZ origLogn st1 w1 leaf_r
  let y0 : F := FloatLike.ofInt32 y0i
  let y1 : F := FloatLike.ofInt32 y1i
  let a_re := FloatLike.sub w0 y0
  let a_im := FloatLike.sub w1 y1
  let b_re := FloatLike.sub (FloatLike.mul a_re l01_re) (FloatLike.mul a_im l01_im)
  let b_im := FloatLike.add (FloatLike.mul a_re l01_im) (FloatLike.mul a_im l01_re)
  let x0 := FloatLike.add (tmp.getD 0 fZero) b_re
  let x1 := FloatLike.add (tmp.getD 1 fZero) b_im
  let mut buf := tmp
  buf := buf.set! 2 y0
  buf := buf.set! 3 y1
  let leaf_l := FloatLike.mul (FloatLike.sqrt d00_re) (invSigmaLoad (F := F) origLogn)
  let (z0i, st3) := samplerZ origLogn st2 x0 leaf_l
  let (z1i, st4) := samplerZ origLogn st3 x1 leaf_l
  buf := buf.set! 0 (FloatLike.ofInt32 z0i)
  buf := buf.set! 1 (FloatLike.ofInt32 z1i)
  return (buf, st4)

partial def ffsampFFTInner (origLogn logn : Nat) (state : PRNGState) (tmp : Array F) :
    Array F × PRNGState :=
  if logn ≤ 1 then
    ffsampFFTDeepest origLogn state tmp
  else Id.run do
    let qn := 1 <<< (logn - 2)
    let n := 1 <<< logn
    let hn := n >>> 1
    let mut buf := tmp
    let mut st := state

    -- LDL decomposition: g00 at 12*qn (hn), g01 at 8*qn (n), g11 at 14*qn (hn)
    let g00 := bufExtract buf (12 * qn) hn
    let g01 := bufExtract buf (8 * qn) n
    let g11 := bufExtract buf (14 * qn) hn
    let (l10, d11) := fpolyLDLFFT logn g00 g01 g11
    buf := bufWrite buf (8 * qn) l10
    buf := bufWrite buf (14 * qn) d11

    -- Split d11 (self-adjoint) into right sub-tree
    let d11' := bufExtract buf (14 * qn) hn
    let (right00, right01) := fpolySplitSelfadjFFT logn d11'
    buf := bufWrite buf (20 * qn) right00
    buf := bufWrite buf (18 * qn) right01
    buf := bufCopy buf (21 * qn) (20 * qn) qn

    -- Split t1 into callee's t0/t1, then recurse (right sub-tree)
    let t1 := bufExtract buf (4 * qn) n
    let (t1f0, t1f1) := fpolySplitFFT logn t1
    buf := bufWrite buf (14 * qn) t1f0
    buf := bufWrite buf (16 * qn) t1f1
    let calleeBuf := bufExtract buf (14 * qn) (14 * qn)
    let (calleeBuf', st') := ffsampFFTInner origLogn (logn - 1) st calleeBuf
    buf := bufWrite buf (14 * qn) calleeBuf'
    st := st'

    -- Merge result into z1
    let mf0 := bufExtract buf (14 * qn) hn
    let mf1 := bufExtract buf (16 * qn) hn
    let z1 := fpolyMergeFFT logn mf0 mf1
    buf := bufWrite buf (18 * qn) z1

    -- Compute tb0 = t0 + (t1 - z1) * l10, move z1 into t1
    buf := bufCopy buf (14 * qn) (4 * qn) n
    buf := bufSub buf logn (14 * qn) (18 * qn)
    buf := bufCopy buf (4 * qn) (18 * qn) n
    buf := bufMulFFT buf logn (14 * qn) (8 * qn)
    buf := bufAdd buf logn 0 (14 * qn)

    -- Split d00 (self-adjoint) into left sub-tree
    let d00 := bufExtract buf (12 * qn) hn
    let (left00, left01) := fpolySplitSelfadjFFT logn d00
    buf := bufWrite buf (20 * qn) left00
    buf := bufWrite buf (18 * qn) left01
    buf := bufCopy buf (21 * qn) (20 * qn) qn

    -- Split tb0, recurse (left sub-tree), merge into t0
    let tb0 := bufExtract buf 0 n
    let (tb0f0, tb0f1) := fpolySplitFFT logn tb0
    buf := bufWrite buf (14 * qn) tb0f0
    buf := bufWrite buf (16 * qn) tb0f1
    let calleeBuf2 := bufExtract buf (14 * qn) (14 * qn)
    let (calleeBuf2', st'') := ffsampFFTInner origLogn (logn - 1) st calleeBuf2
    buf := bufWrite buf (14 * qn) calleeBuf2'
    st := st''

    let z0f0 := bufExtract buf (14 * qn) hn
    let z0f1 := bufExtract buf (16 * qn) hn
    let z0 := fpolyMergeFFT logn z0f0 z0f1
    buf := bufWrite buf 0 z0

    return (buf, st)

def ffSampling (logn : Nat) (state : PRNGState) (tmp : Array F) :
    Array F × PRNGState :=
  ffsampFFTInner logn logn state tmp

end Generic

end Falcon.Concrete.FFTOps
