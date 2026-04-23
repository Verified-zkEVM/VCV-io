/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.HeapSSP.Composition
import VCVio.OracleComp.Constructions.BitVec

/-!
# One-Time Pad as a HeapSSP package

Pilot port of `Examples.OneTimePad.Basic` to the experimental `HeapSSP`
framework: the OTP perfect-secrecy story, rebuilt as a `HeapSSP.Package`
"real vs ideal" pair, with single-query indistinguishability proved at
the package level.

This file is the first real-proof port for the HeapSSP pilot; see
`Notes/vcvio-fs-schnorr-clean-chain.md` §D.14 for context. The point is
to compare a *package-level* OTP proof against the `SymmEncAlg`-style
proof in `Examples.OneTimePad.Basic`. The cryptographic content is
identical, "XOR with a uniform key is uniform"; the HeapSSP layer adds
package wiring (a key cell, a single-query export oracle, real and
ideal packages) on top.

## What this file builds

* `otpSpec sp` exposes a single export query `enc m` taking a plaintext
  `m : BitVec sp` and returning a ciphertext `BitVec sp`.
* `realPkg sp` carries a single named cell `KeyIdent.key : BitVec sp`,
  initialized by uniform sampling at start-of-game. Each `enc m` query
  reads `key` from the heap and returns `key ⊕ m`, the OTP encryption.
* `idealPkg sp` carries no state (identifier set `PEmpty.{1}`). Each
  `enc m` query ignores `m`, samples a fresh uniform ciphertext, and
  returns it.
* `encOnce sp m` is the single-call adversary that issues one `enc m`
  query and returns the ciphertext.
* `evalDist_run_encOnce_eq` is the headline single-query
  indistinguishability: the real and ideal packages produce the same
  output distribution on `encOnce sp m`, for every plaintext `m`.

## Why single-query

OTP secrecy *is* single-key, single-query: encrypting two messages
under the same key reveals their XOR. This pilot file therefore stops
at the single-call lemma, the exact analogue of
`Examples.OneTimePad.Basic.cipherGivenMsg_equiv`. Multi-query
distinguishing is straightforward but orthogonal to the comparison
this pilot is making.

## Comparison with `Examples.OneTimePad.Basic`

`Basic.lean` uses the `SymmEncAlg` abstraction layer (with
`PerfectSecrecyExp`, `Complete`, `perfectSecrecyAt`); it does not use
the SSP package layer. This file uses the HeapSSP package layer
directly. The two files prove the same content ("XOR with a uniform
key is uniform") but exhibit two structurally different framings of
the OTP. The arithmetic core, `probOutput_xor_uniform`, is shared
verbatim. -/

open OracleSpec OracleComp ENNReal

namespace VCVio.HeapSSP.OneTimePad

/-! ## Export oracle interface

A single export query `enc m` with `m : BitVec sp` carrying the
plaintext, returning a ciphertext `BitVec sp`. -/

/-- The OTP export query index: a single constructor `enc m` carrying
the plaintext. -/
inductive OTPOp (sp : ℕ)
  | enc (m : BitVec sp)

/-- The OTP export interface: each `enc _` query returns a `BitVec sp`
ciphertext. -/
@[reducible] def otpSpec (sp : ℕ) : OracleSpec.{0, 0} (OTPOp sp)
  | .enc _ => BitVec sp

/-! ## Real package: OTP key in a single named cell -/

/-- Cell directory for the real OTP package: a single cell `key`
holding the OTP key. -/
inductive KeyIdent (sp : ℕ)
  | key
  deriving DecidableEq

/-- The cell `key` carries a `BitVec sp`. The default value (used by
`Heap.empty` before any write) is the all-zero key; the real package
overwrites it at `init`-time with a uniform sample. -/
instance instCellSpecKeyIdent (sp : ℕ) : CellSpec (KeyIdent sp) where
  type    | .key => BitVec sp
  default | .key => 0#sp

/-- The **real-world OTP package**.

* **State.** A single named cell `KeyIdent.key : BitVec sp`.
* **Init.** Sample a uniform key `k : BitVec sp` and write it to
  `KeyIdent.key`.
* **Handler.** Each `enc m` query reads `key` and returns
  `key ⊕ m`, leaving the heap unchanged. -/
def realPkg (sp : ℕ) : Package unifSpec (otpSpec sp) (KeyIdent sp) where
  init := do
    let k ← ($ᵗ BitVec sp : ProbComp (BitVec sp))
    pure (Heap.empty.update .key k)
  impl
    | .enc m => StateT.mk fun (h : Heap (KeyIdent sp)) =>
        pure (h .key ^^^ m, h)

/-! ## Ideal package: stateless, fresh uniform ciphertext per call -/

/-- The **ideal-world OTP package**.

* **State.** Empty (`PEmpty.{1}` identifier set, singleton heap).
* **Init.** Trivial.
* **Handler.** Each `enc _` query ignores the plaintext and samples
  a fresh uniform ciphertext.

The structurally distinct state types of `realPkg` (a single key cell)
and `idealPkg` (no cells at all) are the heap-level analogue of the
SSP-style "different state types are fine, they live in separate
packages" pattern. The `evalDist`-equivalence below collapses the two
cleanly without any state-bijection bookkeeping. -/
def idealPkg (sp : ℕ) : Package unifSpec (otpSpec sp) PEmpty.{1} where
  init := pure Heap.empty
  impl
    | .enc _ => StateT.mk fun (_ : Heap PEmpty.{1}) => do
        let c ← ($ᵗ BitVec sp : ProbComp (BitVec sp))
        pure (c, Heap.empty)

/-! ## Single-query indistinguishability -/

/-- The single-call adversary that issues one `enc m` query and
returns the ciphertext verbatim.

The body `(otpSpec sp).query (.enc m)` is an `OracleQuery (otpSpec sp) _`;
the implicit `MonadLift (OracleQuery spec) (OracleComp spec)` lifts it
into `OracleComp (otpSpec sp) (BitVec sp)`, matching the declared
return type. Going through the named `(otpSpec sp).query` (rather than
the bare `query (.enc m)`) is what pins down the `spec` for elaboration. -/
def encOnce (sp : ℕ) (m : BitVec sp) : OracleComp (otpSpec sp) (BitVec sp) :=
  (otpSpec sp).query (.enc m)

/-- Closed form for the real package's single-call run: it equals
`(· ^^^ m) <$> ($ᵗ BitVec sp)`.

Mechanically: `realPkg.init` samples `k`, the handler reads it from the
freshly-written cell (`Function.update_self`, since `Heap.update` is
`Function.update`), and `Package.run` discards the final heap. -/
lemma run_realPkg_encOnce (sp : ℕ) (m : BitVec sp) :
    (realPkg sp).run (encOnce sp m) =
      (fun k : BitVec sp => k ^^^ m) <$> ($ᵗ BitVec sp : ProbComp (BitVec sp)) := by
  unfold encOnce realPkg Package.run
  simp [simulateQ_query, StateT.run'_eq, StateT.run, StateT.mk,
    Heap.update, Function.update_self, bind_pure_comp,
    map_eq_bind_pure_comp]

/-- Closed form for the ideal package's single-call run: it equals a
fresh uniform sample over `BitVec sp`. -/
lemma run_idealPkg_encOnce (sp : ℕ) (m : BitVec sp) :
    (idealPkg sp).run (encOnce sp m) =
      ($ᵗ BitVec sp : ProbComp (BitVec sp)) := by
  unfold encOnce idealPkg Package.run
  simp [simulateQ_query, StateT.run'_eq, StateT.run, StateT.mk,
    bind_pure_comp]

/-- **OTP single-query indistinguishability.** The real and ideal
packages produce the same output distribution on a single `enc m`
query, for every plaintext `m`.

The HeapSSP layer reduces this to "XOR with a uniform key is uniform"
(`probOutput_xor_uniform`); the rest is package wiring. The same
content, framed as `SymmEncAlg.PerfectSecrecyCipherGivenMsgExp`
equivalence, is proved as `cipherGivenMsg_equiv` in
`Examples.OneTimePad.Basic`. -/
theorem evalDist_run_encOnce_eq (sp : ℕ) (m : BitVec sp) :
    evalDist ((realPkg sp).run (encOnce sp m)) =
      evalDist ((idealPkg sp).run (encOnce sp m)) := by
  rw [run_realPkg_encOnce, run_idealPkg_encOnce]
  refine evalDist_ext fun σ => ?_
  rw [probOutput_xor_uniform sp m σ, probOutput_uniformSample (BitVec sp) σ]

end VCVio.HeapSSP.OneTimePad
