/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.OracleContext

/-!
# Symmetric Encryption Schemes.

This file defines a type `SymmEncAlg spec M K C` to represent a protocol
for symmetric encryption using oracles in `spec`, with message space `M`,
secret keys of type `K`, and ciphertext space `C`.
-/

universe u v w

open OracleSpec OracleComp ENNReal

structure SymmEncAlg (M K C : ℕ → Type)
    (Q : Type v) extends OracleContext Q ProbComp where
  keygen (sp : ℕ) : OracleComp spec (K sp)
  encrypt {sp : ℕ} (k : K sp) (msg : M sp) : OracleComp spec (C sp)
  decrypt {sp : ℕ} (k : K sp) (c : C sp) : OptionT (OracleComp spec) (M sp)

namespace SymmEncAlg

variable {M K C : ℕ → Type} {Q : Type v}

def CompleteExp (encAlg : SymmEncAlg M K C Q) {sp : ℕ} (m : M sp) :
    OptionT (OracleComp encAlg.spec) (M sp) := do
  let k ← liftM (encAlg.keygen sp)
  let σ ← liftM (encAlg.encrypt k m)
  encAlg.decrypt k σ

def Complete (encAlg : SymmEncAlg M K C Q) : Prop := ∀ sp, ∀ m : M sp,
  Pr[= m | simulateQ encAlg.impl (CompleteExp encAlg m).run] = 1

section perfectSecrecy

def perfectSecrecy (encAlg : SymmEncAlg M K C Q) : Prop :=
  ∀ sp, ∀ mgen : OracleComp encAlg.spec (M sp), ∀ msg : M sp, ∀ σ : C sp,
    Pr[= (msg, σ) | simulateQ encAlg.impl do
      let msg' ← mgen
      let k ← encAlg.keygen sp
      return (msg', ← encAlg.encrypt k msg')] =
    Pr[= msg | simulateQ encAlg.impl mgen]

/-- Shannon's theorem on perfect secrecy at a fixed security parameter: if the message space,
key space, and ciphertext space have the same cardinality, then perfect secrecy holds iff
keys are chosen uniformly and for each (message, ciphertext) pair there is a unique key
that encrypts the message to that ciphertext.

The old version used non-asymptotic `SymmEncAlg m M K C`; here we fix `sp : ℕ` and work
at that security parameter.

`deterministicEnc` asserts that encryption is deterministic (support is a singleton),
which is required for the classical statement. -/
theorem perfectSecrecy_iff_of_card_eq (encAlg : SymmEncAlg M K C Q) (sp : ℕ)
    [Fintype (M sp)] [Fintype (K sp)] [Fintype (C sp)]
    (hComplete : encAlg.Complete)
    (h1 : Fintype.card (M sp) = Fintype.card (K sp))
    (h2 : Fintype.card (K sp) = Fintype.card (C sp))
    (deterministicEnc : ∀ (k : K sp) (msg : M sp),
      ∃ c, support (simulateQ encAlg.impl (encAlg.encrypt k msg)) = {c}) :
    (∀ mgen : OracleComp encAlg.spec (M sp), ∀ msg : M sp, ∀ σ : C sp,
      Pr[= (msg, σ) | simulateQ encAlg.impl do
        let msg' ← mgen
        let k ← encAlg.keygen sp
        return (msg', ← encAlg.encrypt k msg')] =
      Pr[= msg | simulateQ encAlg.impl mgen]) ↔
    ((∀ k : K sp, Pr[= k | simulateQ encAlg.impl (encAlg.keygen sp)] =
        (Fintype.card (K sp) : ℝ≥0∞)⁻¹) ∧
    (∀ msg : M sp, ∀ c : C sp, ∃! k : K sp,
        k ∈ support (simulateQ encAlg.impl (encAlg.keygen sp)) ∧
        c ∈ support (simulateQ encAlg.impl (encAlg.encrypt k msg)))) :=
  sorry

end perfectSecrecy

end SymmEncAlg
