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

open OracleSpec OracleComp

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
  Pr[= m | simulateQ encAlg.impl (CompleteExp encAlg m)] = 1

-- end complete

-- section perfectSecrecy

-- open ENNReal

-- def perfectSecrecy (encAlg : SymmEncAlg m M K C) : Prop :=
--   ∀ mgen : ProbComp M, ∀ msg : M, ∀ σ : C,
--     [= (msg, σ) | encAlg.exec do
--       let msg' ← encAlg.lift_probComp mgen
--       (msg', ·) <$> encAlg.encrypt (← encAlg.keygen) msg'] =
--     [= msg | mgen]

-- /-- Shanon's theorem on perfect secrecy, showing that encryption and decryption must be determined
-- bijections between message and cipher-text space, and that keys must be chosen uniformly. -/
-- theorem perfectSecrecy_iff_of_card_eq [Fintype M] [Fintype K] [Fintype C]
--     (encAlg : SymmEncAlg m M K C) [encAlg.Complete] (h1 : Fintype.card M = Fintype.card K)
--     (h2 : Fintype.card K = Fintype.card C) : encAlg.perfectSecrecy ↔
--       (∀ k, [= k | encAlg.exec encAlg.keygen] = (Fintype.card K : ℝ≥0∞)⁻¹) ∧
--       (∀ m c, ∃! k, k ∈ (encAlg.exec encAlg.keygen).support ∧ encAlg.encrypt k m = c) :=
--   sorry

-- end perfectSecrecy

end SymmEncAlg
