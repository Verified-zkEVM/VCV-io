/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.Constructions.UniformSelect
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# Asymmetric Encryption Schemes.

This file defines a type `AsymmEncAlg spec M PK SK C` to represent an protocol
for asymmetric encryption using oracles in `spec`, with message space `M`,
public/secret keys `PK` and `SK`, and ciphertext space `C`.
-/

-- open OracleSpec OracleComp ENNReal

-- universe u v w

-- /-- An `AsymmEncAlg` with message space `M`, key spaces `PK` and `SK`, and ciphertexts in `C`.
-- `spec` is the available oracle set and `m` is the monad used to execute the oracle calls.
-- Extends `ExecutionMethod spec m`, in most cases will be `ExecutionMethod.default`. -/
-- structure AsymmEncAlg (m : Type → Type u) (M PK SK C : Type)
--     extends ExecutionMethod m where
--   keygen : m (PK × SK)
--   encrypt : (pk : PK) → (msg : M) →  m C
--   decrypt : (sk : SK) → (c : C) → Option M

-- alias PKE_Alg := AsymmEncAlg

-- namespace AsymmEncAlg

-- variable {ι : Type} {spec : OracleSpec ι} {m : Type → Type v} {M PK SK C : Type}
--   (encAlg : AsymmEncAlg m M PK SK C) {α β γ : Type}

-- section Correct

-- variable [DecidableEq M] [AlternativeMonad m]

-- /-- A `SymmEncAlg` is complete if decrypting an encrypted message always returns that original
-- message, captured here by a `guard` statement. -/
-- @[reducible, inline]
-- def CorrectExp (encAlg : AsymmEncAlg m M PK SK C) (msg : M) :
--     ProbComp Unit := encAlg.exec do
--   let (pk, sk) ← encAlg.keygen
--   guard (encAlg.decrypt sk (← encAlg.encrypt pk msg) = msg)

-- def PerfectlyCorrect (encAlg : AsymmEncAlg m M PK SK C) : Prop :=
--   ∀ (msg : M), [⊥ | CorrectExp encAlg msg] = 0

-- @[simp] lemma PerfectlyCorrect_iff (encAlg : AsymmEncAlg m M PK SK C) :
--     PerfectlyCorrect encAlg ↔ ∀ (msg : M),
--       [⊥ | CorrectExp encAlg msg] = 0 := Iff.rfl

-- end Correct

-- section IND_CPA

-- variable [DecidableEq M] [DecidableEq C]

-- -- Simplifying assumption: The algorithm is defined over `ProbComp`

-- def IND_CPA_oracleSpec (_encAlg : AsymmEncAlg ProbComp M PK SK C) :=
--   unifSpec ++ₒ (M × M →ₒ C) -- Second oracle for adversary to request challenge

-- def IND_CPA_adversary (encAlg : AsymmEncAlg ProbComp M PK SK C) :=
--   PK → OracleComp encAlg.IND_CPA_oracleSpec Bool
--   -- with poly functors: `ProbComp ((M × M) × (C → ProbComp Bool))`

-- /-- Can be shown this is equivalent to below definition for asymptotic security. -/
-- def IND_CPA_queryImpl' (encAlg : AsymmEncAlg ProbComp M PK SK C)
--     (pk : PK) (b : Bool) : QueryImpl encAlg.IND_CPA_oracleSpec
--       (StateT (M × M →ₒ C).QueryCache ProbComp) :=
--   have so : QueryImpl (M × M →ₒ C) ProbComp := ⟨fun (query () (m₁, m₂)) =>
--     encAlg.encrypt pk (if b then m₁ else m₂)⟩
--   idOracle ++ₛₒ so.withCaching

-- def IND_CPA_queryImpl (encAlg : AsymmEncAlg ProbComp M PK SK C)
--     (pk : PK) (b : Bool) : QueryImpl encAlg.IND_CPA_oracleSpec
--       (StateT (M × M →ₒ C).QueryCache ProbComp) :=
--   have so : QueryImpl (M × M →ₒ C) ProbComp := ⟨fun (query () (m₁, m₂)) =>
--     encAlg.encrypt pk (if b then m₁ else m₂)⟩
--   idOracle ++ₛₒ so

-- def IND_CPA_experiment {encAlg : AsymmEncAlg ProbComp M PK SK C}
--     (adversary : encAlg.IND_CPA_adversary) : ProbComp Unit := do
--   let b ← $ᵗ Bool
--   let (pk, _sk) ← encAlg.keygen
--   let b' ← (simulateQ (encAlg.IND_CPA_queryImpl' pk b) (adversary pk)).run' ∅
--   guard (b = b')

-- noncomputable def IND_CPA_advantage {encAlg : AsymmEncAlg ProbComp M PK SK C}
--     (adversary : encAlg.IND_CPA_adversary) : ℝ≥0∞ :=
--   [= () | IND_CPA_experiment adversary] - 1 / 2

-- /-- The probability of the IND-CPA experiment is the average of the probability of the experiment
-- with the challenge being true and the probability of the experiment with the challenge being false. -/
-- lemma probOutput_IND_CPA_experiment_eq_add {encAlg : AsymmEncAlg ProbComp M PK SK C}
--     (adversary : encAlg.IND_CPA_adversary) :
--     [= () | IND_CPA_experiment adversary] =
--       [= () | do
--         let (pk, _sk) ← encAlg.keygen
--         let b ← (simulateQ (encAlg.IND_CPA_queryImpl' pk true) (adversary pk)).run' ∅
--         guard b] / 2 +
--       [= () | do
--         let (pk, _sk) ← encAlg.keygen
--         let b ← (simulateQ (encAlg.IND_CPA_queryImpl' pk false) (adversary pk)).run' ∅
--         guard ¬b] / 2 := by
--   unfold IND_CPA_experiment
--   rw [probOutput_bind_eq_sum_finSupport]
--   have {x : ℝ≥0∞} : 2⁻¹ * x = x / 2 := by field_simp; rw [mul_comm, mul_div, mul_one]
--   simp [this]
  -- /-- T

-- end IND_CPA

-- section decryptionOracle

-- variable [AlternativeMonad m]

-- /-- Oracle that uses a secret key to respond to decryption requests. -/
-- def decryptionOracle (encAlg : AsymmEncAlg m M PK SK C)
--     (sk : SK) : QueryImpl (C →ₒ M) m where
--   impl | query () c => Option.getM (encAlg.decrypt sk c)

-- @[simp]
-- lemma decryptionOracle.apply_eq (encAlg : AsymmEncAlg m M PK SK C)
--     (sk : SK) (q : OracleQuery (C →ₒ M) α) : (decryptionOracle encAlg sk).impl q =
--     match q with | query () c => Option.getM (encAlg.decrypt sk c) := rfl

-- end decryptionOracle

-- section IND_CCA

-- variable [AlternativeMonad m] [LawfulAlternative m] [DecidableEq C]

-- /-- Two oracles for IND-CCA Experiment, the first for decrypting ciphertexts, and the second
-- for getting a challenge from a pair of messages. -/
-- def IND_CCA_oracleSpec (_encAlg : AsymmEncAlg m M PK SK C) :=
--     (C →ₒ Option M) ++ₒ ((M × M) →ₒ C)

-- /-- Implement oracles for IND-CCA security game. A state monad is to track the current challenge,
-- if it exists, and is set by the adversary calling the second oracle.
-- The decryption oracle checks to make sure it doesn't decrypt the challenge. -/
-- def IND_CCA_oracleImpl [DecidableEq C] (encAlg : AsymmEncAlg m M PK SK C)
--     (pk : PK) (sk : SK) (b : Bool) : QueryImpl (IND_CCA_oracleSpec encAlg)
--       (StateT (Option C) m) where impl
--   | query (Sum.inl ()) c => do
--       guard ((← get) ≠ some c)
--       return encAlg.decrypt sk c
--   | query (Sum.inr ()) (m₁, m₂) => do
--       guard (← get).isNone
--       let c ← encAlg.encrypt pk (if b then m₁ else m₂)
--       set (some c)
--       return c

-- structure IND_CCA_Adversary (encAlg : AsymmEncAlg m M PK SK C) where
--     main : PK → OracleComp encAlg.IND_CCA_oracleSpec Bool

-- def IND_CCA_Game (encAlg : AsymmEncAlg m M PK SK C)
--     (adversary : encAlg.IND_CCA_Adversary) : ProbComp Unit :=
--   encAlg.exec do
--     let (pk, sk) ← encAlg.keygen
--     let b ← encAlg.lift_probComp ($ᵗ Bool)
--     let b' ← (simulateQ (encAlg.IND_CCA_oracleImpl pk sk b) (adversary.main pk)).run' none
--     guard (b = b')

-- end IND_CCA

-- section IND_CPA

-- variable [DecidableEq ι]

-- variable [AlternativeMonad m] [LawfulAlternative m] [DecidableEq ι]

-- /--
-- `IND_CPA_adv M PK C` is an adversary for IND-CPA security game on an
-- asymmetric encryption with public keys in `PK`, messages in `M`, and ciphertexts in `C`.
-- The adversary consists of two functions:
-- * `chooseMessages`: given a public key, returns a pair of messages that it thinks
-- it can distinguish the encryption of, and a private state.
-- * `distinguish`: given a private state and an encryption, returns whether it is an encryption of
-- the first message or the second message -/
-- structure IND_CPA_Adv (encAlg : AsymmEncAlg m M PK SK C) where
--   State : Type
--   chooseMessages : PK → m (M × M × State)
--   distinguish : State → C → m Bool

-- variable {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
--   (adv : IND_CPA_Adv encAlg)

-- /--
-- Experiment for *one-time* IND-CPA security of an asymmetric encryption algorithm:
-- 1. Run `keygen` to get a public key and a private key.
-- 2. Run `adv.chooseMessages` on `pk` to get a pair of messages and a private state.
-- 3. The challenger then tosses a coin and encrypts one of the messages, returning the ciphertext `c`.
-- 4. Run `adv.distinguish` on the private state and the ciphertext to get a boolean.
-- 5. Return a Boolean indicating whether the adversary's guess is correct.

-- Note: we do _not_ want to end with a `guard` statement, as this can be biased by the adversary
-- potentially always failing.
-- -/
-- def IND_CPA_OneTime_Game : ProbComp Bool :=
--   encAlg.exec do
--     let b : Bool ← encAlg.lift_probComp ($ᵗ Bool)
--     let (pk, _) ← encAlg.keygen
--     let (m₁, m₂, state) ← adv.chooseMessages pk
--     let m := if b then m₁ else m₂
--     let c ← encAlg.encrypt pk m
--     let b' ← adv.distinguish state c
--     return b = b'

-- noncomputable def IND_CPA_OneTime_Advantage (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C)
--     (adv : IND_CPA_Adv encAlg) : ℝ :=
--   (IND_CPA_OneTime_Game (encAlg := encAlg) adv).advantage'

-- -- TODO: prove one-time security implies general IND-CPA security

-- end IND_CPA

-- end AsymmEncAlg
