/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg.Defs
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.SimSemantics.Append

/-!
# Asymmetric Encryption Schemes: IND-CCA

IND-CCA interfaces and games for asymmetric encryption schemes.
-/

open OracleSpec OracleComp ENNReal

universe u v w

namespace AsymmEncAlg

variable {m : Type → Type v} {M PK SK C : Type}
  (encAlg : AsymmEncAlg m M PK SK C)

section decryptionOracle

variable [Monad m]

/-- Oracle that uses a secret key to respond to decryption requests.
Invalid ciphertexts become oracle failure in `OptionT`. -/
def decryptionOracle (sk : SK) : QueryImpl (C →ₒ M) (OptionT m) :=
  fun c => OptionT.mk (encAlg.decrypt sk c)

end decryptionOracle

section IND_CCA

variable {ι : Type} {spec : OracleSpec ι} [DecidableEq C]

/-- IND-CCA adversaries get access to the base oracle set `spec` plus a decryption oracle.
Challenge generation is handled explicitly between the two phases of the game. -/
def IND_CCA_oracleSpec (_encAlg : AsymmEncAlg (OracleComp spec) M PK SK C) :=
    spec + (C →ₒ Option M)

/-- Two-phase IND-CCA adversary:
`chooseMessages` runs before the challenge and outputs `(m₀, m₁, st)`;
`distinguish st c⋆` runs after seeing the challenge ciphertext. -/
structure IND_CCA_Adversary (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C) where
  State : Type
  chooseMessages : PK → OracleComp encAlg.IND_CCA_oracleSpec (M × M × State)
  distinguish : State → C → OracleComp encAlg.IND_CCA_oracleSpec Bool

/-- Pre-challenge decryption oracle for the IND-CCA game. -/
def IND_CCA_preChallengeImpl (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C)
    (sk : SK) : QueryImpl (IND_CCA_oracleSpec encAlg) (OracleComp spec) :=
  (QueryImpl.ofLift spec (OracleComp spec)) + fun c => encAlg.decrypt sk c

/-- Post-challenge decryption oracle for the IND-CCA game.
The challenge ciphertext itself is answered with `none`, while all other ciphertexts are
decrypted normally. -/
def IND_CCA_postChallengeImpl (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C)
    (sk : SK) (cStar : C) : QueryImpl (IND_CCA_oracleSpec encAlg) (OracleComp spec) :=
  (QueryImpl.ofLift spec (OracleComp spec)) + fun c =>
    if c = cStar then return none else encAlg.decrypt sk c

/-- IND-CCA security game in the standard two-phase form.
The adversary chooses challenge messages with access to the decryption oracle, then receives
the challenge ciphertext and continues interacting with a decryption oracle that returns `none`
on the challenge ciphertext. -/
def IND_CCA_Game {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
    (adversary : encAlg.IND_CCA_Adversary) : ProbComp Bool :=
  encAlg.exec do
    let (pk, sk) ← encAlg.keygen
    let (m₀, m₁, st) ← simulateQ (encAlg.IND_CCA_preChallengeImpl sk)
      (adversary.chooseMessages pk)
    let b ← encAlg.lift_probComp ($ᵗ Bool)
    let cStar ← encAlg.encrypt pk (if b then m₀ else m₁)
    let b' ← simulateQ (encAlg.IND_CCA_postChallengeImpl sk cStar)
      (adversary.distinguish st cStar)
    return (b == b')

/-- Real-valued IND-CCA advantage, expressed as the Boolean bias of the IND-CCA game. -/
noncomputable def IND_CCA_Advantage {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
    (adversary : encAlg.IND_CCA_Adversary) : ℝ :=
  (IND_CCA_Game adversary).boolBiasAdvantage

end IND_CCA

end AsymmEncAlg
