/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import Examples.ElGamal.Common
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# ElGamal Encryption: IND-CPA via the generic one-time lift

This file defines ElGamal encryption over a module `Module F G` and treats the security proof as
a one-time DDH client of the generic IND-CPA lift in `AsymmEncAlg`.

## Mathematical notation

We use additive / EC-style notation throughout:

| Textbook (multiplicative) | This file (additive)             |
|---------------------------|----------------------------------|
| `g^a`                     | `a • gen`                        |
| `g^a · g^b = g^{a+b}`     | `a • gen + b • gen`              |
| `(g^a)^b = g^{ab}`        | `b • (a • gen) = (b * a) • gen` |
| `m · g^{ab}`              | `m + (a * b) • gen`              |

Here `F` is the scalar field (for example `ZMod p`), `G` is the additive group of ciphertext
payloads (for example elliptic-curve points), and `gen : G` is a fixed public generator.

## Proof structure

1. ElGamal definition and correctness.
2. One-time DDH bridge:
   `IND_CPA_OneTime_DDHReduction`,
   `IND_CPA_OneTime_game_evalDist_eq_ddhExpReal`,
   `IND_CPA_OneTime_DDHReduction_rand_half`, and
   `elGamal_oneTime_signedAdvantageReal_abs_eq_two_mul_ddhGuessAdvantage`.
3. Final theorem:
   `elGamal_IND_CPA_le_q_mul_ddh` is a direct instantiation of
   `AsymmEncAlg.IND_CPA_advantage_toReal_le_q_mul_of_oneTime_signedAdvantageReal_bound`
   with one-time loss `2 * ε`.
-/

open OracleSpec OracleComp ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]

/-- ElGamal encryption over a module `Module F G` with generator `gen : G`.

Key generation samples a scalar `sk ← $ᵗ F` and returns `(sk • gen, sk)`.
Encryption of `msg` under public key `pk` samples `r ← $ᵗ F` and returns
`(r • gen, msg + r • pk)`. Decryption recovers `msg` as `c₂ - sk • c₁`. -/
@[simps!] noncomputable def elGamalAsymmEnc (F G : Type) [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] [AddCommGroup G] [Module F G] [SampleableType G]
    (gen : G) : AsymmEncAlg ProbComp
    (M := G) (PK := G) (SK := F) (C := G × G) where
  keygen := do
    let sk ← $ᵗ F
    return (sk • gen, sk)
  encrypt := fun pk msg => do
    let r ← $ᵗ F
    return (r • gen, msg + r • pk)
  decrypt := fun sk (c₁, c₂) =>
    return (some (c₂ - sk • c₁))
  toSPMFSemantics := SPMFSemantics.ofHasEvalSPMF ProbComp
  toProbCompLift := ProbCompLift.id

namespace elGamalAsymmEnc

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
variable {gen : G}

/-- ElGamal decryption perfectly inverts encryption: `Dec(sk, Enc(pk, msg)) = msg`. -/
theorem correct [DecidableEq G] : (elGamalAsymmEnc F G gen).PerfectlyCorrect := by
  sorry

section IND_CPA

variable [DecidableEq G]

local instance : Inhabited G := ⟨0⟩

/-- One-time DDH reduction for ElGamal. On input `(gen, A, B, T)`, use `A` as the ElGamal public
key, form the challenge ciphertext `(B, T + m_b)`, and return whether the one-time adversary
guessed the hidden bit `b`. -/
def IND_CPA_OneTime_DDHReduction
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) :
    DiffieHellman.DDHAdversary F G := fun _ A B T => do
  let (m₁, m₂, st) ← adv.chooseMessages A
  let bit ← ($ᵗ Bool : ProbComp Bool)
  let c : G × G := (B, T + if bit then m₁ else m₂)
  let bit' ← adv.distinguish st c
  pure (bit == bit')

omit [DecidableEq G] in
/-- Real-branch identification for the one-time ElGamal reduction. After unfolding
`IND_CPA_OneTime_Game_ProbComp`, `elGamalAsymmEnc`, `DiffieHellman.ddhExpReal`, and
`IND_CPA_OneTime_DDHReduction`, both sides normalize to the same sample space. -/
private lemma IND_CPA_OneTime_game_evalDist_eq_ddhExpReal
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) :
    evalDist
      (AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp
        (encAlg := elGamalAsymmEnc F G gen) adv) =
      evalDist
        (DiffieHellman.ddhExpReal (F := F) gen
          (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)) := by
  simp only [AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp,
    DiffieHellman.ddhExpReal, IND_CPA_OneTime_DDHReduction,
    elGamalAsymmEnc, SPMFSemantics.ofHasEvalSPMF]
  ext z
  change Pr[= z | _] = Pr[= z | _]
  simp only [bind_pure_comp, bind_map_left]
  -- Step 1: swap $ᵗBool past $ᵗF in LHS
  rw [probOutput_bind_bind_swap ($ᵗ Bool) ($ᵗ F)]
  -- Now LHS starts with $ᵗF. Use congr under $ᵗF.
  refine probOutput_bind_congr' ($ᵗ F) z (fun sk => ?_)
  -- Step 2: swap $ᵗBool past chooseMessages in LHS
  rw [probOutput_bind_bind_swap ($ᵗ Bool) (adv.chooseMessages (sk • gen))]
  -- Step 3: swap chooseMessages past $ᵗF in RHS
  conv_rhs => rw [probOutput_bind_bind_swap ($ᵗ F) (adv.chooseMessages (sk • gen))]
  -- Now both start with chooseMessages. Congr under it.
  refine probOutput_bind_congr' (adv.chooseMessages (sk • gen)) z (fun cm => ?_)
  -- Step 4: swap $ᵗBool past $ᵗF in LHS
  rw [probOutput_bind_bind_swap ($ᵗ Bool) ($ᵗ F)]
  -- Now both: $ᵗF >>= fun r => $ᵗBool >>= fun bit => ...
  refine probOutput_bind_congr' ($ᵗ F) z (fun r => ?_)
  refine probOutput_bind_congr' ($ᵗ Bool) z (fun bit => ?_)
  -- Now need to show the ciphertext expressions match
  -- LHS: (r•gen, (if bit then cm.1 else cm.2.1) + r • (sk • gen))
  -- RHS: (r•gen, (sk * r)•gen + (if bit then cm.1 else cm.2.1))
  congr 2
  rw [smul_smul, add_comm, mul_comm]

omit [DecidableEq G] in
/-- Random-branch half lemma for the one-time ElGamal reduction. Under bijectivity of `(· • gen)`,
the DDH-random branch gives a uniform additive mask independent of the challenge bit, so the
adversary can do no better than random guessing. -/
private lemma IND_CPA_OneTime_DDHReduction_rand_half
    (hg : Function.Bijective (· • gen : F → G))
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) :
    Pr[= true | DiffieHellman.ddhExpRand (F := F) gen
      (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] = 1 / 2 := by
  sorry

omit [DecidableEq G] in
/-- The absolute one-time signed IND-CPA advantage of ElGamal is exactly twice the DDH guess
advantage of the reduction above. The factor `2` is essential because the DDH guess advantage is
defined from the mixed experiment, while the one-time IND-CPA game compares the real and random
branches directly. -/
theorem elGamal_oneTime_signedAdvantageReal_abs_eq_two_mul_ddhGuessAdvantage
    (hg : Function.Bijective (· • gen : F → G))
    (adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen)) :
    |AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
        (encAlg := elGamalAsymmEnc F G gen) adv| =
      2 * DiffieHellman.ddhGuessAdvantage gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) := by
  have h_real :
      |AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
        (encAlg := elGamalAsymmEnc F G gen) adv| =
      |(Pr[= true | DiffieHellman.ddhExpReal (F := F) gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)]).toReal - 1 / 2| := by
    have hprob :
        Pr[= true | AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp
          (encAlg := elGamalAsymmEnc F G gen) adv] =
        Pr[= true | DiffieHellman.ddhExpReal (F := F) gen
          (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)] := by
      exact probOutput_congr rfl (IND_CPA_OneTime_game_evalDist_eq_ddhExpReal adv)
    simpa [AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal] using
      congrArg (fun p : ℝ≥0∞ => |p.toReal - 1 / 2|) hprob
  have h_rand : (1 : ℝ) / 2 =
    (Pr[= true | DiffieHellman.ddhExpRand (F := F) gen
      (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)]).toReal := by
    rw [IND_CPA_OneTime_DDHReduction_rand_half hg adv]
    simp [ENNReal.toReal_ofNat]
  rw [h_real, h_rand]
  exact DiffieHellman.ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage gen
    (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv)

/-- **Main theorem.** If an adversary makes at most `q` LR queries and every extracted one-time
ElGamal DDH reduction has guess advantage at most `ε`, then ElGamal has IND-CPA advantage at most
`q * (2 * ε)`. -/
theorem elGamal_IND_CPA_le_q_mul_ddh
    (hg : Function.Bijective (· • gen : F → G))
    (adversary : (elGamalAsymmEnc F G gen).IND_CPA_adversary)
    (q : ℕ) (ε : ℝ)
    (hq : adversary.MakesAtMostQueries q)
    (hddh : ∀ adv : AsymmEncAlg.IND_CPA_Adv (elGamalAsymmEnc F G gen),
      DiffieHellman.ddhGuessAdvantage gen
        (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) ≤ ε) :
    ((elGamalAsymmEnc F G gen).IND_CPA_advantage adversary).toReal ≤ q * (2 * ε) := by
  refine AsymmEncAlg.IND_CPA_advantage_toReal_le_q_mul_of_oneTime_signedAdvantageReal_bound
    (encAlg' := elGamalAsymmEnc F G gen) adversary q (2 * ε) hq ?_
  intro adv
  calc
    |AsymmEncAlg.IND_CPA_OneTime_signedAdvantageReal
        (encAlg := elGamalAsymmEnc F G gen) adv|
      = 2 * DiffieHellman.ddhGuessAdvantage gen
          (IND_CPA_OneTime_DDHReduction (F := F) (G := G) (gen := gen) adv) := by
            exact elGamal_oneTime_signedAdvantageReal_abs_eq_two_mul_ddhGuessAdvantage
              (F := F) (G := G) (gen := gen) hg adv
    _ ≤ 2 * ε := by
        linarith [hddh adv]

end IND_CPA

end elGamalAsymmEnc
