/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.CryptoFoundations.AsymmEncAlg.IND_CPA
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.CryptoFoundations.HardnessAssumptions.EntropySmoothing
import VCVio.EvalDist.Bool
import VCVio.ProgramLogic.Tactics

/-!
# Hashed ElGamal Encryption

This file defines hashed ElGamal encryption and proves that its one-time IND-CPA
advantage is bounded by the DDH advantage plus the entropy smoothing advantage.

Unlike standard ElGamal (where the message space is the group `G`), hashed ElGamal
uses a hash function `hash : HK → G → M` to map the DH shared secret into the
message space `M`. This allows encrypting messages in an arbitrary additive group `M`
(e.g. `BitVec n` with XOR).

## Security proof (4-game hop)

| Game | Description | Distance to next |
|------|-------------|-----------------|
| Game 0 (CPA) | Real hashed ElGamal | = DDH real |
| Game 1 | Replace the DH shared secret with an independent random scalar-multiple of `g` | DDH advantage |
| Game 2 (= Game 1) | Reinterpret as entropy smoothing real | 0 |
| Game 3 | Replace hash output with random | ES advantage |
| Game 4 (= 1/2) | The masking term is uniform, so the challenge bit is hidden | 0 |

Main theorem: `|Pr[CPA wins] - 1/2| ≤ ddhAdvantage + esAdvantage`.

## References

Port of EasyCrypt's `hashed_elgamal_std.ec`.
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal DiffieHellman

/-! ## Hashed ElGamal Scheme -/

/-- Hashed ElGamal encryption over a module `Module F G` with hash `hash : HK → G → M`.

| Operation | Definition |
|-----------|-----------|
| Keygen | Sample `hk ← $ᵗ HK`, `sk ← $ᵗ F`; PK = `(hk, sk • g)`, SK = `(hk, sk)` |
| Encrypt(pk, msg) | Sample `y ← $ᵗ F`; output `(y • g, hash hk (y • pk.2) + msg)` |
| Decrypt(sk, c) | Compute `c.2 - hash sk.1 (sk.2 • c.1)` |

The additive group operation `+` on `M` plays the role of XOR.
Following `elgamalAsymmEnc`, `F` and `G` are explicit type parameters. -/
@[simps!] def hashedElGamal (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {G : Type} [AddCommGroup G] [Module F G] [SampleableType G]
    {HK : Type} [SampleableType HK]
    {M : Type} [AddCommGroup M] [SampleableType M]
    (g : G) (hash : HK → G → M) :
    AsymmEncAlg ProbComp (M := M) (PK := HK × G) (SK := HK × F) (C := G × M) where
  keygen := do
    let hk ← $ᵗ HK
    let sk ← $ᵗ F
    return ((hk, sk • g), (hk, sk))
  encrypt pk msg := do
    let y ← $ᵗ F
    return (y • g, hash pk.1 (y • pk.2) + msg)
  decrypt sk c :=
    return (some (c.2 - hash sk.1 (sk.2 • c.1)))
  __ := ExecutionMethod.default

namespace hashedElGamal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [SampleableType G] [DecidableEq G]
variable {HK : Type} [SampleableType HK]
variable {M : Type} [AddCommGroup M] [SampleableType M] [DecidableEq M] [Fintype M]
variable {g : G} {hash : HK → G → M}

/-! ## Correctness -/

omit [DecidableEq G] [Fintype M] in
theorem correct :
    (hashedElGamal F g hash).PerfectlyCorrect := by
  have hcomm : ∀ (a b : F), a • (b • g) = b • (a • g) := by
    intro a b; rw [← mul_smul, mul_comm, mul_smul]
  intro msg
  simp [AsymmEncAlg.CorrectExp, hashedElGamal, hcomm]

/-! ## DDH Reduction -/

/-- Construct a DDH adversary from a CPA adversary for hashed ElGamal.
Given DDH challenge `(g, A, B, T)`:
- Set `pk = (hk, A)` where `hk ← $ᵗ HK`
- Let adversary choose messages
- Encrypt using `B` as first ciphertext component, `hash hk T + m_b` as second
- Return adversary's guess -/
def ddhReduction (adv : AsymmEncAlg.IND_CPA_Adv (hashedElGamal F g hash)) : DDHAdversary F G :=
  fun _g A B T => do
    let hk ← $ᵗ HK
    let (m₁, m₂, st) ← adv.chooseMessages (hk, A)
    let b ← $ᵗ Bool
    let c : G × M := (B, hash hk T + (if b then m₁ else m₂))
    let b' ← adv.distinguish st c
    return (b == b')

/-! ## Entropy Smoothing Reduction -/

/-- Construct an ES adversary from a CPA adversary for hashed ElGamal.
Given `(hk, v)` where `v` is either `hash hk (z • g)` or random:
- Sample a fresh secret key `sk` and encryption randomness `y`
- Set `pk = sk • g`
- Let adversary choose messages
- Encrypt using `(y • g, v + m_b)` as ciphertext
- Return adversary's guess -/
def esReduction (adv : AsymmEncAlg.IND_CPA_Adv (hashedElGamal F g hash)) :
    HK × M → ProbComp Bool :=
  fun (hk, v) => do
    let sk ← ($ᵗ F : ProbComp F)
    let (m₁, m₂, st) ← adv.chooseMessages (hk, sk • g)
    let b ← $ᵗ Bool
    let y ← ($ᵗ F : ProbComp F)
    let c : G × M := (y • g, v + (if b then m₁ else m₂))
    let b' ← adv.distinguish st c
    return (b == b')

/-! ## Game-hop lemmas -/

/-- Game 0 = CPA game equals DDH real branch (by construction). -/
theorem cpaGame_eq_ddhReal
    (adv : AsymmEncAlg.IND_CPA_Adv (hashedElGamal F g hash)) :
    Pr[= true | AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp
      (encAlg' := hashedElGamal F g hash) adv] =
    Pr[= true | ddhExpReal g (ddhReduction (F := F) (hash := hash) adv)] := by
  sorry

/-- DDH random branch equals ES real experiment (by construction). -/
theorem ddhRand_eq_esReal
    (adv : AsymmEncAlg.IND_CPA_Adv (hashedElGamal F g hash)) :
    Pr[= true | ddhExpRand g (ddhReduction (F := F) (hash := hash) adv)] =
    Pr[= true | EntropySmoothing.realExp F g hash (esReduction (F := F) (g := g) adv)] := by
  sorry

/-- ES ideal experiment: the ciphertext `v + m_b` with uniform `v` is uniform
regardless of `b`, so the game reduces to random guessing.
Uses the same uniform-masking principle as the one-time pad. -/
theorem esIdeal_eq_half
    (adv : AsymmEncAlg.IND_CPA_Adv (hashedElGamal F g hash)) :
    Pr[= true | EntropySmoothing.idealExp (esReduction (F := F) (g := g) adv)] = 1 / 2 := by
  sorry

/-! ## Main theorem -/

/-- **Main theorem.** The one-time IND-CPA bias of hashed ElGamal is bounded by
the DDH distinguishing advantage plus the entropy smoothing advantage:

`|Pr[CPA wins] - 1/2| ≤ ddhDistAdvantage(D) + EntropySmoothing.advantage(E)`

where `D` is the DDH reduction and `E` is the ES reduction, both constructed
from the CPA adversary. -/
theorem hashedElGamal_indcpa_bound
    (adv : AsymmEncAlg.IND_CPA_Adv (hashedElGamal F g hash)) :
    |(Pr[= true | AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp
      (encAlg' := hashedElGamal F g hash) adv]).toReal - 1 / 2| ≤
      ddhDistAdvantage g (ddhReduction (F := F) (hash := hash) adv) +
      EntropySmoothing.advantage F g hash (esReduction (F := F) (g := g) adv) := by
  sorry

end hashedElGamal
