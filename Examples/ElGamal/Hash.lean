/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Examples.ElGamal.Common
import VCVio.CryptoFoundations.AsymmEncAlg.INDCPA
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.CryptoFoundations.HardnessAssumptions.EntropySmoothing
import VCVio.EvalDist.Bool

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
| Game 1 | Replace the DH shared secret with an independent random multiple of `g` | DDH advantage |
| Game 2 (= Game 1) | Reinterpret as entropy smoothing real | 0 |
| Game 3 | Replace hash output with random | ES advantage |
| Game 4 (= 1/2) | The masking term is uniform, so the challenge bit is hidden | 0 |

Main theorem: `|Pr[CPA wins] - 1/2| ≤ ddhAdvantage + esAdvantage`.

## References

Port of EasyCrypt's `hashed_elgamal_std.ec`.
-/


open OracleComp OracleSpec ENNReal DiffieHellman

/-! ## Hashed ElGamal Scheme -/

/-- Hashed ElGamal encryption over a module `Module F G` with hash `hash : HK → G → M`.

| Operation | Definition |
|-----------|-----------|
| Keygen | Sample `hk ← $ᵗ HK`, `sk ← $ᵗ F`; PK = `(hk, sk • g)`, SK = `(hk, sk)` |
| Encrypt(pk, msg) | Sample `y ← $ᵗ F`; output `(y • g, hash hk (y • pk.2) + msg)` |
| Decrypt(sk, c) | Compute `c.2 - hash sk.1 (sk.2 • c.1)` |

The additive group operation `+` on `M` plays the role of XOR.
Following `elGamalAsymmEnc`, `F` and `G` are explicit type parameters. -/
@[simps!] def hashedElGamal
    (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    {G : Type} [AddCommGroup G] [Module F G]
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

namespace hashedElGamal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {G : Type} [AddCommGroup G] [Module F G] [DecidableEq G]
variable {HK : Type} [SampleableType HK]
variable {M : Type} [AddCommGroup M] [SampleableType M] [DecidableEq M]
variable {g : G} {hash : HK → G → M}

/-! ## Correctness -/

omit [DecidableEq G] in
theorem correct :
    (hashedElGamal F g hash).PerfectlyCorrect ProbCompRuntime.probComp := by
  have hcomm : ∀ (a b : F), a • (b • g) = b • (a • g) := by
    intro a b; rw [← mul_smul, mul_comm, mul_smul]
  intro msg
  simp [AsymmEncAlg.CorrectExp, ProbCompRuntime.probComp, ProbCompRuntime.evalDist,
    hashedElGamal, hcomm,
    HasEvalPMF.toSPMF_eq, SPMF.probFailure_liftM, HasEvalPMF.probFailure_eq_zero]

/-! ## DDH Reduction -/

section Security

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
    let sk ← ($ᵗ F)
    let (m₁, m₂, st) ← adv.chooseMessages (hk, sk • g)
    let b ← $ᵗ Bool
    let y ← ($ᵗ F)
    let c : G × M := (y • g, v + (if b then m₁ else m₂))
    let b' ← adv.distinguish st c
    return (b == b')

/-! ## Game-hop lemmas -/

omit [DecidableEq G] [DecidableEq M] in
/-- Game 0 = CPA game equals DDH real branch (by construction). -/
theorem cpaGame_eq_ddhReal
    (adv : AsymmEncAlg.IND_CPA_Adv (hashedElGamal F g hash)) :
    Pr[= true | AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp
      (encAlg := hashedElGamal F g hash) adv] =
    Pr[= true | ddhExpReal g (ddhReduction (F := F) (hash := hash) adv)] := by
  let cpaCanonical : ProbComp Bool := do
    let b ← ($ᵗ Bool)
    let hk ← ($ᵗ HK)
    let a ← ($ᵗ F)
    let x ← adv.chooseMessages (hk, a • g)
    let y ← ($ᵗ F)
    let b' ← adv.distinguish x.2.2
      (y • g, hash hk (y • (a • g)) + if b then x.1 else x.2.1)
    pure (b == b')
  let ddhCanonical : ProbComp Bool := do
    let hk ← ($ᵗ HK)
    let a ← ($ᵗ F)
    let x ← adv.chooseMessages (hk, a • g)
    let b ← ($ᵗ Bool)
    let y ← ($ᵗ F)
    let b' ← adv.distinguish x.2.2
      (y • g, hash hk (y • (a • g)) + if b then x.1 else x.2.1)
    pure (b == b')
  have hleft :
      Pr[= true | AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp
        (encAlg := hashedElGamal F g hash) adv] =
      Pr[= true | cpaCanonical] := by
    simp [AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp, hashedElGamal, cpaCanonical,
      map_eq_bind_pure_comp, smul_smul, mul_comm]
  have hswap :
      Pr[= true | cpaCanonical] =
      Pr[= true | ddhCanonical] := by
    simpa [cpaCanonical, ddhCanonical, bind_assoc, map_eq_bind_pure_comp] using
      (probOutput_bind_bind_swap
        ($ᵗ Bool)
        (do
          let hk ← ($ᵗ HK)
          let a ← ($ᵗ F)
          let x ← adv.chooseMessages (hk, a • g)
          pure (hk, a, x))
        (fun b ⟨hk, a, x⟩ => do
          let y ← ($ᵗ F)
          let b' ← adv.distinguish x.2.2
            (y • g, hash hk (y • (a • g)) + if b then x.1 else x.2.1)
          pure (b == b'))
        true)
  have hright :
      Pr[= true | ddhExpReal g (ddhReduction (F := F) (hash := hash) adv)] =
      Pr[= true | ddhCanonical] := by
    trans Pr[= true | do
      let a ← ($ᵗ F)
      let hk ← ($ᵗ HK)
      let x ← adv.chooseMessages (hk, a • g)
      let b ← ($ᵗ Bool)
      let y ← ($ᵗ F)
      let b' ← adv.distinguish x.2.2
        (y • g, hash hk (y • (a • g)) + if b then x.1 else x.2.1)
      pure (b == b')]
    · simpa [ddhExpReal, ddhReduction, bind_assoc, map_eq_bind_pure_comp,
        smul_smul, mul_comm] using
        (probOutput_bind_congr' ($ᵗ F) true (fun a => by
          simpa [bind_assoc, map_eq_bind_pure_comp, smul_smul, mul_comm] using
            (probOutput_bind_bind_swap
              ($ᵗ F)
              (do
                let hk ← ($ᵗ HK)
                let x ← adv.chooseMessages (hk, a • g)
                let b ← ($ᵗ Bool)
                pure (hk, x, b))
              (fun y ⟨hk, x, b⟩ => do
                let b' ← adv.distinguish x.2.2
                  (y • g, hash hk (y • (a • g)) + if b then x.1 else x.2.1)
                pure (b == b'))
              true)))
    · simpa [ddhCanonical, bind_assoc, map_eq_bind_pure_comp] using
        (probOutput_bind_bind_swap
          ($ᵗ F)
          ($ᵗ HK)
          (fun a hk => do
            let x ← adv.chooseMessages (hk, a • g)
            let b ← ($ᵗ Bool)
            let y ← ($ᵗ F)
            let b' ← adv.distinguish x.2.2
              (y • g, hash hk (y • (a • g)) + if b then x.1 else x.2.1)
            pure (b == b'))
          true)
  exact hleft.trans (hswap.trans hright.symm)

omit [DecidableEq G] [DecidableEq M] in
/-- DDH random branch equals ES real experiment (by construction). -/
theorem ddhRand_eq_esReal
    (adv : AsymmEncAlg.IND_CPA_Adv (hashedElGamal F g hash)) :
    Pr[= true | ddhExpRand g (ddhReduction (F := F) (hash := hash) adv)] =
    Pr[= true | EntropySmoothing.realExp F g hash (esReduction (F := F) (g := g) adv)] := by
  let canonical : ProbComp Bool := do
    let hk ← ($ᵗ HK)
    let a ← ($ᵗ F)
    let x ← adv.chooseMessages (hk, a • g)
    let b ← ($ᵗ Bool)
    let z ← ($ᵗ F)
    let y ← ($ᵗ F)
    let b' ← adv.distinguish x.2.2
      (y • g, hash hk (z • g) + if b then x.1 else x.2.1)
    pure (b == b')
  have hleft :
      Pr[= true | ddhExpRand g (ddhReduction (F := F) (hash := hash) adv)] =
      Pr[= true | canonical] := by
    trans Pr[= true | do
      let a ← ($ᵗ F)
      let z ← ($ᵗ F)
      let hk ← ($ᵗ HK)
      let x ← adv.chooseMessages (hk, a • g)
      let b ← ($ᵗ Bool)
      let y ← ($ᵗ F)
      let b' ← adv.distinguish x.2.2
        (y • g, hash hk (z • g) + if b then x.1 else x.2.1)
      pure (b == b')]
    · simpa [ddhExpRand, ddhReduction, bind_assoc, map_eq_bind_pure_comp] using
        (probOutput_bind_congr' ($ᵗ F) true (fun a => by
          simpa [bind_assoc, map_eq_bind_pure_comp] using
            (probOutput_bind_bind_swap
              ($ᵗ F)
              (do
                let z ← ($ᵗ F)
                let hk ← ($ᵗ HK)
                let x ← adv.chooseMessages (hk, a • g)
                let b ← ($ᵗ Bool)
                pure (z, hk, x, b))
              (fun y ⟨z, hk, x, b⟩ => do
                let b' ← adv.distinguish x.2.2
                  (y • g, hash hk (z • g) + if b then x.1 else x.2.1)
                pure (b == b'))
              true)))
    · trans Pr[= true | do
          let a ← ($ᵗ F)
          let hk ← ($ᵗ HK)
          let x ← adv.chooseMessages (hk, a • g)
          let b ← ($ᵗ Bool)
          let z ← ($ᵗ F)
          let y ← ($ᵗ F)
          let b' ← adv.distinguish x.2.2
            (y • g, hash hk (z • g) + if b then x.1 else x.2.1)
          pure (b == b')]
      · simpa [bind_assoc, map_eq_bind_pure_comp] using
          (probOutput_bind_congr' ($ᵗ F) true (fun a => by
            simpa [bind_assoc, map_eq_bind_pure_comp] using
              (probOutput_bind_bind_swap
                ($ᵗ F)
                (do
                  let hk ← ($ᵗ HK)
                  let x ← adv.chooseMessages (hk, a • g)
                  let b ← ($ᵗ Bool)
                  pure (hk, x, b))
                (fun z ⟨hk, x, b⟩ => do
                  let y ← ($ᵗ F)
                  let b' ← adv.distinguish x.2.2
                    (y • g, hash hk (z • g) + if b then x.1 else x.2.1)
                  pure (b == b'))
                true)))
      · simpa [canonical, bind_assoc, map_eq_bind_pure_comp] using
          (probOutput_bind_bind_swap
            ($ᵗ F)
            ($ᵗ HK)
            (fun a hk => do
              let x ← adv.chooseMessages (hk, a • g)
              let b ← ($ᵗ Bool)
              let z ← ($ᵗ F)
              let y ← ($ᵗ F)
              let b' ← adv.distinguish x.2.2
                (y • g, hash hk (z • g) + if b then x.1 else x.2.1)
              pure (b == b'))
            true)
  have hright :
      Pr[= true | EntropySmoothing.realExp F g hash (esReduction (F := F) (g := g) adv)] =
      Pr[= true | canonical] := by
    refine probOutput_bind_congr' ($ᵗ HK) true ?_
    intro hk
    simpa [EntropySmoothing.realExp, esReduction, canonical, bind_assoc,
      map_eq_bind_pure_comp] using
      (probOutput_bind_bind_swap
        ($ᵗ F)
        (do
          let a ← ($ᵗ F)
          let x ← adv.chooseMessages (hk, a • g)
          let b ← ($ᵗ Bool)
          pure (a, x, b))
        (fun z ⟨a, x, b⟩ => do
          let y ← ($ᵗ F)
          let b' ← adv.distinguish x.2.2
            (y • g, hash hk (z • g) + if b then x.1 else x.2.1)
          pure (b == b'))
        true)
  exact hleft.trans hright.symm
omit [DecidableEq G] [DecidableEq M] in
/-- ES ideal experiment: the ciphertext `v + m_b` with uniform `v` is uniform
regardless of `b`, so the game reduces to random guessing.
Uses the same uniform-masking principle as the one-time pad. -/
theorem esIdeal_eq_half
    (adv : AsymmEncAlg.IND_CPA_Adv (hashedElGamal F g hash)) :
    Pr[= true | EntropySmoothing.idealExp (esReduction (F := F) (g := g) adv)] = 1 / 2 := by
  let inner : HK → ProbComp Bool := fun hk => do
    let h ← ($ᵗ M)
    let sk ← ($ᵗ F)
    let (m₁, m₂, st) ← adv.chooseMessages (hk, sk • g)
    let b ← ($ᵗ Bool)
    let y ← ($ᵗ F)
    let b' ← adv.distinguish st (y • g, h + if b then m₁ else m₂)
    pure (decide (b = b'))
  let f : HK → Bool → ProbComp Bool := fun hk b => do
    let sk ← ($ᵗ F)
    let (m₁, m₂, st) ← adv.chooseMessages (hk, sk • g)
    let y ← ($ᵗ F)
    let h ← ($ᵗ M)
    adv.distinguish st (y • g, h + if b then m₁ else m₂)
  have hf : ∀ hk, evalDist (f hk true) = evalDist (f hk false) := by
    intro hk
    unfold f
    rw [evalDist_bind, evalDist_bind]
    congr 1
    funext sk
    rw [evalDist_bind, evalDist_bind]
    congr 1
    funext x
    rcases x with ⟨m₁, m₂, st⟩
    rw [evalDist_bind, evalDist_bind]
    congr 1
    funext y
    simpa [add_comm, add_left_comm, add_assoc] using
      ElGamalExamples.uniformMaskedCipher_bind_dist_indep
        (head := y • g) (m₁ := m₁) (m₂ := m₂) (cont := adv.distinguish st)
  have hrepr : ∀ hk,
      Pr[= true | inner hk] =
        Pr[= true | do
          let b ← ($ᵗ Bool)
          let b' ← f hk b
          pure (decide (b = b'))] := by
    intro hk
    trans Pr[= true | do
      let sk ← ($ᵗ F)
      let x ← adv.chooseMessages (hk, sk • g)
      let b ← ($ᵗ Bool)
      let y ← ($ᵗ F)
      let h ← ($ᵗ M)
      let b' ← adv.distinguish x.2.2 (y • g, h + if b then x.1 else x.2.1)
      pure (decide (b = b'))]
    · simpa [inner, bind_assoc, map_eq_bind_pure_comp] using
        (probOutput_bind_bind_swap
          ($ᵗ M)
          (do
            let sk ← ($ᵗ F)
            let x ← adv.chooseMessages (hk, sk • g)
            let b ← ($ᵗ Bool)
            let y ← ($ᵗ F)
            pure (sk, x, b, y))
          (fun h ⟨_sk, x, b, y⟩ => do
            let b' ← adv.distinguish x.2.2 (y • g, h + if b then x.1 else x.2.1)
            pure (decide (b = b')))
          true)
    · trans Pr[= true | do
          let b ← ($ᵗ Bool)
          let b' ← f hk b
          pure (decide (b = b'))]
      · simpa [f, bind_assoc, map_eq_bind_pure_comp] using
          (probOutput_bind_bind_swap
            (do
              let sk ← ($ᵗ F)
              let x ← adv.chooseMessages (hk, sk • g)
              pure (sk, x))
            ($ᵗ Bool)
            (fun ⟨_sk, x⟩ b => do
              let y ← ($ᵗ F)
              let h ← ($ᵗ M)
              let b' ← adv.distinguish x.2.2 (y • g, h + if b then x.1 else x.2.1)
              pure (decide (b = b')))
            true)
      · rfl
  have hhalf : ∀ hk, Pr[= true | inner hk] = 1 / 2 := by
    intro hk
    rw [hrepr hk]
    exact probOutput_decide_eq_uniformBool_half (f hk) (hf hk)
  calc
    Pr[= true | EntropySmoothing.idealExp (esReduction (F := F) (g := g) adv)] =
        Pr[= true | do
          let hk ← ($ᵗ HK)
          inner hk] := by
      simp [EntropySmoothing.idealExp, esReduction,
        show ∀ a b : Bool, (a == b) = decide (a = b) from by decide,
        inner]
    _ = Pr[= true | do
          let hk ← ($ᵗ HK)
          ($ᵗ Bool)] :=
      probOutput_bind_congr' ($ᵗ HK) true (fun hk => by
        simpa [probOutput_uniformSample] using hhalf hk)
    _ = 1 / 2 := by
      rw [probOutput_bind_eq_tsum]
      have hbool : Pr[= true | ($ᵗ Bool)] = (1 / 2 : ℝ≥0∞) := by
        simp [probOutput_uniformSample]
      simp_rw [hbool]
      have hsum : ∑' x : HK, Pr[= x | ($ᵗ HK)] = 1 :=
        HasEvalPMF.tsum_probOutput_eq_one ($ᵗ HK)
      rw [ENNReal.tsum_mul_right, hsum, one_mul]

/-! ## Main theorem -/

omit [DecidableEq G] [DecidableEq M] in
/-- **Main theorem.** The one-time IND-CPA bias of hashed ElGamal is bounded by
the DDH distinguishing advantage plus the entropy smoothing advantage:

`|Pr[CPA wins] - 1/2| ≤ ddhDistAdvantage(D) + EntropySmoothing.advantage(E)`

where `D` is the DDH reduction and `E` is the ES reduction, both constructed
from the CPA adversary. -/
theorem hashedElGamal_IND_CPA_bound
    (adv : AsymmEncAlg.IND_CPA_Adv (hashedElGamal F g hash)) :
    |(Pr[= true | AsymmEncAlg.IND_CPA_OneTime_Game_ProbComp
      (encAlg := hashedElGamal F g hash) adv]).toReal - 1 / 2| ≤
      ddhDistAdvantage g (ddhReduction (F := F) (hash := hash) adv) +
      EntropySmoothing.advantage F g hash (esReduction (F := F) (g := g) adv) := by
  rw [cpaGame_eq_ddhReal (F := F) (g := g) (hash := hash)]
  rw [ddhDistAdvantage, EntropySmoothing.advantage]
  have hesHalf :=
    esIdeal_eq_half (F := F) (g := g) (hash := hash) adv
  have hddhEs :
      |(Pr[= true | ddhExpReal g (ddhReduction (F := F) (hash := hash) adv)]).toReal - 1 / 2| =
        |(Pr[= true | ddhExpReal g (ddhReduction (F := F) (hash := hash) adv)]).toReal -
          (Pr[= true | EntropySmoothing.idealExp (esReduction (F := F) (g := g) adv)]).toReal| := by
    rw [hesHalf, ENNReal.toReal_div]
    simp
  rw [hddhEs]
  have hreal :
      (Pr[= true | ddhExpRand g (ddhReduction (F := F) (hash := hash) adv)]).toReal =
        (Pr[= true |
          EntropySmoothing.realExp F g hash (esReduction (F := F) (g := g) adv)]).toReal := by
    congr 1
    exact ddhRand_eq_esReal (F := F) (g := g) (hash := hash) adv
  calc
    |(Pr[= true | ddhExpReal g (ddhReduction (F := F) (hash := hash) adv)]).toReal -
        (Pr[= true | EntropySmoothing.idealExp (esReduction (F := F) (g := g) adv)]).toReal| ≤
      |(Pr[= true | ddhExpReal g (ddhReduction (F := F) (hash := hash) adv)]).toReal -
          (Pr[= true | ddhExpRand g (ddhReduction (F := F) (hash := hash) adv)]).toReal| +
        |(Pr[= true | ddhExpRand g (ddhReduction (F := F) (hash := hash) adv)]).toReal -
          (Pr[= true | EntropySmoothing.idealExp (esReduction (F := F) (g := g) adv)]).toReal| :=
      abs_sub_le _ _ _
    _ = ddhDistAdvantage g (ddhReduction (F := F) (hash := hash) adv) +
        |(Pr[= true |
          EntropySmoothing.realExp F g hash (esReduction (F := F) (g := g) adv)]).toReal -
          (Pr[= true | EntropySmoothing.idealExp (esReduction (F := F) (g := g) adv)]).toReal| := by
      rw [ddhDistAdvantage]
      congr 1
      rw [hreal]
    _ = ddhDistAdvantage g (ddhReduction (F := F) (hash := hash) adv) +
        EntropySmoothing.advantage F g hash (esReduction (F := F) (g := g) adv) := by
      rw [EntropySmoothing.advantage]

end Security

end hashedElGamal
