/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.QueryTracking.CachingOracle

/-!
# Asymmetric Encryption Schemes.

This file defines a type `AsymmEncAlg spec M PK SK C` to represent an protocol
for asymmetric encryption using oracles in `spec`, with message space `M`,
public/secret keys `PK` and `SK`, and ciphertext space `C`.
-/

open OracleSpec OracleComp ENNReal

universe u v w

/-- An `AsymmEncAlg` with message space `M`, key spaces `PK` and `SK`, and ciphertexts in `C`.
`spec` is the available oracle set and `m` is the monad used to execute the oracle calls.
Extends `ExecutionMethod spec m`, in most cases will be `ExecutionMethod.default`. -/
structure AsymmEncAlg (m : Type → Type u) (M PK SK C : Type)
    extends ExecutionMethod m where
  keygen : m (PK × SK)
  encrypt : (pk : PK) → (msg : M) →  m C
  decrypt : (sk : SK) → (c : C) →  m (Option M)

alias PKE_Alg := AsymmEncAlg

namespace AsymmEncAlg

variable {m : Type → Type v} {M PK SK C : Type}
  (encAlg : AsymmEncAlg m M PK SK C)

section Correct

variable [DecidableEq M] [Monad m]

/-- Correctness experiment: returns `true` iff decrypting the ciphertext recovers the message.

The old version used `guard` (requiring `AlternativeMonad`); we return `Bool` instead since
`guard` now requires `OptionT` in the current API. -/
def CorrectExp (msg : M) : m Bool := do
  let (pk, sk) ← encAlg.keygen
  let c ← encAlg.encrypt pk msg
  let msg' ← encAlg.decrypt sk c
  return decide (msg' = some msg)

def PerfectlyCorrect [HasEvalSPMF m] : Prop :=
  ∀ (msg : M), Pr[= true | encAlg.exec (encAlg.CorrectExp msg)] = 1

end Correct

section IND_CPA_Oracle

variable [DecidableEq M] [DecidableEq C]

/-- Oracle-based multi-query IND-CPA game. The adversary gets oracle access to an encryption
oracle that encrypts one of two challenge messages depending on a hidden bit.

API changes from old version:
- `unifSpec ++ₒ` → `unifSpec +`
- `⟨fun (query () (m₁, m₂)) => ...⟩` → `fun (m₁, m₂) => ...`
- `idOracle ++ₛₒ` → `QueryImpl.ofLift ... .liftTarget ... +`
- `guard (b = b')` → `return (b == b')` (Bool-valued experiment) -/

def IND_CPA_oracleSpec (_encAlg : AsymmEncAlg ProbComp M PK SK C) :=
  unifSpec + (M × M →ₒ C)

def IND_CPA_adversary (encAlg : AsymmEncAlg ProbComp M PK SK C) :=
  PK → OracleComp encAlg.IND_CPA_oracleSpec Bool

/-- An IND-CPA adversary `MakesAtMostQueries q` when it issues at most `q` total queries
to the challenge (encryption) oracle, regardless of public key.
Uniform-sampling queries are unrestricted. -/
def IND_CPA_adversary.MakesAtMostQueries {encAlg : AsymmEncAlg ProbComp M PK SK C}
    (adversary : encAlg.IND_CPA_adversary) (q : ℕ) : Prop :=
  ∀ pk, (adversary pk).IsQueryBound q
    (fun t n => match t with | .inl _ => True | .inr _ => 0 < n)
    (fun t n => match t with | .inl _ => n | .inr _ => n - 1)

def IND_CPA_queryImpl' (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (pk : PK) (b : Bool) : QueryImpl encAlg.IND_CPA_oracleSpec
      (StateT ((M × M →ₒ C).QueryCache) ProbComp) :=
  have so : QueryImpl (M × M →ₒ C) ProbComp := fun (m₁, m₂) =>
    encAlg.encrypt pk (if b then m₁ else m₂)
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT ((M × M →ₒ C).QueryCache) ProbComp) + so.withCaching

def IND_CPA_queryImpl (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (pk : PK) (b : Bool) : QueryImpl encAlg.IND_CPA_oracleSpec
      (StateT ((M × M →ₒ C).QueryCache) ProbComp) :=
  have so : QueryImpl (M × M →ₒ C) ProbComp := fun (m₁, m₂) =>
    encAlg.encrypt pk (if b then m₁ else m₂)
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT ((M × M →ₒ C).QueryCache) ProbComp) +
    so.liftTarget (StateT ((M × M →ₒ C).QueryCache) ProbComp)

def IND_CPA_experiment {encAlg : AsymmEncAlg ProbComp M PK SK C}
    (adversary : encAlg.IND_CPA_adversary) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (pk, _sk) ← encAlg.keygen
  let b' ← (simulateQ (encAlg.IND_CPA_queryImpl' pk b) (adversary pk)).run' ∅
  return (b == b')

noncomputable def IND_CPA_advantage {encAlg : AsymmEncAlg ProbComp M PK SK C}
    (adversary : encAlg.IND_CPA_adversary) : ℝ≥0∞ :=
  Pr[= true | IND_CPA_experiment adversary] - 1 / 2

end IND_CPA_Oracle

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

noncomputable def IND_CCA_Advantage {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
    (adversary : encAlg.IND_CCA_Adversary) : ℝ :=
  (IND_CCA_Game adversary).boolBiasAdvantage

end IND_CCA

section IND_CPA_TwoPhase

variable {ι : Type} {spec : OracleSpec ι} [DecidableEq M] [DecidableEq C]

/-- Two-phase adversary for IND-CPA security.
Removed `AlternativeMonad`/`LawfulAlternative` requirements (not available in current API). -/
structure IND_CPA_Adv (encAlg : AsymmEncAlg m M PK SK C) where
  State : Type
  chooseMessages : PK → m (M × M × State)
  distinguish : State → C → m Bool

variable {encAlg : AsymmEncAlg (OracleComp spec) M PK SK C}
  (adv : IND_CPA_Adv encAlg)

/--
Experiment for *one-time* IND-CPA security of an asymmetric encryption algorithm:
1. Run `keygen` to get a public key and a private key.
2. Run `adv.chooseMessages` on `pk` to get a pair of messages and a private state.
3. The challenger then tosses a coin and encrypts one of the messages, returning the ciphertext `c`.
4. Run `adv.distinguish` on the private state and the ciphertext to get a boolean.
5. Return a Boolean indicating whether the adversary's guess is correct.

Note: we do _not_ want to end with a `guard` statement, as this can be biased by the adversary
potentially always failing.
-/
def IND_CPA_OneTime_Game : ProbComp Bool :=
  encAlg.exec do
    let b : Bool ← encAlg.lift_probComp ($ᵗ Bool)
    let (pk, _) ← encAlg.keygen
    let (m₁, m₂, state) ← adv.chooseMessages pk
    let msg := if b then m₁ else m₂
    let c ← encAlg.encrypt pk msg
    let b' ← adv.distinguish state c
    return (b == b')

noncomputable def IND_CPA_OneTime_Advantage (encAlg : AsymmEncAlg (OracleComp spec) M PK SK C)
    (adv : IND_CPA_Adv encAlg) : ℝ :=
  (IND_CPA_OneTime_Game (encAlg := encAlg) adv).boolBiasAdvantage

section OracleLift

variable {encAlg' : AsymmEncAlg ProbComp M PK SK C}

/-- One-time IND-CPA game specialized to `ProbComp` execution (no extra `exec` wrapper). This is
the canonical target for generic one-query lifts into the oracle IND-CPA interface. -/
def IND_CPA_OneTime_Game_ProbComp (adv : IND_CPA_Adv encAlg') : ProbComp Bool := do
  let b ← $ᵗ Bool
  let (pk, _) ← encAlg'.keygen
  let (m₁, m₂, state) ← adv.chooseMessages pk
  let msg := if b then m₁ else m₂
  let c ← encAlg'.encrypt pk msg
  let b' ← adv.distinguish state c
  return (b == b')

/-- Embed a two-phase one-time adversary into the oracle IND-CPA interface by issuing exactly
one challenge query. This construction is scheme-agnostic. -/
def IND_CPA_adversary_of_OneTime_raw (adv : IND_CPA_Adv encAlg') :
    PK → OracleComp (unifSpec + (M × M →ₒ C)) Bool := fun pk => do
  let (m₁, m₂, st) ←
    (OracleComp.liftComp (spec := unifSpec)
      (superSpec := unifSpec + (M × M →ₒ C))
      (adv.chooseMessages pk))
  let c ← query (spec := unifSpec + (M × M →ₒ C)) (Sum.inr (m₁, m₂))
  OracleComp.liftComp (spec := unifSpec)
    (superSpec := unifSpec + (M × M →ₒ C))
    (adv.distinguish st c)

/-- Embed a two-phase one-time adversary into the oracle IND-CPA interface by issuing exactly
one challenge query. This construction is scheme-agnostic. -/
def IND_CPA_adversary_of_OneTime (adv : IND_CPA_Adv encAlg') :
    encAlg'.IND_CPA_adversary := by
  simpa [IND_CPA_adversary, IND_CPA_oracleSpec] using
    (IND_CPA_adversary_of_OneTime_raw (encAlg' := encAlg') adv)

/-- Main proof obligation for a one-query lift: the oracle IND-CPA game with the embedded
one-time adversary is equal to the direct one-time ProbComp game. -/
abbrev IND_CPA_experiment_adversary_of_OneTime_eq_oneTimeGameObligation
    [DecidableEq M] [DecidableEq C] (adv : IND_CPA_Adv encAlg') : Prop :=
  IND_CPA_experiment (encAlg := encAlg') (IND_CPA_adversary_of_OneTime (encAlg' := encAlg') adv) =
    IND_CPA_OneTime_Game_ProbComp (encAlg' := encAlg') adv

/-- `ℝ≥0∞` one-time signed IND-CPA advantage, aligned with `IND_CPA_advantage`. -/
noncomputable def IND_CPA_OneTime_AdvantageENN (encAlg : AsymmEncAlg ProbComp M PK SK C)
    (adv : IND_CPA_Adv encAlg) : ℝ≥0∞ :=
  Pr[= true | IND_CPA_OneTime_Game_ProbComp (encAlg' := encAlg) adv] - 1 / 2

omit [DecidableEq M] [DecidableEq C] in
/-- Generic advantage equality for adversaries obtained from the one-query embedding,
once the game-equivalence obligation is discharged. -/
theorem IND_CPA_advantage_adversary_of_OneTime_eq_oneTimeAdvantageENN_of_obligation
    [DecidableEq M] [DecidableEq C]
    (adv : IND_CPA_Adv encAlg') :
    IND_CPA_experiment_adversary_of_OneTime_eq_oneTimeGameObligation
      (encAlg' := encAlg') adv →
    IND_CPA_advantage (encAlg := encAlg') (IND_CPA_adversary_of_OneTime (encAlg' := encAlg') adv) =
      IND_CPA_OneTime_AdvantageENN (encAlg := encAlg') adv := by
  intro hgame
  unfold IND_CPA_advantage IND_CPA_OneTime_AdvantageENN
  simpa using congrArg (fun p : ℝ≥0∞ => p - 1 / 2)
    (congrArg (fun g : ProbComp Bool => Pr[= true | g])
      hgame)

/-- Obligation form for reducing an arbitrary oracle IND-CPA adversary to a one-query
two-phase adversary. -/
abbrev IND_CPA_oneQueryFactorizationObligation [DecidableEq M] [DecidableEq C]
    (adversary : encAlg'.IND_CPA_adversary) : Prop :=
  ∃ adv : IND_CPA_Adv encAlg',
    adversary = IND_CPA_adversary_of_OneTime (encAlg' := encAlg') adv ∧
      IND_CPA_experiment_adversary_of_OneTime_eq_oneTimeGameObligation
        (encAlg' := encAlg') adv

omit [DecidableEq M] [DecidableEq C] in
/-- Generic one-query lift: if a multi-query oracle adversary factors through a one-query
two-phase adversary, its IND-CPA advantage is exactly the one-time advantage. -/
theorem IND_CPA_advantage_eq_oneTimeAdvantageENN_of_oneQueryFactorization
    [DecidableEq M] [DecidableEq C]
    (adversary : encAlg'.IND_CPA_adversary)
    (hfactor : IND_CPA_oneQueryFactorizationObligation (encAlg' := encAlg') adversary) :
    ∃ adv : IND_CPA_Adv encAlg',
      IND_CPA_advantage (encAlg := encAlg') adversary =
        IND_CPA_OneTime_AdvantageENN (encAlg := encAlg') adv := by
  rcases hfactor with ⟨adv, rfl, hgame⟩
  exact ⟨adv, IND_CPA_advantage_adversary_of_OneTime_eq_oneTimeAdvantageENN_of_obligation
    (encAlg' := encAlg') adv hgame⟩

end OracleLift

section MultiQueryHybridLift

variable {encAlg' : AsymmEncAlg ProbComp M PK SK C}

/-- Signed real IND-CPA advantage (`Pr[win]-1/2`) for the oracle IND-CPA experiment. -/
noncomputable def IND_CPA_signedAdvantageReal (adversary : encAlg'.IND_CPA_adversary) : ℝ :=
  (Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary]).toReal - 1 / 2

lemma sum_hybridDiff_eq_trueProb_sub (games : ℕ → ProbComp Bool) (q : ℕ) :
    Finset.sum (Finset.range q)
      (fun i => (Pr[= true | games i]).toReal - (Pr[= true | games (i + 1)]).toReal) =
      (Pr[= true | games 0]).toReal - (Pr[= true | games q]).toReal := by
  let f : ℕ → ℝ := fun i => (Pr[= true | games i]).toReal
  have hsub : Finset.sum (Finset.range q) (fun i => f (i + 1)) -
      Finset.sum (Finset.range q) (fun i => f i) = f q - f 0 := by
    simpa [f] using (Finset.sum_range_sub (f := f) q)
  have hneg := congrArg Neg.neg hsub
  calc
    Finset.sum (Finset.range q) (fun i => f i - f (i + 1))
        = -(Finset.sum (Finset.range q) (fun i => f (i + 1)) -
            Finset.sum (Finset.range q) (fun i => f i)) := by
              simp [Finset.sum_sub_distrib]
    _ = -(f q - f 0) := by simpa using hneg
    _ = f 0 - f q := by ring

omit [DecidableEq C] in
/-- Generic telescoping identity for multi-query game-hopping:
if `games 0` is the target IND-CPA experiment and `games q` has success probability `1/2`,
then IND-CPA advantage is the sum of adjacent hybrid differences. -/
theorem IND_CPA_advantage'_eq_sum_hybridDiff
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ) (games : ℕ → ProbComp Bool)
    (h0 : (Pr[= true | games 0]).toReal =
      (Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary]).toReal)
    (hq : (Pr[= true | games q]).toReal = (1 / 2 : ℝ)) :
    IND_CPA_signedAdvantageReal (encAlg' := encAlg') adversary =
      Finset.sum (Finset.range q) (fun i =>
        (Pr[= true | games i]).toReal - (Pr[= true | games (i + 1)]).toReal) := by
  unfold IND_CPA_signedAdvantageReal
  calc
    (Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary]).toReal - 1 / 2
        = (Pr[= true | games 0]).toReal - (Pr[= true | games q]).toReal := by linarith
    _ = Finset.sum (Finset.range q)
          (fun i => (Pr[= true | games i]).toReal -
            (Pr[= true | games (i + 1)]).toReal) := by
          simpa using (sum_hybridDiff_eq_trueProb_sub (games := games) q).symm

omit [DecidableEq C] in
/-- Generic multi-query bound: absolute IND-CPA advantage is at most the sum of absolute
adjacent hybrid gaps. -/
theorem IND_CPA_advantage'_abs_le_sum_hybridDiff_abs
    (adversary : encAlg'.IND_CPA_adversary) (q : ℕ) (games : ℕ → ProbComp Bool)
    (h0 : (Pr[= true | games 0]).toReal =
      (Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary]).toReal)
    (hq : (Pr[= true | games q]).toReal = (1 / 2 : ℝ)) :
    |IND_CPA_signedAdvantageReal (encAlg' := encAlg') adversary| ≤
      Finset.sum (Finset.range q) (fun i =>
        |(Pr[= true | games i]).toReal - (Pr[= true | games (i + 1)]).toReal|) := by
  rw [IND_CPA_advantage'_eq_sum_hybridDiff (encAlg' := encAlg') adversary q games h0 hq]
  simpa using
    (Finset.abs_sum_le_sum_abs
      (s := Finset.range q)
      (f := fun i => (Pr[= true | games i]).toReal -
        (Pr[= true | games (i + 1)]).toReal))

/-- Real bridge for truncated ENNReal subtraction: `(a - b).toReal` is bounded by
`|a.toReal - b.toReal|`. -/
lemma toReal_tsub_le_abs_toReal_sub (a b : ℝ≥0∞) (ha : a ≠ ∞) :
    (a - b).toReal ≤ |a.toReal - b.toReal| := by
  by_cases h : b ≤ a
  · rw [ENNReal.toReal_sub_of_le h ha]
    exact le_abs_self _
  · have h' : a ≤ b := le_of_not_ge h
    rw [tsub_eq_zero_of_le h']
    exact abs_nonneg _

omit [DecidableEq C] in
/-- Compatibility bridge to the existing `IND_CPA_advantage` API:
the `toReal` of ENNReal signed advantage is bounded by absolute signed real advantage. -/
theorem IND_CPA_advantage_toReal_le_abs_signedAdvantageReal
    [DecidableEq C]
    (adversary : encAlg'.IND_CPA_adversary) :
    (IND_CPA_advantage (encAlg := encAlg') adversary).toReal ≤
      |IND_CPA_signedAdvantageReal (encAlg' := encAlg') adversary| := by
  unfold IND_CPA_advantage IND_CPA_signedAdvantageReal
  simpa using
    (toReal_tsub_le_abs_toReal_sub
      (a := Pr[= true | IND_CPA_experiment (encAlg := encAlg') adversary])
      (b := (1 / 2 : ℝ≥0∞))
      (ha := probOutput_ne_top))

end MultiQueryHybridLift

end IND_CPA_TwoPhase

end AsymmEncAlg
