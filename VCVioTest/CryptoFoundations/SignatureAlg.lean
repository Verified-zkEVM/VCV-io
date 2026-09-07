/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module
public import VCVio.CryptoFoundations.SignatureAlg

/-!
# Signature security-game canaries

Executable symbolic canaries for the generic SUF-CMA endpoint. The toy scheme deliberately has
two valid signatures for each message, while honest signing returns only one of them. This makes
the distinction between message freshness and exact returned-pair freshness observable.
-/

@[expose] public section

open OracleComp OracleSpec

namespace SignatureAlgTest

/-- The toy signature records the message in its first bit and has an ignored rerandomization
bit. Both values of the second bit verify. -/
abbrev ToySignature := Bool × Bool

/-- A deterministic scheme with two valid signatures per message. Honest signing uses
rerandomization bit `false`. -/
def twoSignatureAlg : SignatureAlg ProbComp Bool Unit Unit ToySignature where
  keygen := pure ((), ())
  sign _ _ msg := pure (msg, false)
  verify _ msg σ := pure (σ.1 == msg)

/-- Query one signature and replay the exact pair. -/
def replayAdv : SignatureAlg.strongUnforgeableAdv twoSignatureAlg where
  main _ := do
    let σ ← (unifSpec + (Bool →ₒ ToySignature)).query (Sum.inr false)
    return (false, σ)

/-- Query a signature, then flip its ignored rerandomization bit. -/
def rerandomizeAdv : SignatureAlg.strongUnforgeableAdv twoSignatureAlg where
  main _ := do
    let _ ← (unifSpec + (Bool →ₒ ToySignature)).query (Sum.inr false)
    return (false, (false, true))

/-- Forge directly on a fresh message without calling the signing oracle. -/
def freshMessageAdv : SignatureAlg.strongUnforgeableAdv twoSignatureAlg where
  main _ := pure (true, (true, true))

/-- Return a fresh-message pair whose signature encodes the wrong message. -/
def invalidFreshMessageAdv : SignatureAlg.strongUnforgeableAdv twoSignatureAlg where
  main _ := pure (true, (false, true))

/-- Query one message, then return a fresh pair for that message whose signature encodes the
other message. This reaches the same-message branch but must still fail verification. -/
def invalidSameMessageAdv : SignatureAlg.strongUnforgeableAdv twoSignatureAlg where
  main _ := do
    let _ ← (unifSpec + (Bool →ₒ ToySignature)).query (Sum.inr false)
    return (false, (true, true))

/-- Replaying an exact signing-oracle response loses SUF-CMA. -/
example :
    SignatureAlg.strongUnforgeableExp ProbCompRuntime.probComp replayAdv {true} = 0 := by
  simp [SignatureAlg.strongUnforgeableExp, SignatureAlg.strongUnforgeableGame,
    replayAdv, twoSignatureAlg,
    SignatureAlg.signingOracle, SignatureAlg.signingLogContains,
    ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

/-- A different valid signature on an already queried message is an eligible strong forgery. -/
example :
    SignatureAlg.strongUnforgeableExp ProbCompRuntime.probComp rerandomizeAdv {true} = 1 := by
  simp [SignatureAlg.strongUnforgeableExp, SignatureAlg.strongUnforgeableGame,
    rerandomizeAdv, twoSignatureAlg,
    SignatureAlg.signingOracle, SignatureAlg.signingLogContains,
    ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

/-- A valid signature on a fresh message wins exactly as in the ordinary unforgeability game. -/
example :
    SignatureAlg.strongUnforgeableExp ProbCompRuntime.probComp freshMessageAdv {true} = 1 := by
  simp [SignatureAlg.strongUnforgeableExp, SignatureAlg.strongUnforgeableGame,
    freshMessageAdv, twoSignatureAlg,
    SignatureAlg.signingOracle, SignatureAlg.signingLogContains,
    ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

/-- The ENNReal advantage endpoint assigns zero to replay and one to the two valid fresh-pair
forgeries in this deterministic scheme. -/
example : replayAdv.advantage ProbCompRuntime.probComp = 0 ∧
    rerandomizeAdv.advantage ProbCompRuntime.probComp = 1 ∧
    freshMessageAdv.advantage ProbCompRuntime.probComp = 1 := by
  simp [SignatureAlg.strongUnforgeableAdv.advantage,
    SignatureAlg.strongUnforgeableExp, SignatureAlg.strongUnforgeableGame,
    replayAdv, rerandomizeAdv, freshMessageAdv,
    twoSignatureAlg, SignatureAlg.signingOracle, SignatureAlg.signingLogContains,
    ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

/-- Exact-pair freshness alone is insufficient: an invalid fresh-message signature loses. -/
example :
    SignatureAlg.strongUnforgeableExp ProbCompRuntime.probComp
        invalidFreshMessageAdv {true} = 0 := by
  simp [SignatureAlg.strongUnforgeableExp, SignatureAlg.strongUnforgeableGame,
    invalidFreshMessageAdv, twoSignatureAlg,
    SignatureAlg.signingOracle, SignatureAlg.signingLogContains,
    ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

/-- Exact replay is excluded from the same-message residual as well as from SUF itself. This
pins exact-pair freshness independently in the residual experiment and its advantage endpoint. -/
example :
    SignatureAlg.sameMessageStrongUnforgeableExp ProbCompRuntime.probComp replayAdv {true} = 0 ∧
      replayAdv.sameMessageAdvantage ProbCompRuntime.probComp = 0 := by
  simp [SignatureAlg.strongUnforgeableAdv.sameMessageAdvantage,
    SignatureAlg.sameMessageStrongUnforgeableExp, replayAdv, twoSignatureAlg,
    SignatureAlg.sameMessageStrongUnforgeableGame,
    SignatureAlg.signingOracle, SignatureAlg.signingLogContains,
    ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

/-- The same-message residual requires verification: a new but invalid pair has probability
zero even after the message was submitted to the signing oracle. -/
example :
    SignatureAlg.sameMessageStrongUnforgeableExp ProbCompRuntime.probComp
        invalidSameMessageAdv {true} = 0 := by
  simp [SignatureAlg.sameMessageStrongUnforgeableExp,
    SignatureAlg.sameMessageStrongUnforgeableGame,
    invalidSameMessageAdv, twoSignatureAlg,
    SignatureAlg.signingOracle, SignatureAlg.signingLogContains,
    ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

/-- The SUF partition is exact on the two qualitatively different forgery branches: rerandomizing
an already signed message contributes only to the same-message term, while a fresh-message
forgery contributes only to EUF. -/
example :
    rerandomizeAdv.toUnforgeableAdv.advantage ProbCompRuntime.probComp = 0 ∧
      rerandomizeAdv.sameMessageAdvantage ProbCompRuntime.probComp = 1 ∧
      freshMessageAdv.toUnforgeableAdv.advantage ProbCompRuntime.probComp = 1 ∧
      freshMessageAdv.sameMessageAdvantage ProbCompRuntime.probComp = 0 := by
  simp [SignatureAlg.unforgeableAdv.advantage, SignatureAlg.unforgeableExp,
    SignatureAlg.strongUnforgeableAdv.sameMessageAdvantage,
    SignatureAlg.sameMessageStrongUnforgeableExp,
    SignatureAlg.sameMessageStrongUnforgeableGame,
    SignatureAlg.strongUnforgeableAdv.toUnforgeableAdv,
    rerandomizeAdv, freshMessageAdv, twoSignatureAlg, SignatureAlg.signingOracle,
    SignatureAlg.signingLogContains, QueryLog.wasQueried,
    ProbCompRuntime.evalSPMF, ProbCompRuntime.probComp]

/-- Direct executable-runtime consumer of the public exact SUF partition, discharging the
pull-through hypothesis with the library-level `ProbCompRuntime.probComp_evalSPMF_bind_pure`. -/
example (adv : SignatureAlg.strongUnforgeableAdv twoSignatureAlg) :
    adv.advantage ProbCompRuntime.probComp =
      adv.toUnforgeableAdv.advantage ProbCompRuntime.probComp +
        adv.sameMessageAdvantage ProbCompRuntime.probComp :=
  adv.advantage_eq_euf_add_sameMessage ProbCompRuntime.probComp
    ProbCompRuntime.probComp_evalSPMF_bind_pure

/-- The toy scheme satisfies the vacuous unit upper bound for the same-message residual. -/
private lemma twoSignatureBinding :
    twoSignatureAlg.SameMessageBinding ProbCompRuntime.probComp 1 := by
  intro adv
  unfold SignatureAlg.strongUnforgeableAdv.sameMessageAdvantage
    SignatureAlg.sameMessageStrongUnforgeableExp
  exact (MeasureTheory.measure_mono (Set.subset_univ {true})).trans
    (SPMF.toMeasure_apply_univ_le_one _)

/-- Direct consumer of the quantitative `SameMessageBinding` packaging. -/
example (adv : SignatureAlg.strongUnforgeableAdv twoSignatureAlg) :
    adv.advantage ProbCompRuntime.probComp ≤
      adv.toUnforgeableAdv.advantage ProbCompRuntime.probComp + 1 :=
  adv.advantage_le_euf_add_of_sameMessageBinding ProbCompRuntime.probComp
    ProbCompRuntime.probComp_evalSPMF_bind_pure twoSignatureBinding

end SignatureAlgTest
