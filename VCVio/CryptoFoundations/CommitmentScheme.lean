/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.Constructions.SampleableType

/-!
# Commitment Schemes

This file defines non-interactive commitment schemes and their standard security
properties: correctness, hiding, and binding.

## Main Definitions

- `CommitmentScheme PP M C D` — a commitment scheme with public parameters `PP`,
  message space `M`, commitment space `C`, and opening (decommitment) space `D`.
- `CommitmentScheme.PerfectlyCorrect` — honestly generated parameters and commitments always verify.
- `CommitmentScheme.PerfectlyHiding` — under honestly generated parameters, commitment
  distribution is independent of the message.
- `CommitmentScheme.hidingExp` — computational hiding experiment (IND-style).
- `CommitmentScheme.bindingExp` — computational binding experiment.
- `TrapdoorExtractor PP TD C M` — trapdoor-based message extraction algorithm.
- `CommitmentScheme.extractExp` — extraction experiment (game-based, allows error).
-/

set_option autoImplicit false

open OracleComp OracleSpec ENNReal

/-- A non-interactive commitment scheme with public parameters `PP`, message space `M`,
commitment space `C`, and opening (decommitment) space `D`. -/
structure CommitmentScheme (PP M C D : Type) where
  /-- Generate public parameters (e.g. a common reference string). -/
  setup : ProbComp PP
  /-- Commit to a message, producing a commitment and an opening. -/
  commit (pp : PP) (m : M) : ProbComp (C × D)
  /-- Deterministic verification that an opening is valid. -/
  verify (pp : PP) (m : M) (c : C) (d : D) : Bool

namespace CommitmentScheme

variable {PP M C D : Type}

/-- A commitment scheme is perfectly correct if every honestly generated public
parameter and commitment-opening pair passes verification. -/
def PerfectlyCorrect (cs : CommitmentScheme PP M C D) : Prop :=
  ∀ pp, pp ∈ support cs.setup →
    ∀ m cd, cd ∈ support (cs.commit pp m) → cs.verify pp m cd.1 cd.2 = true

/-- A commitment scheme is perfectly hiding if, for every honestly generated
public parameter, the commitment (first component) has the same distribution
regardless of the committed message. -/
def PerfectlyHiding (cs : CommitmentScheme PP M C D) : Prop :=
  ∀ pp, pp ∈ support cs.setup →
    ∀ m₁ m₂, evalDist (Prod.fst <$> cs.commit pp m₁) =
      evalDist (Prod.fst <$> cs.commit pp m₂)

/-! ### Computational hiding -/

/-- A two-phase hiding adversary: phase 1 chooses two messages given the public parameters;
phase 2 receives the commitment and tries to guess which message was committed.
`State` carries information between the two phases. -/
structure HidingAdv (PP M C : Type) where
  State : Type
  chooseMessages : PP → ProbComp (M × M × State)
  distinguish : State → C → ProbComp Bool

/-- Hiding experiment: the adversary chooses two messages, the challenger commits
to one at random, and the adversary tries to guess which. -/
def hidingExp (cs : CommitmentScheme PP M C D) (adversary : HidingAdv PP M C) :
    ProbComp Bool := do
  let pp ← cs.setup
  let (m₁, m₂, st) ← adversary.chooseMessages pp
  let b ← $ᵗ Bool
  let (c, _) ← cs.commit pp (if b then m₁ else m₂)
  let b' ← adversary.distinguish st c
  return (b == b')

noncomputable def hidingAdvantage (cs : CommitmentScheme PP M C D)
    (adversary : HidingAdv PP M C) : ℝ :=
  |(Pr[= true | cs.hidingExp adversary]).toReal - 1 / 2|

/-! ### Computational binding -/

/-- A binding adversary outputs a commitment with two openings to different messages. -/
def BindingAdv (PP M C D : Type) := PP → ProbComp (C × M × D × M × D)

/-- Binding experiment: the adversary tries to open a single commitment to two
distinct messages. Succeeds iff both openings verify and the messages differ. -/
def bindingExp [DecidableEq M] (cs : CommitmentScheme PP M C D)
    (adversary : BindingAdv PP M C D) : ProbComp Bool := do
  let pp ← cs.setup
  let (c, m₁, d₁, m₂, d₂) ← adversary pp
  return (decide (m₁ ≠ m₂) && cs.verify pp m₁ c d₁ && cs.verify pp m₂ c d₂)

noncomputable def bindingAdvantage [DecidableEq M] (cs : CommitmentScheme PP M C D)
    (adversary : BindingAdv PP M C D) : ℝ≥0∞ :=
  Pr[= true | cs.bindingExp adversary]

/-! ### Trapdoor extractability -/

/-- A trapdoor extractor for a commitment scheme: bundles an alternative setup
that produces a trapdoor alongside the public parameters, and a (potentially
probabilistic) extraction algorithm that recovers the committed message from
the commitment using the trapdoor.

Named `TrapdoorExtractor` specifically to leave room for other extraction
paradigms (e.g. rewinding-based extraction). -/
structure TrapdoorExtractor (PP TD C M : Type) where
  setupExtract : ProbComp (PP × TD)
  extract : TD → C → ProbComp M

/-- The extraction setup produces the same public parameter distribution as
the scheme's normal setup. Required for reductions that swap in the
trapdoor setup without the adversary noticing. -/
def TrapdoorExtractor.SetupConsistent {TD : Type}
    (extractor : TrapdoorExtractor PP TD C M)
    (cs : CommitmentScheme PP M C D) : Prop :=
  evalDist (Prod.fst <$> extractor.setupExtract) = evalDist cs.setup

/-- Extraction experiment: generate parameters with trapdoor, honestly commit
to message `m`, then check whether the extractor recovers `m` from the commitment.

Downstream code decides how much error to tolerate:
- Perfect extraction: `∀ m, Pr[= true | extractExp cs ext m] = 1`
- Computational: bound `1 - Pr[= true | extractExp cs ext m]` -/
def extractExp [DecidableEq M] (cs : CommitmentScheme PP M C D)
    {TD : Type} (extractor : TrapdoorExtractor PP TD C M)
    (m : M) : ProbComp Bool := do
  let (pp, td) ← extractor.setupExtract
  let (c, _) ← cs.commit pp m
  let m' ← extractor.extract td c
  return decide (m' = m)

end CommitmentScheme
