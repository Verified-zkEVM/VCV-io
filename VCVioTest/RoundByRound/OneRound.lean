/-
Copyright (c) 2026 Aristotle (Harmonic), Elias Judin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/

module

public import VCVio.CryptoFoundations.RoundByRound

/-!
# One-round regression for round-by-round knowledge extraction

This smoke test instantiates a genuinely nontrivial one-round `KnowledgeExtractionFamily` over a
uniformly sampled two-challenge round and exercises the strict-trigger content of Definition 3.12
of Block, Garreta, Tiwari, and Zając (*On Soundness Notions for Interactive Oracle Proofs*,
Cryptology ePrint Archive 2023/1256), rather than merely naming the generic bridge.

The instantiated family is deliberately non-vacuous:

* the canonical initial context is doomed for every input (`oneRound_initialCondition`);
* a doomed terminal context forces rejection (`oneRound_terminalCondition`);
* the extracted witness genuinely fails the relation (`oneRound_relation_fails`);
* the fresh challenge escapes the doomed set with probability exactly `1 / 2`
  (`oneRound_escape_prob`), so escape has nonzero probability;
* on the doomed `(context, message)` subtype the transition `badEvent` reduces to that escape event
  (`oneRound_badEvent_iff`);
* at `error = Pr[escape] = 1 / 2` the strict trigger `error < Pr[escape]` does **not** fire, and
  both sides of the bridge hold (`oneRound_extractionCondition_half`, `oneRound_isBounded_half`);
* at the strictly smaller `error = 0` the strict trigger fires on a failed extraction, so both the
  extraction condition and boundedness fail (`oneRound_not_extractionCondition_zero`,
  `oneRound_not_isBounded_zero`).

At least one theorem (`oneRound_escape_prob`) establishes the concrete probability fact directly
instead of restating `KnowledgeExtractionFamily.extractionCondition_iff_isBounded` by application.
The final `oneRound_extractionCondition_iff_isBounded` still exercises the generic bridge on this
concrete family.

One caveat about the family above, and the reason for the companion below. `ExtractionCondition`
is a conditional, and for `oneRound` its antecedent `error < Pr[escape]` is unsatisfiable at
`1 / 2`, since escape has probability exactly `1 / 2`. So `oneRound_extractionCondition_half` is
vacuously true: axiom-clean while asserting nothing about extraction. This is the failure class in
`docs/agents/gotchas.md` §14, and `#print axioms` cannot detect it.

`oneRoundValid` supplies the missing certificate. It differs from `oneRound` only in its relation,
so that `extract`'s output satisfies it, and then:

* `oneRoundValid_hypotheses_satisfiable` exhibits a context that is doomed **and** whose escape
  probability exceeds the error, so the clause's antecedents are jointly inhabitable;
* `oneRoundValid_extractionCondition_zero` discharges the clause at `error = 0` *because
  extraction succeeds*, with the trigger firing rather than silent;
* `oneRoundValid_isBounded_zero` reaches the relation-holds branch of the generic bridge, which
  `oneRound` cannot;
* `oneRoundValid_extensionalConditions` bundles all three clauses at `error = 0`, since showing
  each hypothesis separately inhabited is weaker than a witness for the whole bundle.
-/

public section

open scoped ENNReal

namespace VCVioTest.RoundByRound

open _root_.RoundByRound
open OracleComp OracleSpec

/-- A genuinely nontrivial one-round knowledge-extraction family.

The context type at each stage is `Fin 2` (carrying the sampled challenge at the terminal stage),
the fresh challenge is sampled uniformly from `Fin 2`, and the doomed set is "stage `0`, or the
carried value is `0`". Thus the initial context is always doomed, the terminal context escapes doom
exactly when the sampled challenge is `1`, and the extractor returns `false` while the relation
only accepts `true`, so the extracted witness always fails the relation. -/
noncomputable def oneRound : KnowledgeExtractionFamily 1 where
  Statement := Unit
  Witness := Bool
  Context := fun _ => Fin 2
  Message := fun _ => Unit
  Challenge := fun _ => Fin 2
  FinalMessage := Unit
  challengeSampleable := fun _ => inferInstance
  statement := fun _ _ => ()
  initialContext := fun _ => 0
  extend := fun _ _ _ challenge => challenge
  statement_initial := fun _ => rfl
  statement_extend := fun _ _ _ _ => rfl
  doomed := fun stage c => stage = 0 ∨ c = 0
  extract := fun _ _ _ => false
  relation := fun _ w => w = true
  rejects := fun ctx _ => ctx = 0

/-- The specialized `OracleComp.probOutput_eq_sub_probFailure_of_unit` accepts `spec` as a named
argument. -/
example {ι : Type} {spec : OracleSpec ι} [IsProbabilitySpec spec] (oa : OracleComp spec PUnit) :
    Pr[= () | oa] = 1 - Pr[⊥ | oa] :=
  probOutput_eq_sub_probFailure_of_unit (spec := spec)

/-- The canonical initial context is doomed for every input. -/
theorem oneRound_initialCondition : oneRound.InitialCondition := by
  intro _; exact Or.inl rfl

/-- A doomed terminal context forces the verifier to reject every final prover message. -/
theorem oneRound_terminalCondition : oneRound.TerminalCondition := by
  intro context _ hdoomed
  rcases hdoomed with h | h
  · exact absurd h (by decide)
  · exact h

/-- The directly extracted witness genuinely fails the relation. -/
theorem oneRound_relation_fails (context : oneRound.Context (0 : Fin 1).castSucc)
    (message : oneRound.Message 0) :
    ¬ oneRound.relation (oneRound.statement (0 : Fin 1).castSucc context)
        (oneRound.extract 0 context message) := by
  simp only [oneRound]; decide

/-- The fresh challenge escapes the doomed set with probability exactly `1 / 2`. This is the
concrete probability fact, proved directly rather than through the generic bridge. -/
theorem oneRound_escape_prob (context : oneRound.Context (0 : Fin 1).castSucc)
    (message : oneRound.Message 0) :
    Pr[oneRound.escapeEvent 0 context message | oneRound.sampleChallenge 0] = 1 / 2 := by
  have hev : Pr[oneRound.escapeEvent 0 context message | $ᵗ (Fin 2)]
      = Pr[(fun c : Fin 2 => c ≠ 0) | $ᵗ (Fin 2)] := by
    refine probEvent_ext (fun c _ => ?_)
    fin_cases c <;> simp only [KnowledgeExtractionFamily.escapeEvent, oneRound] <;> decide
  -- Normalize the dependent challenge type `oneRound.Challenge 0` to the concrete sampler
  -- `$ᵗ (Fin 2)` before rewriting through the probability lemmas.
  change Pr[oneRound.escapeEvent 0 context message | $ᵗ (Fin 2)] = 1 / 2
  rw [hev, probEvent_uniformSample]
  have hc : (Finset.univ.filter (fun c : Fin 2 => c ≠ 0)).card = 1 := by decide
  rw [hc, Fintype.card_fin]
  norm_num

/-- On the doomed `(context, message)` subtype, the transition `badEvent` reduces exactly to the
escape event (because the extracted witness always fails the relation). -/
theorem oneRound_badEvent_iff (context : oneRound.Context (0 : Fin 1).castSucc)
    (message : oneRound.Message 0)
    (hdoomed : oneRound.doomed (0 : Fin 1).castSucc context) (challenge : oneRound.Challenge 0) :
    oneRound.toKnowledgeTransitionFamily.badEvent 0 ⟨(context, message), hdoomed⟩ challenge
      ↔ oneRound.escapeEvent 0 context message challenge := by
  rw [oneRound.toKnowledgeTransitionFamily_badEvent_iff 0 context message hdoomed challenge]
  exact ⟨fun h => h.2, fun h => ⟨oneRound_relation_fails context message, h⟩⟩

/-- Direct fact: the doomed-subtype transition family is bounded by the constant error `1 / 2`,
i.e. at `error = Pr[escape]` boundedness holds. -/
theorem oneRound_isBounded_half :
    oneRound.toKnowledgeTransitionFamily.IsBounded (fun _ => 1 / 2) := by
  rw [KnowledgeTransitionFamily.isBounded_iff]
  intro round cm
  obtain rfl : round = 0 := Subsingleton.elim _ _
  obtain ⟨⟨context, message⟩, hdoomed⟩ := cm
  rw [oneRound.probEvent_toKnowledgeTransitionFamily_badEvent_of_not_relation 0 context message
      hdoomed (oneRound_relation_fails context message), oneRound_escape_prob context message]

/-- At `error = Pr[escape] = 1 / 2` the strict trigger does not fire, so the extraction condition
holds; obtained from `oneRound_isBounded_half` through the generic bridge. -/
theorem oneRound_extractionCondition_half : oneRound.ExtractionCondition (fun _ => 1 / 2) :=
  (oneRound.extractionCondition_iff_isBounded _).mpr oneRound_isBounded_half

/-- Direct fact: the doomed-subtype transition family is **not** bounded by the strictly smaller
constant error `0`, because escape (hence the bad event) has probability `1 / 2 > 0`. -/
theorem oneRound_not_isBounded_zero :
    ¬ oneRound.toKnowledgeTransitionFamily.IsBounded (fun _ => 0) := by
  rw [KnowledgeTransitionFamily.isBounded_iff]
  push Not
  refine ⟨0, ⟨((0 : Fin 2), ()), Or.inl rfl⟩, ?_⟩
  rw [oneRound.probEvent_toKnowledgeTransitionFamily_badEvent_of_not_relation 0 (0 : Fin 2) ()
      (Or.inl rfl) (oneRound_relation_fails (0 : Fin 2) ()), oneRound_escape_prob (0 : Fin 2) ()]
  exact ENNReal.half_pos (by norm_num)

/-- At the strictly smaller `error = 0` the strict trigger fires on a failed extraction, so the
extraction condition fails; obtained from `oneRound_not_isBounded_zero` through the generic
bridge. -/
theorem oneRound_not_extractionCondition_zero : ¬ oneRound.ExtractionCondition (fun _ => 0) := by
  rw [oneRound.extractionCondition_iff_isBounded]
  exact oneRound_not_isBounded_zero

/-- Regression: the extensional extraction condition for `oneRound` is equivalent to boundedness of
its doomed `(context, message)` knowledge-transition family, i.e. the compiled instance of the
generic bridge `KnowledgeExtractionFamily.extractionCondition_iff_isBounded` on this concrete
family. -/
theorem oneRound_extractionCondition_iff_isBounded (error : Fin 1 → ℝ≥0∞) :
    oneRound.ExtractionCondition error ↔
      oneRound.toKnowledgeTransitionFamily.IsBounded error :=
  oneRound.extractionCondition_iff_isBounded error

/-! ### A family whose extraction succeeds under a firing trigger

In `oneRound` the extracted witness always fails the relation, so `ExtractionCondition` holds at
`1 / 2` only because the strict trigger `error < Pr[escape]` never fires. The family below flips
the relation so that `extract`'s output satisfies it, which exercises the complementary situation:
the trigger fires and the extraction condition holds *because extraction succeeds*. It also reaches
the relation-holds branch of `extractionCondition_iff_isBounded`, which `oneRound` cannot. -/

/-- `oneRound` with the relation satisfied by the extracted witness. Everything determining the
doomed set, the challenge distribution and the escape event is unchanged; only `relation` flips
from `w = true` to `w = false`, so `extract`'s constant output `false` now satisfies it. -/
noncomputable def oneRoundValid : KnowledgeExtractionFamily 1 :=
  { oneRound with relation := fun _ w => w = false }

/-- The escape event and challenge sampler are literally those of `oneRound`. -/
theorem oneRoundValid_escape_prob (context : oneRoundValid.Context (0 : Fin 1).castSucc)
    (message : oneRoundValid.Message 0) :
    Pr[oneRoundValid.escapeEvent 0 context message | oneRoundValid.sampleChallenge 0] = 1 / 2 :=
  oneRound_escape_prob context message

/-- The directly extracted witness genuinely **satisfies** the relation, the mirror image of
`oneRound_relation_fails`. -/
theorem oneRoundValid_relation_holds (context : oneRoundValid.Context (0 : Fin 1).castSucc)
    (message : oneRoundValid.Message 0) :
    oneRoundValid.relation (oneRoundValid.statement (0 : Fin 1).castSucc context)
      (oneRoundValid.extract 0 context message) := by
  simp only [oneRoundValid, oneRound]

/-- The strict escape trigger fires at `error = 0`, since escape has probability `1 / 2 > 0`. This
is the hypothesis `oneRound` can never discharge. -/
theorem oneRoundValid_trigger_fires (context : oneRoundValid.Context (0 : Fin 1).castSucc)
    (message : oneRoundValid.Message 0) :
    (0 : ℝ≥0∞) < Pr[oneRoundValid.escapeEvent 0 context message
      | oneRoundValid.sampleChallenge 0] := by
  rw [oneRoundValid_escape_prob context message]
  exact ENNReal.half_pos (by norm_num)

/-- **Satisfiability of the extraction clause's hypotheses.** `ExtractionCondition` is a
conditional, so proving it says nothing unless its antecedents are jointly inhabitable: a context
that is doomed *and* whose escape probability exceeds the error. Here both hold at once, at
`error = 0`, for the initial context. Without this the clause below would be discharged by
hypotheses no instance can meet — the vacuity that `#print axioms` cannot see. -/
theorem oneRoundValid_hypotheses_satisfiable :
    ∃ (context : oneRoundValid.Context (0 : Fin 1).castSucc) (message : oneRoundValid.Message 0),
      oneRoundValid.doomed (0 : Fin 1).castSucc context ∧
        (0 : ℝ≥0∞) < Pr[oneRoundValid.escapeEvent 0 context message
          | oneRoundValid.sampleChallenge 0] :=
  ⟨(0 : Fin 2), (), Or.inl rfl, oneRoundValid_trigger_fires (0 : Fin 2) ()⟩

/-- The extraction condition holds at `error = 0` because extraction succeeds, not because the
trigger stays silent — `oneRoundValid_hypotheses_satisfiable` exhibits a context meeting both
antecedents. Read against `oneRound_not_extractionCondition_zero`, which fails at the same error
with a failing extractor, this pins down that `ExtractionCondition` measures the extractor rather
than the trigger. -/
theorem oneRoundValid_extractionCondition_zero :
    oneRoundValid.ExtractionCondition (fun _ => 0) := by
  intro round context message _ _
  exact oneRoundValid_relation_holds context message

/-- Through the generic bridge, the doomed-subtype transition family is bounded by `0`: the bad
event is empty because the extracted witness satisfies the relation. This is the relation-holds
branch of `extractionCondition_iff_isBounded`. -/
theorem oneRoundValid_isBounded_zero :
    oneRoundValid.toKnowledgeTransitionFamily.IsBounded (fun _ => 0) :=
  (oneRoundValid.extractionCondition_iff_isBounded _).mp oneRoundValid_extractionCondition_zero

/-- All three extensional clauses hold for `oneRoundValid` at error `0`, with the extraction clause
discharged under a firing trigger. -/
theorem oneRoundValid_extensionalConditions : oneRoundValid.ExtensionalConditions (fun _ => 0) :=
  ⟨oneRound_initialCondition, oneRound_terminalCondition, oneRoundValid_extractionCondition_zero⟩

end VCVioTest.RoundByRound
