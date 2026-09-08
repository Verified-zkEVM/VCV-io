# Reading: design records

Longer-form design documents. These are records of investigation and decision, not agent
instructions — for how to *use* the probability layer, see
[`docs/agents/probability.md`](../agents/probability.md).

## Probability semantics

Read in this order; each answers a different question.

| # | Document | Status | Question it answers |
|---|---|---|---|
| 1 | [`probability-semantics-landscape.md`](probability-semantics-landscape.md) | Historical survey plus current-status appendix | What options were considered, what evidence supported the decision, and which volatile upstream facts were later rechecked? §19 preserves the original verification log; §20 records later disposition. |
| 2 | [`measure-semantics-spike.md`](measure-semantics-spike.md) | Historical implementation record | What happened when the measure-native option was built? Findings and friction, including what it did *not* settle. |
| 3 | [`denotational-probability-semantics.md`](denotational-probability-semantics.md) | Accepted baseline | Which design was accepted, and what rules govern new work? |
| 4 | [`mathlib-integration-shape.md`](mathlib-integration-shape.md) | Design guidance | What should the resulting statements *look like* so Mathlib's library applies to them? Short- and long-term shape. |

Start at 3 if you only want the current rule. Start at 1 if you want to know why, or to check a
claim before relying on it.

The documents deliberately serve different time horizons. The landscape and spike preserve the
reasoning that led to the decision; the baseline and agent guide state the rules to apply now. Do
not infer current API names or PR status from an old snapshot without checking its later-status
section or the pinned source tree.

## Upstream alignment

| Document | Status | Question it answers |
|---|---|---|
| [`upstream-alignment.md`](upstream-alignment.md) | Living ledger, re-run at each pin bump | Which of VCVio's general-purpose machinery and tooling does Lean core, Mathlib, Batteries, cslib, or PolyFun already own, and what is the verdict (adopt / keep / upstream / track) for each, with the evidence? Includes a broad reading of the adjacent Mathlib areas and the idioms they suggest. |
| [`internal-duplication.md`](internal-duplication.md) | Living record | Where does VCVio say the same thing twice *inside* the repository (cost layers, invariant predicates, the two Merkle engines, `OracleSpec` operations versus PolyFun's), which spelling is canonical, and what blocks folding the rest? |

## Keeping these honest

Two conventions, both learned the hard way and worth preserving:

**Record the method, not just the verdict.** §19 of the landscape gives, for each claim, how it was
checked. The failure mode these documents are most exposed to is asserting that upstream provides
something on the strength of a name matching. A name is a hypothesis; the declaration in the pinned
tree is the evidence.

**Re-check volatile facts at the moment of editing.** Upstream tags, PR statuses, and draft-versus-
open state change faster than the documents that cite them — the PolyFun tag in §19.4 went stale
twice in a single day. Preserve the dated result as history, then add a new dated disposition backed
by the pinned source tree. A fact that was verified last week is not verified today.
