/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import Lean
import VCVio.ProgramLogic.Tactics.Common.Core

/-! # VC Spec Intermediate Representation

Tactic-level intermediate representation used to classify program-logic
specification rules for diagnostic messages, registry bookkeeping, and
structural candidate filtering. The discrimination-tree indexing itself lives
in `Registry.lean` and operates on `Lean.Meta.Sym.Pattern`; the IR defined
here is a light-weight summary attached to each `@[vcspec]` entry.
-/

open Lean Elab Meta

namespace OracleComp.ProgramLogic

/-- Broad category of a `@[vcspec]` rule, derived from the head of the
theorem's statement (`Triple`, `wp`, `RelTriple`, `RelWP`). -/
inductive VCSpecKind where
  | unaryTriple
  | unaryWP
  | relTriple
  | relWP
  deriving Inhabited, BEq, Repr

/-- Coarse lookup shape used to route a rule into the right discrimination
tree partition (unary vs relational) at registration time. -/
inductive VCSpecLookupKey where
  | unary (head : Name)
  | relational (leftHead rightHead : Name)
  deriving Inhabited, BEq, Repr

/-- Outer syntactic shape of a single oracle computation slot of a
`@[vcspec]` rule. Used for coarse secondary filtering when the
discrimination tree returns multiple candidates. -/
inductive VCSpecCompForm where
  | bind
  | pure
  | ite
  | map
  | replicate
  | listMapM
  | listFoldlM
  | query
  | simulateQ
  | other
  deriving Inhabited, BEq, Repr

/-- Combined comp-form of a rule's computation slot(s). Unary rules record
a single form; relational rules record both sides. -/
inductive VCSpecCompPattern where
  | unary (form : VCSpecCompForm)
  | relational (leftForm rightForm : VCSpecCompForm)
  deriving Inhabited, BEq, Repr

/-- Normalized summary of a `@[vcspec]` rule attached to every registered
entry. The discrimination tree is the primary index; this summary powers
kind-filtered iteration helpers and structural-compatibility scoring in
the planner. -/
structure NormalizedVCSpec where
  kind : VCSpecKind
  lookupKey : VCSpecLookupKey
  compPattern : VCSpecCompPattern
  deriving Inhabited, BEq, Repr

/-- Rough structural summary of the outer head of a computation slot,
keyed on the standard monad operations (`>>=`, `pure`, `query`, `if`, …). -/
def classifyVCSpecCompForm (comp : Expr) : VCSpecCompForm :=
  let comp := comp.consumeMData
  if isBindExpr comp then
    .bind
  else if isPureExpr comp then
    .pure
  else if isIfExpr comp then
    .ite
  else if isMapExpr comp then
    .map
  else if isReplicateExpr comp then
    .replicate
  else if isListMapMExpr comp then
    .listMapM
  else if isListFoldlMExpr comp then
    .listFoldlM
  else if isSimulateQAction comp then
    .simulateQ
  else if (findAppWithHead? ``query comp).isSome then
    .query
  else
    .other

def classifyUnaryCompPattern (comp : Expr) : VCSpecCompPattern :=
  .unary (classifyVCSpecCompForm comp)

def classifyRelationalCompPattern (oa ob : Expr) : VCSpecCompPattern :=
  .relational (classifyVCSpecCompForm oa) (classifyVCSpecCompForm ob)

end OracleComp.ProgramLogic
