/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Lean
import VCVio.ProgramLogic.Tactics.Common.Core

/-! # VC Spec Intermediate Representation

Tactic-level intermediate representation used to classify program-logic
specification rules for diagnostic messages, registry bookkeeping, and the
compiled-rule layer. The discrimination-tree indexing itself lives in
`Registry.lean` and operates on `Lean.Meta.Sym.Pattern`; the IR defined here is
a light-weight summary attached to each `@[vcspec]` entry.
-/

open Lean Elab Meta

namespace OracleComp.ProgramLogic

inductive VCSpecKind where
  | unaryTriple
  | unaryWP
  | relTriple
  | relWP
  | eRelTriple
  deriving Inhabited, BEq, Repr

inductive VCSpecLookupKey where
  | unary (head : Name)
  | relational (leftHead rightHead : Name)
  deriving Inhabited, BEq, Repr

inductive VCSpecArgShape where
  | schematic
  | concrete
  deriving Inhabited, BEq, Repr

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

inductive VCSpecCompPattern where
  | unary (form : VCSpecCompForm)
  | relational (leftForm rightForm : VCSpecCompForm)
  deriving Inhabited, BEq, Repr

structure NormalizedVCSpec where
  kind : VCSpecKind
  lookupKey : VCSpecLookupKey
  compPattern : VCSpecCompPattern
  theoremBinderCount : Nat
  preShape : Option VCSpecArgShape
  postShape : VCSpecArgShape
  deriving Inhabited, BEq, Repr

def VCSpecLookupKey.toLegacyKey : VCSpecLookupKey → Sum Name (Name × Name)
  | .unary head => .inl head
  | .relational leftHead rightHead => .inr (leftHead, rightHead)

/-- Rough structural summary of a single argument slot of a `@[vcspec]` rule.
`.schematic` means the argument is a bare free variable or metavariable in the
rule statement (the user has not constrained its shape); `.concrete` means the
argument has some structural shape at the rule level. The planner uses this
classification as a coarse secondary filter when ranking candidates. -/
def classifyArgShape (e : Expr) : VCSpecArgShape :=
  let e := e.consumeMData
  if e.isFVar || e.isMVar then
    .schematic
  else
    .concrete

/-- Rough structural summary of a single oracle computation slot of a
`@[vcspec]` rule, keyed on the outer head introduced by the standard monad
operations (`>>=`, `pure`, `query`, `if`, …). -/
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
