/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import PolyFun.Realizability.Quantitative.Polynomial
public import VCVio.CryptoFoundations.Asymptotics.ComputationalComplexity
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Meta.Tactic.Assumption
public meta import Lean.Meta.Tactic.TryThis

/-!
# Conservative polynomial-time proof lookup

This module provides a deliberately small automation surface for polynomial-time proofs.
`@[ppt_primitive]` accepts only concrete value declarations returning a PolyFun `PolyRealizer`, or
theorems concluding VCVio's backend-relative `IsOraclePPTBy`. (`PolyRealizer` lives in `Type`, so it
cannot itself be the conclusion of a Lean `theorem`.) The `ppt` tactic closes a goal only with a
definitionally exact local assumption or a registered declaration that elaborates as an exact
term of the whole goal.

There is intentionally no simp set, recursive theorem application, or generic proof search here.
In particular, registration does not make a semantic function executable and `ppt` never invents
a realizer. Later compositional automation can grow from PolyFun's explicit polynomial-category
and structural mixins without weakening this trusted primitive boundary.

The registry uses two literal result-head buckets rather than `Sym.Pattern`: there are only two
accepted heads, and Sym's declaration preprocessing would unfold the reducible `IsOraclePPTBy`
surface to its `Nonempty` implementation. Every bucket candidate is still checked by exact term
elaboration, so head lookup is only a bounded selector and never establishes a proof.
-/

public meta section

open Lean Elab Meta Tactic

namespace OracleComp.Complexity

private inductive PPTPrimitiveKind where
  | polyRealizer
  | oraclePPT
  deriving BEq, Inhabited

attribute [inherit_doc Inhabited.default] instInhabitedPPTPrimitiveKind.default

private def PPTPrimitiveKind.description : PPTPrimitiveKind → String
  | .polyRealizer => "PolyRealizer"
  | .oraclePPT => "IsOraclePPTBy"

private def constantInfoKind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .thmInfo _ => "theorem"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

private structure PPTPrimitiveEntry where
  declaration : Name
  kind : PPTPrimitiveKind
  deriving Inhabited

attribute [inherit_doc Inhabited.default] instInhabitedPPTPrimitiveEntry.default

private structure PPTPrimitiveRegistry where
  entries : Array PPTPrimitiveEntry := #[]

private instance : Inhabited PPTPrimitiveRegistry := ⟨{}⟩

private initialize pptPrimitiveRegistry :
    SimpleScopedEnvExtension PPTPrimitiveEntry PPTPrimitiveRegistry ←
  registerSimpleScopedEnvExtension {
    addEntry := fun registry entry =>
      { registry with entries := registry.entries.push entry }
    initial := {}
  }

/-- Classify one un-reduced result type accepted by `@[ppt_primitive]` and `ppt`.

The check intentionally observes the surface head before weak-head reduction: reducing
`IsOraclePPTBy` would erase the API boundary and expose its `Nonempty` implementation. -/
private def classifyResult? (result : Expr) : Option PPTPrimitiveKind :=
  match result.consumeMData.getAppFn.constName? with
  | some ``PFunctor.QuantitativeStepClass.PolyRealizer => some .polyRealizer
  | some ``OracleComp.Complexity.IsOraclePPTBy => some .oraclePPT
  | _ => none

/-- Validate a declaration and recover the supported head of its final result.

`PolyRealizer` primitives must be definitions or opaque values, never unbacked constants.
`IsOraclePPTBy` primitives must be theorem or opaque proof declarations. Lean exposes a theorem as
a temporary axiom while processing its attributes, before recording its final theorem tag; the
registry therefore revalidates the finalized declaration metadata before every lookup. -/
private def classifyPrimitiveDeclaration (declaration : Name) : MetaM PPTPrimitiveKind := do
  let info ← getConstInfo declaration
  forallTelescope info.toConstantVal.type fun _ result => do
    let some kind := classifyResult? result
      | throwError "@[ppt_primitive] expects a declaration ending in exactly one of:\n\
          - a concrete `PFunctor.QuantitativeStepClass.PolyRealizer ...` value\n\
          - a theorem proving `OracleComp.Complexity.IsOraclePPTBy ...`\n\
          got:{indentExpr result}"
    match kind, info with
    | .polyRealizer, .defnInfo _ | .polyRealizer, .opaqueInfo _ => return kind
    | .oraclePPT, .thmInfo _ | .oraclePPT, .opaqueInfo _ | .oraclePPT, .axiomInfo _ => return kind
    | .polyRealizer, _ =>
        throwError "@[ppt_primitive] rejects `{declaration}`: a `PolyRealizer` primitive must be a \
          concrete `def` or `opaque` value, not an unbacked constant or theorem."
    | .oraclePPT, _ =>
        throwError "@[ppt_primitive] rejects `{declaration}`: an `IsOraclePPTBy` primitive must be \
          a theorem or opaque proof; registration saw `{constantInfoKind info}` metadata."

initialize registerBuiltinAttribute {
  name := `ppt_primitive
  descr := "Register exact PolyRealizer data or an IsOraclePPTBy theorem for conservative lookup."
  add := fun declaration _stx kind => MetaM.run' do
    let primitiveKind ← classifyPrimitiveDeclaration declaration
    pptPrimitiveRegistry.add { declaration, kind := primitiveKind } kind
}

/-- Whether finalized declaration metadata is trusted for its registered primitive kind.

The axiom placeholder visible while applying an attribute is deliberately absent here, so an
actual axiom can never become an automatic `ppt` primitive. -/
private def isFinalPPTPrimitive (entry : PPTPrimitiveEntry) : CoreM Bool := do
  let some info := (← getEnv).find? entry.declaration | return false
  return match entry.kind, info with
    | .polyRealizer, .defnInfo _ | .polyRealizer, .opaqueInfo _ => true
    | .oraclePPT, .thmInfo _ | .oraclePPT, .opaqueInfo _ => true
    | _, _ => false

/-- Registered declarations with the same validated result head as the current goal. -/
private def getPPTPrimitives (kind : PPTPrimitiveKind) : CoreM (Array PPTPrimitiveEntry) := do
  let registry := pptPrimitiveRegistry.getState (← getEnv)
  let mut result := #[]
  for entry in registry.entries do
    if entry.kind == kind && (← isFinalPPTPrimitive entry) then
      result := result.push entry
  return result

private inductive PPTResolution where
  | assumption
  | primitive (declaration : Name)

/-- Close the main goal with exactly the supplied term, rejecting unassigned metavariables. -/
private def closeWithExactTerm (term : TSyntax `term) : TacticM Unit :=
  closeMainGoalUsing `ppt fun target _ =>
    withoutRecover <| elabTermEnsuringType term (some target)

/-- Backtracking exact-term attempt used for registered candidates. -/
private def tryExactTerm (term : TSyntax `term) : TacticM Bool := do
  return (← observing? (closeWithExactTerm term)).isSome

/-- Backtracking use of a definitionally exact local assumption. -/
private def tryLocalAssumption : TacticM Bool := do
  return (← observing? do
    let goal ← getMainGoal
    unless ← goal.assumptionCore do
      throwError "no definitionally exact local assumption"
    replaceMainGoal []).isSome

/-- Run the bounded `ppt` lookup and report how the goal was closed. -/
private def runPPT : TacticM PPTResolution := withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  let some kind := classifyResult? target
    | throwError "ppt supports goals headed exactly by `PolyRealizer` or `IsOraclePPTBy`; \
        got:{indentExpr target}"
  if ← tryLocalAssumption then
    return .assumption
  let candidates ← getPPTPrimitives kind
  for candidate in candidates do
    let term : TSyntax `term := ⟨mkIdent candidate.declaration⟩
    if ← tryExactTerm term then
      return .primitive candidate.declaration
  let tried := String.intercalate ", " <| candidates.toList.map fun candidate =>
    candidate.declaration.toString
  if candidates.isEmpty then
    throwError "ppt found no exact local assumption and no registered \
      `@[ppt_primitive]` declaration with result head `{kind.description}` for:{indentExpr target}"
  throwError "ppt found no exact local assumption, and none of the {candidates.size} registered \
    `{kind.description}` primitives exactly closed the goal:{indentExpr target}\n\
    tried: {tried}\n\
    Use `ppt using <term>` when a registered declaration needs explicit arguments."

/-- Attach a replayable suggestion for the successful bounded lookup. -/
private def addPPTSuggestion (ref : Syntax) : PPTResolution → MetaM Unit
  | .assumption =>
      Meta.Tactic.TryThis.addSuggestion ref
        { suggestion := .string "assumption" }
        (origSpan? := some ref)
        (header := "Try this:\n")
  | .primitive declaration =>
      Meta.Tactic.TryThis.addSuggestion ref
        { suggestion := .string s!"exact {declaration}" }
        (origSpan? := some ref)
        (header := "Try this:\n")

/-- Close a `PolyRealizer` or `IsOraclePPTBy` goal using only an exact local assumption or an
exact registered `@[ppt_primitive]` declaration. -/
syntax (name := pptBasic) "ppt" : tactic

/-- Run the same bounded lookup as `ppt` and emit its exact replay term as a suggestion. -/
syntax (name := pptSuggestion) "ppt?" : tactic

/-- Close a supported polynomial-time goal with exactly the user-supplied proof term. -/
syntax (name := pptUsing) "ppt" "using" term : tactic

elab_rules (kind := pptBasic) : tactic
  | `(tactic| ppt) =>
      discard runPPT

elab_rules (kind := pptSuggestion) : tactic
  | `(tactic| ppt?) => do
      let ref ← getRef
      addPPTSuggestion ref (← runPPT)

elab_rules (kind := pptUsing) : tactic
  | `(tactic| ppt using $term) => do
      let target ← withMainContext <| instantiateMVars (← getMainTarget)
      unless classifyResult? target |>.isSome do
        throwError "ppt using supports goals headed exactly by `PolyRealizer` or \
          `IsOraclePPTBy`; got:{indentExpr target}"
      try
        closeWithExactTerm term
      catch error =>
        throwErrorAt term m!"ppt using failed to close the goal exactly:\n\
          {indentExpr target}\n\
          {error.toMessageData}"

end OracleComp.Complexity
