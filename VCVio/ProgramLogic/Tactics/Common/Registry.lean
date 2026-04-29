/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import Lean
import Lean.Meta.Sym.Pattern
import Lean.Meta.Sym.Simp.DiscrTree
import Lean.Elab.Tactic.Do.Attr
import ToMathlib.Control.Monad.RelWP
import VCVio.ProgramLogic.Tactics.Common.SpecIR

/-!
# VCSpec Registry

Discrimination-tree backed registry for `@[vcspec]` lemmas used by the unary and relational
program-logic tactics.

The registry indexes each registered theorem by the *computation* sub-expression
of its conclusion: for unary triples / `wp` goals this is the `OracleComp` argument,
and for relational triples / `RelWP` goals this is the left-hand computation. A separate
constant-name filter on the right-hand head keeps relational lookups precise without
paying for two structural matches.

## Implementation notes

Patterns are constructed via `Lean.Meta.Sym.mkPatternFromDeclWithKey`. That pipeline
preprocesses the theorem type (unfolding reducibles, renaming universe parameters,
collecting proof / instance argument metadata), internalizes `∀`-bound variables as
de Bruijn indices, and lets us pick the index key (the computation expression) out
of the preprocessed body. The resulting `Sym.Pattern` is then inserted into a
`Lean.Meta.DiscrTree` via `Sym.insertPattern`, which wildcards proof / instance
arguments and bound variables in the key sequence.

Because `Sym.preprocessType` unfolds the user-facing abbreviations
(`Triple`, `wp`, `RelTriple`, `RelWP`) into their `MAlgOrdered.*` /
`MAlgRelOrdered.*` cores, the selector matches on the unfolded heads (plus the
folded abbreviations as a safety net). On the lookup side we apply
`withReducible <| whnf` to the goal's computation before querying, matching the
normalization performed during pattern preprocessing.

## Alignment with core `SpecTheorem`

Entries mirror the layout of `Lean.Elab.Tactic.Do.SpecAttr.SpecTheorem`
wherever possible:

* `proof : SpecProof` is reused directly, so entries can be global
  declarations (the common case for `@[vcspec]`), local hypotheses, or raw
  proof expressions. This anticipates the Phase F bridge where a subset of
  our entries (the `Triple`-shaped ones) is exposed to `mvcgen'` via the
  core `SpecExtension`.
* `pattern : Sym.Pattern` is the Sym-side analogue of the combined
  `SpecTheorem.{prog, keys}` pair; it carries the program sub-expression,
  ∀-binder types, level parameters, and proof/instance slot metadata.
* `priority : Nat` uses the same default as `SpecTheorem` so attribute
  overrides carry over cleanly.

## Future-proofing note

`Lean.Meta.Sym` is under active development upstream; minor shape changes to
`Sym.Pattern`, `Sym.insertPattern`, or `Sym.DiscrTree.getMatch` between Lean
releases should be expected. If a toolchain bump breaks the registry, the
affected surface is confined to the selector in `buildVCSpecEntry` and the
lookup path in `getRegisteredUnaryVCSpecEntries` /
`getRegisteredRelationalVCSpecEntries`; downstream tactic dispatch works
through `VCSpecEntry.declName?` / `VCSpecEntry.theoremName!` and is
insulated from `Sym` API churn.
-/

open Lean Elab Meta Lean.Meta
open Lean.Elab.Tactic.Do.SpecAttr (SpecProof)

namespace OracleComp.ProgramLogic

/-- A registered `@[vcspec]` lemma together with everything the planner needs.

Layout mirrors `Lean.Elab.Tactic.Do.SpecAttr.SpecTheorem` so the Phase F
bridge can lift entries into the core `SpecExtension` without an extra
conversion pass: `proof` is a shared `SpecProof`, `pattern` is the Sym
analogue of `SpecTheorem.{prog, keys}`, and `priority` uses the same default
macro expansion. `spec` and `rightHead?` are VCVio-specific diagnostic /
planner extras that core does not need. -/
structure VCSpecEntry where
  /-- Origin of the proof: a global declaration, a local hypothesis, or a
  raw proof expression. For `@[vcspec]` attribute registrations this is
  always `.global declName`, but keeping the full `SpecProof` ADT leaves
  room for a future tactic-level `vcspec` syntax that feeds hypotheses in
  directly, and for direct interop with core `SpecTheorem`. -/
  proof : SpecProof
  /-- Sym-level pattern used for discrimination-tree indexing. The pattern
  stores the program sub-expression plus enough bookkeeping (level params,
  ∀-binder types, proof / instance slots) for `Sym.insertPattern` and
  `Sym.getMatch` to work; it is the Sym-side analogue of
  `SpecTheorem.{prog, keys}`. -/
  pattern : Lean.Meta.Sym.Pattern
  /-- Normalized IR summary attached for diagnostics and planner ranking.
  Not consumed by the discrimination-tree layer. -/
  spec : NormalizedVCSpec
  /-- Right-hand head constant used as a secondary filter for relational
  entries. `none` for unary entries. -/
  rightHead? : Option Name := none
  /-- User-supplied priority; same default as `SpecTheorem.priority`. -/
  priority : Nat := eval_prio default
  deriving Inhabited

instance : BEq VCSpecEntry where
  beq a b := a.proof == b.proof

/-- Global declaration name for entries registered via `@[vcspec]`; `none`
for entries backed by a local hypothesis or raw proof expression. -/
def VCSpecEntry.declName? (entry : VCSpecEntry) : Option Name :=
  match entry.proof with
  | .global n => some n
  | _ => none

/-- Extract the global declaration name, assuming the entry was registered
via `@[vcspec]` on a global theorem. Panics on local / stx proofs; intended
for legacy call sites that pre-date local-hypothesis support. -/
def VCSpecEntry.theoremName! (entry : VCSpecEntry) : Name :=
  entry.declName?.getD Name.anonymous

def VCSpecEntry.kind (entry : VCSpecEntry) : VCSpecKind :=
  entry.spec.kind

def VCSpecEntry.lookupKey (entry : VCSpecEntry) : VCSpecLookupKey :=
  entry.spec.lookupKey

/-- Persistent state for the `@[vcspec]` registry.

* `all` retains insertion order, used by `kind`-indexed iteration helpers.
* `unary` indexes unary entries by their `comp` `Sym.Pattern`.
* `relational` indexes relational entries by their `oa` `Sym.Pattern`;
  the right-hand head check happens at lookup time. -/
structure VCSpecRegistry where
  all : Array VCSpecEntry := #[]
  unary : DiscrTree VCSpecEntry := .empty
  relational : DiscrTree VCSpecEntry := .empty
  deriving Inhabited

private def VCSpecRegistry.addToTree (tree : DiscrTree VCSpecEntry) (entry : VCSpecEntry) :
    DiscrTree VCSpecEntry :=
  Lean.Meta.Sym.insertPattern tree entry.pattern entry

initialize vcSpecRegistry :
    SimpleScopedEnvExtension
      VCSpecEntry
      VCSpecRegistry ←
  registerSimpleScopedEnvExtension {
    addEntry := fun registry entry =>
      let registry := { registry with all := registry.all.push entry }
      match entry.lookupKey with
      | .unary _ =>
          { registry with unary := VCSpecRegistry.addToTree registry.unary entry }
      | .relational _ _ =>
          { registry with
              relational := VCSpecRegistry.addToTree registry.relational entry }
    initial := {}
  }

/-! ### `vcspec_simp` simp set

Auxiliary simp set used internally by the unary and relational tactics for
transformer-layer normalization (peeling `apply_wp`, running monadic `*.run`
projections, normalizing lifts, and so on). Mirror of `Loom.Tactic.lspecSimpExt`.

Users should write `@[vcspec]`; the attribute first tries to register the
declaration as a spec theorem and on failure falls back to inserting it into
`vcspec_simp`. This lets a single attribute handle both spec lemmas and the
normalization rewrites needed to massage a goal into spec-applicable shape.

This attribute is not intended to be used directly. -/
initialize vcSpecSimpExt : Meta.SimpExtension ←
  Meta.registerSimpAttr `vcspec_simp
    "simp theorems internally used by VCVio program-logic tactics"

/-- The accumulated simp set behind the `vcspec_simp` fallback layer of
`@[vcspec]`. Used by `runVCSpecSimp` to normalize transformer-stack `wp` goals
before spec dispatch. -/
def getVCSpecSimpTheorems : CoreM Meta.SimpTheorems :=
  vcSpecSimpExt.getTheorems

/-! ### Preprocessed-body head matchers

`Sym.preprocessType` aggressively unfolds reducible abbreviations (including our
own `Triple`, `wp`, `RelTriple`, `RelWP` wrappers) before handing the body to
the selector. These helpers match on both the folded (`OracleComp.ProgramLogic.…`)
and unfolded (`MAlgOrdered.…` / `MAlgRelOrdered.…`) heads so registrations are
robust to future reducibility shifts.
-/

/-- Unfolded cores of the unary triple / wp abbreviations; matched on the
preprocessed theorem body alongside the folded heads. -/
private def unaryTripleHeadNames : Array Name :=
  #[``OracleComp.ProgramLogic.Triple, ``MAlgOrdered.Triple, ``Std.Do'.Triple]

private def unaryWpHeadNames : Array Name :=
  #[``OracleComp.ProgramLogic.wp, ``MAlgOrdered.wp, ``Std.Do'.wp]

private def relTripleHeadNames : Array Name :=
  #[``OracleComp.ProgramLogic.Relational.RelTriple, ``MAlgRelOrdered.Triple, ``Std.Do'.RelTriple]

private def relWpHeadNames : Array Name :=
  #[``OracleComp.ProgramLogic.Relational.RelWP,
    ``MAlgRelOrdered.RelWP,
    ``MAlgRelOrdered.rwp,
    ``Std.Do'.rwp]

/-- Head check that tolerates varying numbers of implicit / instance arguments.
Each `@[vcspec]` target has a fixed number of *explicit* trailing arguments
(the precondition, computation(s), and postcondition); we only care that the
application head is one of the recognized constants. -/
private def headIsOneOf (e : Expr) (names : Array Name) : Bool :=
  names.any fun n => e.getAppFn.isConstOf n

/-- Extract the last `n` arguments of an application. Returns `none` if there
are fewer than `n` arguments. -/
private def trailingArgsN? (e : Expr) (n : Nat) : Option (Array Expr) :=
  let args := e.getAppArgs
  if n ≤ args.size then
    some <| args.extract (args.size - n) args.size
  else
    none

/-- Preprocessed-body variant of `tripleGoalParts?` that also matches the
unfolded `MAlgOrdered.Triple` head, as well as Loom2's `Std.Do'.Triple`
which carries an extra trailing exception postcondition. Returns
`(pre, oa, post)`. -/
private def tripleBodyParts? (body : Expr) : Option (Expr × Expr × Expr) := do
  let body := body.consumeMData
  unless headIsOneOf body unaryTripleHeadNames do none
  let n := if body.getAppFn.isConstOf ``Std.Do'.Triple then 4 else 3
  let args ← trailingArgsN? body n
  if n == 4 then
    let #[pre, oa, post, _epost] := args | none
    some (pre, oa, post)
  else
    let #[pre, oa, post] := args | none
    some (pre, oa, post)

/-- Preprocessed-body variant of `wpGoalParts?` that also matches the unfolded
`MAlgOrdered.wp` head and Loom2's `Std.Do'.wp` (which carries a trailing
exception postcondition). Returns `(oa, post)`. -/
private def wpBodyParts? (body : Expr) : Option (Expr × Expr) := do
  let body := body.consumeMData
  unless headIsOneOf body unaryWpHeadNames do none
  let n := if body.getAppFn.isConstOf ``Std.Do'.wp then 3 else 2
  let args ← trailingArgsN? body n
  if n == 3 then
    let #[oa, post, _epost] := args | none
    some (oa, post)
  else
    let #[oa, post] := args | none
    some (oa, post)

/-- Preprocessed-body variant of `rawWPGoalParts?` that also matches the
unfolded `MAlgOrdered.wp` head under `≤`. Returns `(pre, oa, post)`. -/
private def rawWpBodyParts? (body : Expr) : Option (Expr × Expr × Expr) := do
  let body := body.consumeMData
  unless body.isAppOfArity ``LE.le 4 || body.isAppOfArity ``Lean.Order.PartialOrder.rel 4 do
    none
  let pre := body.getArg! 2
  let rhs := body.getArg! 3
  let (oa, post) ← wpBodyParts? rhs
  some (pre, oa, post)

/-- Preprocessed-body variant of `relTripleGoalParts?` that also matches the
unfolded `MAlgRelOrdered.Triple` head and Loom2's `Std.Do'.RelTriple`.
The folded `RelTriple` has three explicit trailing args `(oa, ob, post)`;
the unfolded `MAlgRelOrdered.Triple` has four `(pre, oa, ob, post)`;
`Std.Do'.RelTriple` has six `(pre, oa, ob, post, epost₁, epost₂)`.
Returns `(oa, ob, post)` in all cases. -/
private def relTripleBodyParts? (body : Expr) : Option (Expr × Expr × Expr) := do
  let body := body.consumeMData
  let fn := body.getAppFn
  if fn.isConstOf ``OracleComp.ProgramLogic.Relational.RelTriple then
    let args ← trailingArgsN? body 3
    let #[oa, ob, post] := args | none
    some (oa, ob, post)
  else if fn.isConstOf ``MAlgRelOrdered.Triple then
    let args ← trailingArgsN? body 4
    let #[_pre, oa, ob, post] := args | none
    some (oa, ob, post)
  else if fn.isConstOf ``Std.Do'.RelTriple then
    let args ← trailingArgsN? body 6
    let #[_pre, oa, ob, post, _epost₁, _epost₂] := args | none
    some (oa, ob, post)
  else
    none

/-- Preprocessed-body variant of `relWPGoalParts?` that also matches the
unfolded `MAlgRelOrdered.rwp` head. Returns `(oa, ob, post)`. -/
private def relWpBodyParts? (body : Expr) : Option (Expr × Expr × Expr) := do
  let body := body.consumeMData
  unless headIsOneOf body relWpHeadNames do none
  let n := if body.getAppFn.isConstOf ``Std.Do'.rwp then 5 else 3
  let args ← trailingArgsN? body n
  if n == 5 then
    let #[oa, ob, post, _epost₁, _epost₂] := args | none
    some (oa, ob, post)
  else
    let #[oa, ob, post] := args | none
    some (oa, ob, post)

/-- Preprocessed-body variant of a raw relational WP goal under `≤` / `⊑`.
Returns `(pre, oa, ob, post)`. -/
private def rawRelWpBodyParts? (body : Expr) : Option (Expr × Expr × Expr × Expr) := do
  let body := body.consumeMData
  unless body.isAppOfArity ``LE.le 4 || body.isAppOfArity ``Lean.Order.PartialOrder.rel 4 do
    none
  let pre := body.getArg! 2
  let rhs := body.getArg! 3
  let (oa, ob, post) ← relWpBodyParts? rhs
  some (pre, oa, ob, post)

/-- Selector fed to `Sym.mkPatternFromDeclWithKey`. Given the preprocessed body
of a `@[vcspec]` theorem, returns the computation expression to use as the
pattern key, together with the normalized spec description and (for relational
entries) the right-hand head constant used as a secondary filter.

Handles both the folded (`Triple`, `wp`, `RelTriple`, `RelWP`) and unfolded
(`MAlgOrdered.Triple`, `MAlgOrdered.wp`, `MAlgRelOrdered.Triple`,
`MAlgRelOrdered.rwp`) heads because `Sym.preprocessType` aggressively unfolds
the abbreviations in the source theorem before we see the body. -/
private def selectVCSpecKey (body : Expr) :
    MetaM (Expr × NormalizedVCSpec × Option Name) := do
  let body := body.consumeMData
  if let some (_pre, oa, _post) := tripleBodyParts? body then
    let head ← headConstNameOrUnary oa
    let spec : NormalizedVCSpec := {
      kind := .unaryTriple
      lookupKey := .unary head
      compPattern := classifyUnaryCompPattern oa
    }
    return (oa, spec, none)
  if let some (_pre, oa, _post) := rawWpBodyParts? body then
    let head ← headConstNameOrUnary oa
    let spec : NormalizedVCSpec := {
      kind := .unaryWP
      lookupKey := .unary head
      compPattern := classifyUnaryCompPattern oa
    }
    return (oa, spec, none)
  if let some (oa, _post) := wpBodyParts? body then
    let head ← headConstNameOrUnary oa
    let spec : NormalizedVCSpec := {
      kind := .unaryWP
      lookupKey := .unary head
      compPattern := classifyUnaryCompPattern oa
    }
    return (oa, spec, none)
  if let some (oa, ob, _post) := relTripleBodyParts? body then
    let (leftHead, rightHead) ← relationalHeads oa ob
    let spec : NormalizedVCSpec := {
      kind := .relTriple
      lookupKey := .relational leftHead rightHead
      compPattern := classifyRelationalCompPattern oa ob
    }
    return (oa, spec, some rightHead)
  if let some (oa, ob, _post) := relWpBodyParts? body then
    let (leftHead, rightHead) ← relationalHeads oa ob
    let spec : NormalizedVCSpec := {
      kind := .relWP
      lookupKey := .relational leftHead rightHead
      compPattern := classifyRelationalCompPattern oa ob
    }
    return (oa, spec, some rightHead)
  if let some (_pre, oa, ob, _post) := rawRelWpBodyParts? body then
    let (leftHead, rightHead) ← relationalHeads oa ob
    let spec : NormalizedVCSpec := {
      kind := .relWP
      lookupKey := .relational leftHead rightHead
      compPattern := classifyRelationalCompPattern oa ob
    }
    return (oa, spec, some rightHead)
  throwError
    m!"@[vcspec] expects a theorem whose target is one of:\n\
    - a unary `Triple`\n\
    - a unary raw `wp` goal\n\
    - a relational `RelTriple`\n\
    - a relational raw `RelWP`\n\
    got:{indentExpr body}"
where
  /-- Extract the head constant of a preprocessed computation expression,
  tolerating `whnf`-reducible layers. -/
  headConstNameOrUnary (comp : Expr) : MetaM Name := do
    let comp ← whnfReducible (← instantiateMVars comp)
    match headConstName? comp with
    | some h => return h
    | none =>
        throwError
          m!"@[vcspec] only supports unary computations with a constant head symbol, got:\
          {indentExpr comp}"
  relationalHeads (oa ob : Expr) : MetaM (Name × Name) := do
    let oa ← whnfReducible (← instantiateMVars oa)
    let ob ← whnfReducible (← instantiateMVars ob)
    let some leftHead := headConstName? oa
      | throwError
          m!"@[vcspec] only supports relational left computations with a constant head symbol, got:\
          {indentExpr oa}"
    let some rightHead := headConstName? ob
      | throwError m!"@[vcspec] only supports relational right computations with a constant head \
          symbol, got:{indentExpr ob}"
    return (leftHead, rightHead)

/-- Build a registry entry for `decl` from its type by extracting the indexed
sub-expression and producing a `Sym.Pattern` for discrimination-tree indexing. -/
private def buildVCSpecEntry (decl : Name) (priority : Nat) : MetaM VCSpecEntry := do
  let (pattern, extras) ←
    Lean.Meta.Sym.mkPatternFromDeclWithKey decl selectVCSpecKey
  let (spec, rightHead?) := extras
  return { proof := .global decl, spec, pattern, rightHead?, priority }

initialize registerBuiltinAttribute {
  name := `vcspec
  descr := "Register a unary or relational program-logic theorem for vcgen/rvcgen \
    lookup, or a normalization simp lemma for the internal `vcspec_simp` set."
  applicationTime := AttributeApplicationTime.afterCompilation
  add := fun decl stx kind => MetaM.run' do
    let prio ← getAttrParamOptPrio stx[1]
    try
      let entry ← buildVCSpecEntry decl prio
      vcSpecRegistry.add entry kind
    catch specErr =>
      let env ← getEnv
      match getAttributeImpl env `vcspec_simp with
      | .error _ => throw specErr
      | .ok impl =>
          try
            let newStx ← `(attr| vcspec_simp)
            let newStx := newStx.raw.setArg 3 stx[1]
            impl.add decl newStx kind
          catch simpErr =>
            throwError "@[vcspec] failed to register `{decl}`:\n\
              - as a spec theorem: {specErr.toMessageData}\n\
              - as a `vcspec_simp` lemma: {simpErr.toMessageData}"
}

private def headOfWhnf (e : Expr) : MetaM (Option Name) := do
  let e ← whnfReducible (← instantiateMVars e)
  return headConstName? e

def getRegisteredUnaryVCSpecEntries (comp : Expr) : MetaM (Array VCSpecEntry) := do
  let comp ← instantiateMVars comp
  let comp ← whnfReducible comp
  let registry := vcSpecRegistry.getState (← getEnv)
  return Lean.Meta.Sym.getMatch registry.unary comp

/-- Retrieve unary `@[vcspec]` entries without reducible `whnf` on the computation.

This is only for raw `wp` structural dispatch, where the syntactic head is already
the surface we want to step and reducing zero/nil iterator terms can unfold into
larger monadic expressions. -/
def getRegisteredUnaryVCSpecEntriesNoWhnf (comp : Expr) : MetaM (Array VCSpecEntry) := do
  let comp ← instantiateMVars comp
  let registry := vcSpecRegistry.getState (← getEnv)
  return Lean.Meta.Sym.getMatch registry.unary comp

def getRegisteredRelationalVCSpecEntries (oa ob : Expr) : MetaM (Array VCSpecEntry) := do
  let oa ← instantiateMVars oa
  let oa ← whnfReducible oa
  let some rightHead ← headOfWhnf ob | return #[]
  let registry := vcSpecRegistry.getState (← getEnv)
  let candidates := Lean.Meta.Sym.getMatch registry.relational oa
  return candidates.filter fun entry =>
    match entry.rightHead? with
    | some h => h == rightHead
    | none => false

def getRegisteredUnaryVCSpecTheorems (comp : Expr) : MetaM (Array Name) := do
  return (← getRegisteredUnaryVCSpecEntries comp).filterMap (·.declName?)

def getRegisteredRelationalVCSpecTheorems (oa ob : Expr) : MetaM (Array Name) := do
  return (← getRegisteredRelationalVCSpecEntries oa ob).filterMap (·.declName?)

def getVCSpecEntriesOfKind (kind : VCSpecKind) : CoreM (Array VCSpecEntry) := do
  let registry := vcSpecRegistry.getState (← getEnv)
  return registry.all.filter (·.kind == kind)

def getVCSpecTheoremsOfKind (kind : VCSpecKind) : CoreM (Array Name) := do
  return (← getVCSpecEntriesOfKind kind).filterMap (·.declName?)

end OracleComp.ProgramLogic
