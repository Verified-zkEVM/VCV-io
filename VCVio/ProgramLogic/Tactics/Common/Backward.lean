/-
Copyright (c) 2026 Anonymized for double-blind review.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anonymized for double-blind review
-/

import Lean.Meta.Sym.Apply
import VCVio.ProgramLogic.Tactics.Common.Registry

/-!
# Backward application for VCSpec entries

Shared native application helpers for `@[vcspec]` entries.
-/

open Lean Elab Tactic Meta

namespace OracleComp.ProgramLogic

/-- Cached VCVio wrapper around Lean's symbolic backward rule. The source
entry is kept for diagnostics and replay text. -/
structure VCSpecBackwardRule where
  source : VCSpecEntry
  rawGoal : Bool
  proof : AbstractMVarsResult
  declName : Name
  rule : Lean.Meta.Sym.BackwardRule

/-- Cache key for global `@[vcspec]` backward rules.

Local hypotheses and raw syntax proofs are intentionally not cached here.
For global declarations, the declaration name fixes the theorem body while the
raw/folded mode and normalized `VCSpecKind` select the consequence wrapper shape.
Carrier, WP/RWP instance, exception-post, and state arguments remain abstracted
in the cached proof and are reopened freshly at each application. If future local
or structurally specialized entries are cached, this key should be widened
rather than reused. -/
private abbrev VCSpecBackwardRuleCacheKey := Name × Bool × Nat

private def VCSpecKind.cacheKey : VCSpecKind → Nat
  | .unaryTriple => 0
  | .unaryWP => 1
  | .relTriple => 2
  | .relWP => 3

private def VCSpecKind.traceLabel : VCSpecKind → String
  | .unaryTriple => "unaryTriple"
  | .unaryWP => "unaryWP"
  | .relTriple => "relTriple"
  | .relWP => "relWP"

private def rawGoalTraceLabel (rawGoal : Bool) : String :=
  if rawGoal then "raw" else "folded"

initialize vcSpecBackwardRuleCache :
    IO.Ref (Std.HashMap VCSpecBackwardRuleCacheKey VCSpecBackwardRule) ←
  IO.mkRef {}

private def traceVCSpecCacheEvent (event : String) (entry : VCSpecEntry)
    (rawGoal : Bool) : MetaM Unit := do
  if vcvio.vcgen.traceCachedRules.get (← getOptions) then
    let source := entry.declName?.map Name.toString |>.getD "<local>"
    logInfo m!"[vcspec cache] {event} `{source}` \
      ({rawGoalTraceLabel rawGoal}, {entry.kind.traceLabel})"

private def instantiateProofNoBridge (proof : Lean.Elab.Tactic.Do.SpecAttr.SpecProof) :
    MetaM (Array Expr × Array BinderInfo × Expr × Expr) := do
  let prf ←
    match proof with
    | .global declName => mkConstWithFreshMVarLevels declName
    | .local fvarId => pure <| mkFVar fvarId
    | .stx _ _ proof => pure proof
  let type ← instantiateMVars (← inferType prf)
  let (xs, bis, type) ← forallMetaTelescope type
  let prf := prf.beta xs
  return (xs, bis, prf, type)

/--
If `(prf, type)` proves a `Std.Do'.Triple`, return the corresponding
`pre ⊑ wp ...` proof via `Std.Do'.Triple.iff`.
Relational `Std.Do'.RelTriple` is a reducible definition, so later raw
normalization sees it by weak-head reducing the type to `pre ⊑ rwp ...`.
Otherwise return the proof unchanged.
-/
private def bridgeTriple? (prf type : Expr) : MetaM (Expr × Expr) := do
  let type ← whnfR type
  if type.isAppOfArity ``Std.Do'.Triple 12 then
    let .const _ lvls := type.getAppFn
      | return (prf, type)
    let args := type.getAppArgs
    let tripleIff := mkAppN (mkConst ``Std.Do'.Triple.iff lvls)
      #[ args[0]!,  -- m
         args[1]!,  -- Pred
         args[2]!,  -- EPred
         args[4]!,  -- Monad
         args[5]!,  -- Assertion Pred
         args[6]!,  -- Assertion EPred
         args[7]!,  -- WP
         args[3]!,  -- α
         args[9]!,  -- x
         args[8]!,  -- pre
         args[10]!, -- post
         args[11]!  -- epost
       ]
    let prf' ← mkAppM ``Iff.mp #[tripleIff, prf]
    let type' ← instantiateMVars (← inferType prf')
    return (prf', type')
  return (prf, type)

/-- Extract the predicate carrier from a raw order relation. -/
private def rawOrderCarrier? (type : Expr) : MetaM (Option Expr) := do
  let type ← whnfR type
  if type.isAppOfArity ``Lean.Order.PartialOrder.rel 4 ||
      type.isAppOfArity ``LE.le 4 then
    return some (type.getArg! 0)
  return none

/-- If a raw order goal fixes the predicate carrier, push that information into
a universe-polymorphic `⊑` / `≤` proof before `Meta.apply`. -/
private def fixPredFromGoal? (prfTy goalTy : Expr) : MetaM Unit := do
  let some prfPred ← rawOrderCarrier? prfTy | return
  let some goalPred ← rawOrderCarrier? goalTy | return
  _ ← isDefEq prfPred goalPred

/-- A goal whose target is already in `≤`/`⊑` weakest-precondition form. -/
private def isRawBackwardGoal (target : Expr) : MetaM Bool := do
  let target ← whnfR target
  return target.isAppOfArity ``LE.le 4 ||
    target.isAppOfArity ``Lean.Order.PartialOrder.rel 4

private def rawRelParts? (type : Expr) : MetaM (Option (Expr × Expr)) := do
  let type ← whnfR type
  if type.isAppOfArity ``Lean.Order.PartialOrder.rel 4 ||
      type.isAppOfArity ``LE.le 4 then
    return some (type.getArg! 2, type.getArg! 3)
  return none

private def stdDoWpParts? (rhs : Expr) : Option (Expr × Expr × Expr) := do
  let rhs := rhs.consumeMData
  unless rhs.getAppFn.isConstOf ``Std.Do'.wp do none
  let args := rhs.getAppArgs
  unless args.size ≥ 3 do none
  let oa := args[args.size - 3]!
  let post := args[args.size - 2]!
  let epost := args[args.size - 1]!
  some (oa, post, epost)

private def stdDoRelWpParts? (rhs : Expr) : Option (Expr × Expr × Expr × Expr × Expr) := do
  let rhs := rhs.consumeMData
  unless rhs.getAppFn.isConstOf ``Std.Do'.rwp do none
  let args := rhs.getAppArgs
  unless args.size ≥ 5 do none
  let oa := args[args.size - 5]!
  let ob := args[args.size - 4]!
  let post := args[args.size - 3]!
  let epost₁ := args[args.size - 2]!
  let epost₂ := args[args.size - 1]!
  some (oa, ob, post, epost₁, epost₂)

private def unaryTripleParts? (type : Expr) : Option (Expr × Expr × Expr) := do
  let type := type.consumeMData
  if type.getAppFn.isConstOf ``OracleComp.ProgramLogic.Triple then
    let args := type.getAppArgs
    unless args.size ≥ 3 do none
    return (args[args.size - 3]!, args[args.size - 2]!, args[args.size - 1]!)
  if type.getAppFn.isConstOf ``Std.Do'.Triple then
    let args := type.getAppArgs
    unless args.size ≥ 4 do none
    return (args[args.size - 4]!, args[args.size - 3]!, args[args.size - 2]!)
  none

private def mkOrderRel (lhs rhs : Expr) : MetaM Expr := do
  let pred ← inferType lhs
  mkAppOptM ``Lean.Order.PartialOrder.rel #[some pred, none, some lhs, some rhs]

private def mkLE (lhs rhs : Expr) : MetaM Expr := do
  let α ← inferType lhs
  mkAppOptM ``LE.le #[some α, none, some lhs, some rhs]

private def rawOrderParts? (type : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let type ← whnfR type
  if type.isAppOfArity ``Lean.Order.PartialOrder.rel 4 ||
      type.isAppOfArity ``LE.le 4 then
    return some (type.getArg! 0, type.getArg! 2, type.getArg! 3)
  return none

private def mkOrderRelTrans (hxy hyz : Expr) : MetaM Expr := do
  let hxyTy ← instantiateMVars (← inferType hxy)
  let hyzTy ← instantiateMVars (← inferType hyz)
  let some (pred, x, y) ← rawOrderParts? hxyTy
    | mkAppM ``Lean.Order.PartialOrder.rel_trans #[hxy, hyz]
  let some (_, _, z) ← rawOrderParts? hyzTy
    | mkAppM ``Lean.Order.PartialOrder.rel_trans #[hxy, hyz]
  mkAppOptM ``Lean.Order.PartialOrder.rel_trans
    #[some pred, none, some x, some y, some z, some hxy, some hyz]

/-- Build the pointwise postcondition premise used when a concrete unary post
from a spec theorem is generalized to the goal's postcondition. -/
private def mkUnaryPostPointwisePremise (postSpec postTarget postTy : Expr) :
    MetaM Expr := do
  let .forallE _ α _ _ := postTy.consumeMData
    | throwError "expected a unary postcondition, got:{indentExpr postTy}"
  withLocalDeclD `a α fun a => do
    let lhs := mkApp postSpec a
    let rhs := mkApp postTarget a
    let rel ← mkOrderRel lhs rhs
    mkForallFVars #[a] rel

/-- Build the pointwise relational-postcondition premise used when a concrete
relational post from a spec theorem is generalized to the goal's postcondition. -/
private def mkRelPostPointwisePremise (postSpec postTarget postTy : Expr) :
    MetaM Expr := do
  let .forallE _ α body _ := postTy.consumeMData
    | throwError "expected a relational postcondition, got:{indentExpr postTy}"
  let .forallE _ β _ _ := body.consumeMData
    | throwError "expected a binary relational postcondition, got:{indentExpr postTy}"
  withLocalDeclD `a α fun a => do
    withLocalDeclD `b β fun b => do
      let lhs := mkApp2 postSpec a b
      let rhs := mkApp2 postTarget a b
      let rel ← mkOrderRel lhs rhs
      mkForallFVars #[a, b] rel

/-- Build the pointwise postcondition premise used when a concrete folded unary
`Triple` theorem is generalized to the goal's postcondition. -/
private def mkUnaryPostLEPremise (postSpec postTarget postTy : Expr) :
    MetaM Expr := do
  let .forallE _ α _ _ := postTy.consumeMData
    | throwError "expected a unary postcondition, got:{indentExpr postTy}"
  withLocalDeclD `a α fun a => do
    let lhs := mkApp postSpec a
    let rhs := mkApp postTarget a
    let rel ← mkLE lhs rhs
    mkForallFVars #[a] rel

private def mkUnaryPostLERfl (post postTy : Expr) : MetaM Expr := do
  let .forallE _ α _ _ := postTy.consumeMData
    | throwError "expected a unary postcondition, got:{indentExpr postTy}"
  withLocalDeclD `a α fun a => do
    let lhs := mkApp post a
    let h ← mkAppOptM ``le_rfl #[none, none, some lhs]
    mkLambdaFVars #[a] h

private def oracleSpecInstancesFrom (xs : Array Expr) : MetaM (Option Expr × Option Expr) := do
  let mut fintype? := none
  let mut inhabited? := none
  for x in xs do
    let ty ← whnfR (← inferType x)
    if ty.getAppFn.isConstOf ``OracleSpec.Fintype then
      fintype? := some x
    else if ty.getAppFn.isConstOf ``OracleSpec.Inhabited then
      inhabited? := some x
  return (fintype?, inhabited?)

private def mkTripleConseqApp (fintype? inhabited? : Option Expr)
    (pre preAbstract prog postSpec postAbstract hpre hpost specProof : Expr) : MetaM Expr :=
  mkAppOptM ``OracleComp.ProgramLogic.triple_conseq
    #[none, none, fintype?, inhabited?, none, some pre, some preAbstract, some prog,
      some postSpec, some postAbstract, some hpre, some hpost, some specProof]

/-- Generalize a folded unary `Triple pre prog post` proof into a reusable
backward-rule source by abstracting concrete `post` and always abstracting
`pre` through `triple_conseq`. -/
private def mkUnaryTripleBackwardProof (proofArgs : Array Expr)
    (pre _prog postSpec specProof : Expr) :
    MetaM Expr := do
  let (fintype?, inhabited?) ← oracleSpecInstancesFrom proofArgs
  let mut postAbstract := postSpec.consumeMData
  unless postAbstract.isMVar do
    let postTy ← inferType postSpec
    postAbstract ← mkFreshExprMVar (userName := `post) postTy
    let hpostTy ← mkUnaryPostLEPremise postSpec postAbstract postTy
    let hpost ← mkFreshExprMVar (userName := `postImpl) hpostTy
    let preTy ← inferType pre
    let preAbstract ← mkFreshExprMVar (userName := `pre) preTy
    let hpreTy ← mkLE preAbstract pre
    let hpre ← mkFreshExprMVar (userName := `vc) hpreTy
    return (← mkTripleConseqApp fintype? inhabited?
      pre preAbstract _prog postSpec postAbstract hpre hpost specProof)
  let preTy ← inferType pre
  let preAbstract ← mkFreshExprMVar (userName := `pre) preTy
  let hpreTy ← mkLE preAbstract pre
  let hpre ← mkFreshExprMVar (userName := `vc) hpreTy
  let postTy ← inferType postAbstract
  let hpost ← mkUnaryPostLERfl postAbstract postTy
  mkTripleConseqApp fintype? inhabited?
    pre preAbstract _prog postAbstract postAbstract hpre hpost specProof

/-- Generalize a raw unary `pre ⊑ wp prog post epost` proof into a reusable
backward rule source by abstracting concrete `post` and always abstracting
`pre` through transitivity. This is the unary, flat-carrier subset of Loom2's
`mkSpecBackwardProof`. -/
private def mkUnarySpecBackwardProof (pre rhs specProof : Expr) : MetaM Expr := do
  let some (prog, postSpec, epostSpec) := stdDoWpParts? rhs
    | throwError "expected a Std.Do'.wp RHS, got:{indentExpr rhs}"
  let mut postAbstract := postSpec.consumeMData
  let mut specApplied := specProof
  unless postAbstract.isMVar do
    let postTy ← inferType postSpec
    postAbstract ← mkFreshExprMVar (userName := `post) postTy
    let hpostTy ← mkUnaryPostPointwisePremise postSpec postAbstract postTy
    let hpost ← mkFreshExprMVar (userName := `postImpl) hpostTy
    specApplied ←
      mkAppM ``Std.Do'.WP.wp_consequence_rel
        #[prog, postSpec, postAbstract, epostSpec, hpost, specApplied]
  let preTy ← inferType pre
  let preAbstract ← mkFreshExprMVar (userName := `pre) preTy
  let hpreTy ← mkOrderRel preAbstract pre
  let hpre ← mkFreshExprMVar (userName := `vc) hpreTy
  mkOrderRelTrans hpre specApplied

/-- Generalize a raw relational `pre ⊑ rwp left right post epost₁ epost₂`
proof into a reusable backward rule source. This is the relational analogue of
`mkUnarySpecBackwardProof`; qualitative and quantitative carriers share this
path once they are expressed as `Std.Do'.RelTriple` / raw `Std.Do'.rwp`. -/
private def mkRelSpecBackwardProof (pre rhs specProof : Expr) : MetaM Expr := do
  let some (oa, ob, postSpec, epost₁, epost₂) := stdDoRelWpParts? rhs
    | throwError "expected a Std.Do'.rwp RHS, got:{indentExpr rhs}"
  let mut postAbstract := postSpec.consumeMData
  let mut specApplied := specProof
  unless postAbstract.isMVar do
    let postTy ← inferType postSpec
    postAbstract ← mkFreshExprMVar (userName := `post) postTy
    let hpostTy ← mkRelPostPointwisePremise postSpec postAbstract postTy
    let hpost ← mkFreshExprMVar (userName := `postImpl) hpostTy
    specApplied ←
      mkAppM ``Std.Do'.RelWP.rwp_consequence_rel
        #[oa, ob, postSpec, postAbstract, epost₁, epost₂, hpost, specApplied]
  let preTy ← inferType pre
  let preAbstract ← mkFreshExprMVar (userName := `pre) preTy
  let hpreTy ← mkOrderRel preAbstract pre
  let hpre ← mkFreshExprMVar (userName := `vc) hpreTy
  mkOrderRelTrans hpre specApplied

private def mkBackwardRuleFromProofExpr (prf : Expr) :
    MetaM (AbstractMVarsResult × Name × Lean.Meta.Sym.BackwardRule) := do
  let prf ← instantiateMVars prf
  let res ← abstractMVars prf
  let type ← instantiateMVars (← inferType res.expr)
  let decl ← mkAuxLemma res.paramNames.toList type res.expr
  let rule ← Lean.Meta.Sym.mkBackwardRuleFromDecl decl
  return (res, decl, rule)

private def mkVCSpecBackwardRule (entry : VCSpecEntry) (rawGoal : Bool) :
    MetaM VCSpecBackwardRule := do
  let (xsNoBridge, _bisNoBridge, prfNoBridge, typeNoBridge) ←
    instantiateProofNoBridge entry.proof
  let (_xs, _bis, prf, type) ← entry.proof.instantiate
  let (prf, type) ←
    if rawGoal then
      bridgeTriple? prf type
    else
      pure (prf, type)
  let prf ←
    if !rawGoal then
      match unaryTripleParts? typeNoBridge with
      | some (pre, prog, post) =>
          mkUnaryTripleBackwardProof xsNoBridge pre prog post prfNoBridge
      | none =>
          match ← rawRelParts? type with
          | some (pre, rhs) =>
              if (stdDoWpParts? rhs).isSome then
                mkUnarySpecBackwardProof pre rhs prf
              else if (stdDoRelWpParts? rhs).isSome then
                mkRelSpecBackwardProof pre rhs prf
              else
                pure prf
          | none => pure prf
    else
      match ← rawRelParts? type with
      | some (pre, rhs) =>
          if (stdDoWpParts? rhs).isSome then
            mkUnarySpecBackwardProof pre rhs prf
          else if (stdDoRelWpParts? rhs).isSome then
            mkRelSpecBackwardProof pre rhs prf
          else
            pure prf
      | none => pure prf
  let (proof, declName, rule) ← mkBackwardRuleFromProofExpr prf
  return { source := entry, rawGoal, proof, declName, rule }

private def mkVCSpecBackwardRuleTimed (entry : VCSpecEntry) (rawGoal : Bool) :
    MetaM VCSpecBackwardRule := do
  if vcvio.vcgen.time.get (← getOptions) then
    let (rule, ns) ← timeNs (mkVCSpecBackwardRule entry rawGoal)
    addCachedRuleBuildTime ns
    return rule
  else
    mkVCSpecBackwardRule entry rawGoal

private def getVCSpecBackwardRuleCached (entry : VCSpecEntry) (rawGoal : Bool) :
    MetaM VCSpecBackwardRule := do
  let some declName := entry.declName?
    | traceVCSpecCacheEvent "uncached-build" entry rawGoal
      mkVCSpecBackwardRuleTimed entry rawGoal
  -- Only global declarations use the shared cache. Local hypotheses and syntax
  -- proofs can share pretty names while carrying different closed-over terms, so
  -- they must build a fresh rule unless the cache key grows expression identity.
  let key : VCSpecBackwardRuleCacheKey := (declName, rawGoal, entry.kind.cacheKey)
  let cache ← vcSpecBackwardRuleCache.get
  match cache[key]? with
  | some rule =>
      addCachedRuleHit
      traceVCSpecCacheEvent "hit" entry rawGoal
      return rule
  | none =>
      addCachedRuleMiss
      traceVCSpecCacheEvent "miss" entry rawGoal
      let rule ← mkVCSpecBackwardRuleTimed entry rawGoal
      vcSpecBackwardRuleCache.modify fun cache => cache.insert key rule
      return rule

/-- Whether applying this registered theorem is expected to leave an ordinary
proof obligation, such as an auxiliary premise. Instance arguments and data
arguments are ignored. -/
def VCSpecEntry.hasProofPremise (entry : VCSpecEntry) : MetaM Bool := do
  let (xs, bis, _prf, _type) ← entry.proof.instantiate
  for x in xs, bi in bis do
    if bi == .default then
      if ← isProp (← inferType x) then
        return true
  return false

/-- Apply a raw unary `@[vcspec]` theorem under consequence, constructing the
proof directly against the current target. This is the unary analogue of the
direct raw relational path and covers raw `Std.Do'.wp` goals with `epost⟨⟩`
without going through theorem-syntax replay. -/
def VCSpecEntry.tryApplyRawUnaryConsequence (entry : VCSpecEntry) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  let goalTy ← instantiateMVars (← mvarId.getType)
  let some (preTarget, rhsTarget) ← rawRelParts? goalTy
    | return none
  let some (progTarget, postTarget, _epostTarget) := stdDoWpParts? rhsTarget
    | return none
  let (_xs, _bis, specProof, specType) ← entry.proof.instantiate
  let some (preSpec, rhsSpec) ← rawRelParts? specType
    | return none
  let some (progSpec, postSpec, epostSpec) := stdDoWpParts? rhsSpec
    | return none
  unless ← isDefEq progSpec progTarget do
    return none
  let postTy ← inferType postSpec
  let hpostTy ← mkUnaryPostPointwisePremise postSpec postTarget postTy
  let hpost ← mkFreshExprMVar (userName := `postImpl) hpostTy
  let specApplied ←
    mkAppM ``Std.Do'.WP.wp_consequence_rel
      #[progSpec, postSpec, postTarget, epostSpec, hpost, specProof]
  let hpreTy ← mkOrderRel preTarget preSpec
  let hpre ← mkFreshExprMVar (userName := `vc) hpreTy
  let prf ← mkOrderRelTrans hpre specApplied
  try
    let subgoals ← mvarId.apply prf
    return some subgoals
  catch _ =>
    return none

/-- Apply a raw unary consequence proof for a `@[vcspec]` entry to the current
main goal, preserving tail goals. -/
def runVCSpecEntryRawUnaryConsequence (entry : VCSpecEntry) : TacticM Bool := do
  match ← getGoals with
  | [] => return false
  | goal :: rest =>
      match ← liftMetaM <| entry.tryApplyRawUnaryConsequence goal with
      | none => return false
      | some subgoals =>
          setGoals (subgoals ++ rest)
          return true

/-- Apply a raw relational `@[vcspec]` theorem under consequence, constructing
the consequence proof against the current target directly. This avoids asking
elaboration to infer the target `rwp` shape from an underscore-heavy `refine`
term, which is expensive for premised raw relational rules. -/
def VCSpecEntry.tryApplyRawRelConsequence (entry : VCSpecEntry) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  let goalTy ← instantiateMVars (← mvarId.getType)
  let some (preTarget, rhsTarget) ← rawRelParts? goalTy
    | return none
  let some (oaTarget, obTarget, postTarget, _epostTarget₁, _epostTarget₂) :=
      stdDoRelWpParts? rhsTarget
    | return none
  let (_xs, _bis, specProof, specType) ← entry.proof.instantiate
  let some (preSpec, rhsSpec) ← rawRelParts? specType
    | return none
  let some (oaSpec, obSpec, postSpec, epostSpec₁, epostSpec₂) :=
      stdDoRelWpParts? rhsSpec
    | return none
  unless (← isDefEq oaSpec oaTarget) && (← isDefEq obSpec obTarget) do
    return none
  let postTy ← inferType postSpec
  let hpostTy ← mkRelPostPointwisePremise postSpec postTarget postTy
  let hpost ← mkFreshExprMVar (userName := `postImpl) hpostTy
  let specApplied ←
    mkAppM ``Std.Do'.RelWP.rwp_consequence_rel
      #[oaSpec, obSpec, postSpec, postTarget, epostSpec₁, epostSpec₂, hpost, specProof]
  let hpreTy ← mkOrderRel preTarget preSpec
  let hpre ← mkFreshExprMVar (userName := `vc) hpreTy
  let prf ← mkOrderRelTrans hpre specApplied
  try
    let subgoals ← mvarId.apply prf
    return some subgoals
  catch _ =>
    return none

/-- Apply a raw relational consequence proof for a `@[vcspec]` entry to the
current main goal, preserving tail goals. -/
def runVCSpecEntryRawRelConsequence (entry : VCSpecEntry) : TacticM Bool := do
  match ← getGoals with
  | [] => return false
  | goal :: rest =>
      match ← liftMetaM <| entry.tryApplyRawRelConsequence goal with
      | none => return false
      | some subgoals =>
          setGoals (subgoals ++ rest)
          return true

private def VCSpecBackwardRule.applyProof (rule : VCSpecBackwardRule) (mvarId : MVarId)
    (goalTy : Expr) : MetaM (Option (List MVarId)) := do
  try
    let (_xs, _bis, prf) ← openAbstractMVarsResult rule.proof
    let prfTy ← instantiateMVars (← inferType prf)
    fixPredFromGoal? prfTy goalTy
    let subgoals ← mvarId.apply prf
    return some subgoals
  catch _ =>
    return none

/-- Try to apply a cached symbolic backward rule for a registered `@[vcspec]`
entry. Unary and relational rules are normalized through raw `wp` / `rwp`
sources when their theorem statements expose those forms definitionally. -/
def VCSpecEntry.tryApplyCachedBackward (entry : VCSpecEntry) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  let goalTy ← instantiateMVars (← mvarId.getType)
  let rawGoal ← isRawBackwardGoal goalTy
  let rule ← getVCSpecBackwardRuleCached entry rawGoal
  if rawGoal then
    return (← rule.applyProof mvarId goalTy)
  let symResult ←
    try
      Lean.Meta.Sym.SymM.run <| rule.rule.apply mvarId
    catch _ =>
      pure .failed
  match symResult with
  | .failed =>
      -- `Sym.BackwardRule` matches against its preprocessed pattern. Some
      -- folded VCVio-facing goals are still better handled by Lean's ordinary
      -- elaborated application, but we still apply the cached abstracted proof
      -- source, not the original theorem entry.
      rule.applyProof mvarId goalTy
  | .goals subgoals => return some subgoals

/-- Try to apply a registered `@[vcspec]` entry directly to a goal metavariable.

This instantiates the stored `SpecProof`, bridges `Triple` proofs when the goal
is already in raw weakest-precondition form, applies with fresh metavariables,
and returns the generated subgoals. Goal-specific close passes remain in the
unary and relational planners because they know which leaf rules are cheap and
valid for their logic. -/
def VCSpecEntry.tryApplyBackward (entry : VCSpecEntry) (mvarId : MVarId) :
    MetaM (Option (List MVarId)) := do
  let (_xs, _bis, prf, type) ← entry.proof.instantiate
  let goalTy ← instantiateMVars (← mvarId.getType)
  let (prf, type) ←
    if ← isRawBackwardGoal goalTy then
      bridgeTriple? prf type
    else
      pure (prf, type)
  fixPredFromGoal? type goalTy
  try
    let subgoals ← mvarId.apply prf
    return some subgoals
  catch _ =>
    return none

/-- Apply a `@[vcspec]` entry to the current main goal, preserving the tail goals.

This helper performs only the theorem application. Callers should run their
existing cheap close pass afterwards. -/
def runVCSpecEntryBackward (entry : VCSpecEntry) : TacticM Bool := do
  match ← getGoals with
  | [] => return false
  | goal :: rest =>
      match ← liftMetaM <| entry.tryApplyBackward goal with
      | none => return false
      | some subgoals =>
          setGoals (subgoals ++ rest)
          return true

/-- Apply a cached symbolic backward rule for a `@[vcspec]` entry to the
current main goal, preserving the tail goals. -/
def runVCSpecEntryCachedBackward (entry : VCSpecEntry) : TacticM Bool := do
  match ← getGoals with
  | [] => return false
  | goal :: rest =>
      match ← liftMetaM <| entry.tryApplyCachedBackward goal with
      | none => return false
      | some subgoals =>
          setGoals (subgoals ++ rest)
          return true

/-! ## VCSpec simp dispatch -/

/-- Run the cached `vcspec_simp` simp set on the main goal target, swallowing
errors and unchanged-goal failures.

This is the single replacement for the previous open-coded `simp only [...]`
blocks that peeled transformer `wp` layers (`apply_wp`, `*.run`, lifts,
`Std.Do'.EPost.cons.push*`, `MAlgOrdered.wp_*`, the `Loom.wp_eq_mAlgOrdered_wp`
bridges, and the assorted monad/algebra rewrites). Tag a new normalization
lemma with `@[vcspec_simp]` (or rely on the `@[vcspec]` fallback) instead of
appending it to a tactic-local simp list. -/
def runVCSpecSimp : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let thms ← liftMetaM getVCSpecSimpTheorems
  let ctx ← Simp.mkContext
    (config := { failIfUnchanged := false })
    (simpTheorems := #[thms])
    (congrTheorems := (← getSimpCongrTheorems))
  try
    let (result?, _) ← Lean.Meta.simpTarget goal ctx
    match result? with
    | none => replaceMainGoal []
    | some goal' => replaceMainGoal [goal']
  catch _ =>
    pure ()

end OracleComp.ProgramLogic
