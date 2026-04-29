module

public meta import Lean
public meta import VCVioWidgets.GameHop.Hints
public meta import VCVioWidgets.GameHop.Model
public meta import VCVioWidgets.GameHop.Registry

public meta section

namespace VCVioWidgets
namespace GameHop

open Lean Meta

private def gameEquivConst : Name :=
  Name.str (Name.str (Name.str .anonymous "OracleComp") "ProgramLogic") "GameEquiv"

inductive DiagramInferenceError where
  | multipleRoots (roots : Array Name)
  | inferenceFailed (root : Name) (message : String)
  deriving Inhabited, Repr

namespace DiagramInferenceError

def message : DiagramInferenceError → String
  | .multipleRoots roots =>
      let names := String.intercalate ", " <| roots.toList.map toString
      s!"Multiple game-hop roots are registered for this module: {names}"
  | .inferenceFailed root msg =>
      s!"Could not infer a game-hop diagram for `{root}`: {msg}"

end DiagramInferenceError

private def declBasename : Name → String
  | .anonymous => ""
  | .str _ s => s
  | .num p _ => declBasename p

private def humanizeIdentifier (s : String) : String :=
  Id.run do
    let mut out := ""
    let mut prevWasLower := false
    for c in s.toList do
      if c = '_' then
        if !out.endsWith " " then
          out := out ++ " "
        prevWasLower := false
      else
        if prevWasLower && c.isUpper then
          out := out ++ " "
        out := out.push c
        prevWasLower := c.isLower
    out.trimAscii.toString

private def humanizeName (name : Name) : String :=
  humanizeIdentifier (declBasename name)

private def ppExprString (e : Expr) : MetaM String := do
  withOptions
      (fun opts =>
        opts.set `format.width (52 : Nat)
          |>.set `pp.universes false
          |>.set `pp.fullNames false) do
    let fmt ← PrettyPrinter.ppExpr e
    return (Format.pretty fmt 52).trimAscii.toString

private def trailingArgs? (e : Expr) (n : Nat) : Option (Array Expr) :=
  let args := e.consumeMData.getAppArgs
  if _ : n ≤ args.size then
    some <| args.extract (args.size - n) args.size
  else
    none

private def findAppWithHead? (head : Name) (e : Expr) : Option Expr :=
  (e.find? fun e' => e'.consumeMData.getAppFn.isConstOf head).map Expr.consumeMData

private def valueConstants (info : ConstantInfo) : Array Name :=
  match info.value? with
  | some value => value.getUsedConstants
  | none => #[]

private def isPrivateLike (declName : Name) : Bool :=
  let s := declName.toString
  s.contains "_private" || s.contains "match_" || s.contains "proof_"

private def isTheoremInfo : ConstantInfo → Bool
  | .thmInfo _ => true
  | _ => false

private def anchorRefForDecl (declName : Name) (preferResult : Bool := false) :
    MetaM (Option AnchorRef) := do
  let info ← getConstInfo declName
  return some <| match info with
    | .thmInfo _ =>
        if preferResult then AnchorRef.result declName else AnchorRef.thm declName
    | .defnInfo _ => AnchorRef.defn declName
    | .opaqueInfo _ => AnchorRef.defn declName
    | .axiomInfo _ => AnchorRef.defn declName
    | .quotInfo _ => AnchorRef.defn declName
    | .inductInfo _ => AnchorRef.defn declName
    | .ctorInfo _ => AnchorRef.defn declName
    | .recInfo _ => AnchorRef.defn declName

private def sameModule (modName declName : Name) : MetaM Bool := do
  match (← Lean.findModuleOf? declName) with
  | some declMod => return declMod == modName
  | none => return (← getEnv).mainModule == modName

private def isFunctionValuedExpr (expr : Expr) : MetaM Bool := do
  let ty ← whnf (← inferType expr)
  match ty.consumeMData with
  | .forallE .. => return true
  | _ => return false

private structure CompRef where
  key : String
  title : String
  kind : NodeKind
  anchor? : Option AnchorRef := none
  snippets : Array CodeSnippet := #[]
  deriving Inhabited, Repr

private def compTitleFromExpr (expr : Expr) : MetaM String := do
  let some head := expr.consumeMData.getAppFn.constName?
    | return "game"
  let base := declBasename head
  let args := expr.consumeMData.getAppArgs
  if base = "PerfectSecrecyCipherGivenMsgExp" then
    match args.back? with
    | some msg => return s!"Cipher game for {← ppExprString msg}"
    | none => return "Cipher game"
  if base = "IND_CPA_HybridGame" then
    match args.back? with
    | some idx => return s!"Hybrid {← ppExprString idx}"
    | none => return "Hybrid game"
  if base = "IND_CPA_game" then
    return "IND-CPA game"
  return humanizeName head

private def compKindFromExpr (expr : Expr) : NodeKind :=
  match expr.consumeMData.getAppFn.constName? with
  | some head =>
      if declBasename head |>.contains "Hybrid" then .hybrid else .game
  | none => .game

private def shouldRejectCompHead (head : Name) : Bool :=
  let base := declBasename head
  base = "ddhExp" || base = "ddhExpReal" || base = "ddhExpRand" ||
    base.contains "Reduction" || base.contains "advantage"

private def looksLikeComputationHead (head : Name) : Bool :=
  let base := declBasename head
  let lower := base.toLower
  lower.contains "game" || lower.contains "exp"

private def mkCompRef (rootModule : Name) (expr : Expr) (allowImported : Bool := false) :
    MetaM (Option CompRef) := do
  let expr := expr.consumeMData
  let some head := expr.getAppFn.constName?
    | return none
  if shouldRejectCompHead head then
    return none
  if !looksLikeComputationHead head then
    return none
  if ← isFunctionValuedExpr expr then
    return none
  if !allowImported && !(← sameModule rootModule head) then
    return none
  let key ← ppExprString expr
  let title ← compTitleFromExpr expr
  let anchor? ← anchorRefForDecl head
  let info ← getConstInfo head
  let snippets :=
    match info with
    | .thmInfo _ => #[.declSignature head]
    | _ => #[.declSource head]
  return some {
    key
    title
    kind := compKindFromExpr expr
    anchor?
    snippets
  }

private def uniqueCompRefs (refs : Array CompRef) : Array CompRef :=
  Id.run do
    let mut seen : Std.HashSet String := {}
    let mut out := #[]
    for ref in refs do
      if !seen.contains ref.key then
        seen := seen.insert ref.key
        out := out.push ref
    out

private def extractGeneralCompRefs (rootModule : Name) (target : Expr) :
    MetaM (Array CompRef) := do
  let (_, refs) ← StateT.run (m := MetaM) (s := #[]) <|
    Lean.Meta.transform target (pre := fun expr => do
      if let some ref ← liftM <| mkCompRef rootModule expr then
        modify fun refs => refs.push ref
      return TransformStep.continue)
  return uniqueCompRefs refs

private def extractGameEquivSides? (rootModule : Name) (target : Expr) :
    MetaM (Option (CompRef × CompRef)) := do
  let some app := findAppWithHead? gameEquivConst target
    | return none
  let some args := trailingArgs? app 2
    | return none
  let #[lhs, rhs] := args
    | return none
  let some lhsRef ← mkCompRef rootModule lhs (allowImported := true)
    | return none
  let some rhsRef ← mkCompRef rootModule rhs (allowImported := true)
    | return none
  return some (lhsRef, rhsRef)

private inductive CandidateKind where
  | root
  | equivalence
  | equality
  | bound
  | endpoint
  | consequence
  deriving Inhabited, Repr, DecidableEq

private structure CandidateDecl where
  declName : Name
  depth : Nat
  kind : CandidateKind
  score : Nat
  targetText : String
  compRefs : Array CompRef
  directDeps : Array Name
  deriving Inhabited, Repr

private def scoreNameBonus (declName : Name) : Nat :=
  Id.run do
    let s := declName.toString.toLower
    let mut score : Nat := 0
    if s.contains "bound" then score := score + 5
    if s.contains "half" then score := score + 5
    if s.contains "equiv" then score := score + 4
    if s.contains "hybrid" then score := score + 3
    if s.contains "game" then score := score + 2
    if s.contains "reduction" then score := score + 2
    score

private def classifyCandidateKind (target : Expr) (targetText : String) (compRefs : Array CompRef) :
    CandidateKind :=
  if (findAppWithHead? gameEquivConst target).isSome then
    .equivalence
  else if compRefs.size ≤ 1 && targetText.contains "1 / 2" then
    .endpoint
  else if targetText.contains "≤" && !compRefs.isEmpty then
    .bound
  else if compRefs.size ≥ 2 then
    .equality
  else
    .consequence

private def scoreCandidateKind : CandidateKind → Nat
  | .root => 100
  | .equivalence => 40
  | .bound => 32
  | .endpoint => 30
  | .equality => 28
  | .consequence => 12

private def directLocalTheoremDependencies (modName declName : Name) : MetaM (Array Name) := do
  let info ← getConstInfo declName
  let used := info.type.getUsedConstants ++ valueConstants info
  let mut deps := #[]
  for dep in used do
    if dep != declName && !(isPrivateLike dep) && (← sameModule modName dep) then
      let depInfo ← getConstInfo dep
      if isTheoremInfo depInfo && !deps.contains dep then
        deps := deps.push dep
  return deps

private partial def collectRecursiveTheorems (modName : Name) (root : Name) (maxDepth : Nat := 3) :
    MetaM (Array (Name × Nat) × Std.HashMap Name (Array Name)) := do
  let rec go (frontier : List (Name × Nat)) (seen : Std.HashMap Name Nat)
      (depMap : Std.HashMap Name (Array Name)) :
      MetaM (Std.HashMap Name Nat × Std.HashMap Name (Array Name)) := do
    match frontier with
    | [] => return (seen, depMap)
    | (declName, depth) :: rest =>
        if seen.contains declName then
          go rest seen depMap
        else
          let deps ← directLocalTheoremDependencies modName declName
          let seen := seen.insert declName depth
          let depMap := depMap.insert declName deps
          let rest :=
            if depth < maxDepth then
              rest ++ deps.toList.map (fun dep => (dep, depth + 1))
            else
              rest
          go rest seen depMap
  let (seen, depMap) ← go [(root, 0)] {} {}
  let entries := seen.toList.toArray.filter (fun (declName, _) => declName != root)
  return (entries, depMap)

private def analyzeCandidate (rootModule : Name) (declName : Name) (depth : Nat)
    (depMap : Std.HashMap Name (Array Name)) : MetaM CandidateDecl := do
  let info ← getConstInfo declName
  let (xs, _, target) ← forallMetaTelescopeReducing info.type
  let targetText ← ppExprString target
  let compRefs ←
    match (← extractGameEquivSides? rootModule target) with
    | some (lhs, rhs) => pure #[lhs, rhs]
    | none => do
        let mut refs := #[]
        for x in xs do
          refs := refs ++ (← extractGeneralCompRefs rootModule (← inferType x))
        refs := refs ++ (← extractGeneralCompRefs rootModule target)
        pure (uniqueCompRefs refs)
  let kind := classifyCandidateKind target targetText compRefs
  return {
    declName
    depth
    kind
    score := scoreCandidateKind kind + scoreNameBonus declName
    targetText
    compRefs
    directDeps := match depMap.get? declName with
      | some deps => deps
      | none => #[]
  }

private def moduleTitle (modName : Name) : String :=
  let base := humanizeName modName
  if base.isEmpty then "Game hop"
  else s!"{base} game hop"

private def rootTitle (declName : Name) : String :=
  let base := declBasename declName
  if base.contains "_le_" || base.contains "bound_" then
    "Main theorem"
  else
    humanizeIdentifier base

private structure BuildState where
  nextId : Nat := 0
  keyToId : Std.HashMap String NodeId := {}
  nodes : Array GameNode := #[]
  edges : Array GameEdge := #[]
  edgeKeys : Std.HashSet String := {}
  primaryNodes : Std.HashMap Name NodeId := {}
  rootNode : NodeId := ""
  deriving Inhabited

private abbrev BuildM := StateT BuildState MetaM

private def ensureNode (key title : String) (kind : NodeKind) (anchor? : Option AnchorRef)
    (snippets : Array CodeSnippet := #[]) : BuildM NodeId := do
  let state ← get
  match state.keyToId.get? key with
  | some nodeId => return nodeId
  | none =>
      let nodeId := s!"n{state.nextId}"
      let summary :=
        match anchor? with
        | some _ => TextSource.fromAnchorDoc
        | none => .none
      let node : GameNode := {
        id := nodeId
        kind
        title
        summary
        anchor?
        snippets
      }
      set {
        state with
        nextId := state.nextId + 1
        keyToId := state.keyToId.insert key nodeId
        nodes := state.nodes.push node
      }
      return nodeId

private def addEdge (source target : NodeId) (kind : EdgeKind) (label : String)
    (anchor? : Option AnchorRef := none) (detail? : Option String := none)
    (notes : Array GameEdgeNote := #[]) : BuildM Unit := do
  let key := s!"{source}|{target}|{reprStr kind}|{label}|{anchor?.map (·.declName.toString)}"
  let state ← get
  if !state.edgeKeys.contains key then
    let edge : GameEdge := {
      source
      target
      kind
      label
      detail?
      anchor?
      notes
    }
    set {
      state with
      edgeKeys := state.edgeKeys.insert key
      edges := state.edges.push edge
    }

private def recordPrimaryNode (declName : Name) (nodeId : NodeId) : BuildM Unit := do
  modify fun state => { state with primaryNodes := state.primaryNodes.insert declName nodeId }

private def getPrimaryNode? (declName : Name) : BuildM (Option NodeId) := do
  return (← get).primaryNodes.get? declName

private def orderBridgeRefs (refs : Array CompRef) : Array CompRef :=
  if refs.size != 2 then refs else
  let lhs := refs[0]!
  let rhs := refs[1]!
  if lhs.kind = .hybrid && rhs.kind = .game then
    #[rhs, lhs]
  else
    refs

private def buildCompNode (ref : CompRef) : BuildM NodeId :=
  ensureNode s!"expr:{ref.key}" ref.title ref.kind ref.anchor? ref.snippets

private def applyCandidate (candidate : CandidateDecl) : BuildM Unit := do
  match candidate.kind with
  | .equivalence =>
      if candidate.compRefs.size = 2 then
        let lhsId ← buildCompNode candidate.compRefs[0]!
        let rhsId ← buildCompNode candidate.compRefs[1]!
        let anchor? ← liftM <| anchorRefForDecl candidate.declName
        addEdge lhsId rhsId .equivalence "GameEquiv" anchor?
        recordPrimaryNode candidate.declName rhsId
  | .endpoint =>
      let anchor? ← liftM <| anchorRefForDecl candidate.declName
      let endpointId ←
        ensureNode
          s!"theorem:{candidate.declName}"
          "Winning probability = 1 / 2"
          .endpoint
          anchor?
          #[.declSignature candidate.declName]
      recordPrimaryNode candidate.declName endpointId
      if let some ref := candidate.compRefs[0]? then
        let gameId ← buildCompNode ref
        addEdge gameId endpointId .equality "= 1 / 2" anchor?
  | .bound =>
      let refs := orderBridgeRefs candidate.compRefs
      if refs.size ≥ 2 then
        let lhsId ← buildCompNode refs[0]!
        let rhsId ← buildCompNode refs[1]!
        let anchor? ← liftM <| anchorRefForDecl candidate.declName
        addEdge lhsId rhsId .bound "bound" anchor?
        recordPrimaryNode candidate.declName rhsId
      else if let some ref := refs[0]? then
        let nodeId ← buildCompNode ref
        recordPrimaryNode candidate.declName nodeId
  | .equality =>
      let refs := orderBridgeRefs candidate.compRefs
      if refs.size ≥ 2 then
        let lhsId ← buildCompNode refs[0]!
        let rhsId ← buildCompNode refs[1]!
        let anchor? ← liftM <| anchorRefForDecl candidate.declName
        addEdge lhsId rhsId .equality "=" anchor?
        recordPrimaryNode candidate.declName rhsId
      else if let some ref := refs[0]? then
        let nodeId ← buildCompNode ref
        recordPrimaryNode candidate.declName nodeId
  | .consequence =>
      if let some ref := candidate.compRefs[0]? then
        let nodeId ← buildCompNode ref
        recordPrimaryNode candidate.declName nodeId
      else
        let anchor? ← liftM <| anchorRefForDecl candidate.declName
        let nodeId ←
          ensureNode
            s!"theorem:{candidate.declName}"
            (humanizeName candidate.declName)
            .result
            anchor?
            #[.declSignature candidate.declName]
        recordPrimaryNode candidate.declName nodeId
  | .root => pure ()

private partial def buildMainPath (rootId : NodeId) (edges : Array GameEdge) : List NodeId :=
  let incoming := edges.filter (fun edge => edge.target == rootId)
  match incoming[0]? with
  | none => [rootId]
  | some edge =>
      let path := buildMainPath edge.source edges
      if path.contains rootId then
        [rootId]
      else
        path ++ [rootId]

private def ensureRootNode (root : Name) : BuildM NodeId := do
  let anchor? ← liftM <| anchorRefForDecl root (preferResult := true)
  let nodeId ←
    ensureNode
      s!"root:{root}"
      (rootTitle root)
      .result
      anchor?
      #[.declSignature root]
  modify fun state => { state with rootNode := nodeId }
  recordPrimaryNode root nodeId
  return nodeId

private def chooseSelectedCandidates (analyses : Array CandidateDecl) (rootDirectDeps : Array Name) :
    Array CandidateDecl :=
  Id.run do
    let ranked :=
      (analyses.filter fun cand =>
        cand.score > 0 && (cand.kind != .consequence || !cand.compRefs.isEmpty)).qsort fun a b =>
        if a.score = b.score then a.depth < b.depth else a.score > b.score
    let top := ranked.extract 0 (min ranked.size 3)
    let direct := analyses.filter fun cand =>
      rootDirectDeps.contains cand.declName && (cand.kind != .consequence || !cand.compRefs.isEmpty)
    let mut selected : Array CandidateDecl := #[]
    for cand in direct ++ top do
      if !selected.any (fun prev => prev.declName == cand.declName) then
        selected := selected.push cand
    selected

/--
Phase 2 hook: when tactic instrumentation lands, merge its structured proof events into the
candidate pool here before graph assembly and path selection.
-/
private def applyDeferredTacticSignals (candidates : Array CandidateDecl) : Array CandidateDecl :=
  candidates

/--
Phase 1B hook: proof-local hints are defined in `Hints.lean`, but raw root-only inference remains
the active behavior until the refinement pass is intentionally enabled.
-/
private def applyDormantHintRefinement (diagram : GameDiagram) : MetaM GameDiagram := do
  pure diagram

private def inferDiagramCore (rootModule root : Name) : MetaM GameDiagram := do
  let rootDirectDeps ← directLocalTheoremDependencies rootModule root
  let (recursiveDeps, depMap) ← collectRecursiveTheorems rootModule root
  let mut analyses := #[]
  for (declName, depth) in recursiveDeps do
    analyses := analyses.push (← analyzeCandidate rootModule declName depth depMap)
  let selected := applyDeferredTacticSignals <| chooseSelectedCandidates analyses rootDirectDeps
  let (_, state) ← (do
      let rootId ← ensureRootNode root
      let selected := selected.qsort fun a b =>
        if a.depth = b.depth then a.score > b.score else a.depth < b.depth
      for cand in selected do
        applyCandidate cand
      for dep in rootDirectDeps do
        if let some nodeId ← getPrimaryNode? dep then
          let anchor? ← liftM <| anchorRefForDecl root (preferResult := true)
          addEdge nodeId rootId .consequence "consequence" anchor?
      pure rootId).run {}
  let mainPath := buildMainPath state.rootNode state.edges
  let diagram : GameDiagram := {
    title := moduleTitle rootModule
    subtitle := .moduleDoc
    layout := .sequenceWithSideEdges
    mainPath := mainPath.toArray
    nodes := state.nodes
    edges := state.edges
  }
  applyDormantHintRefinement diagram

def inferDiagramForRoot (root : Name) : MetaM GameDiagram := do
  let rootModule ← match (← Lean.findModuleOf? root) with
    | some rootModule => pure rootModule
    | none => pure (← getEnv).mainModule
  inferDiagramCore rootModule root

def inferDiagramForModule? (modName : Name) : MetaM (Except DiagramInferenceError (Option GameDiagram)) := do
  let roots ← getRegisteredGameHopRoots modName
  if roots.isEmpty then
    return .ok none
  if roots.size > 1 then
    return .error <| .multipleRoots roots
  let root := roots[0]!
  try
    let diagram ← inferDiagramCore modName root
    return .ok (some diagram)
  catch e =>
    let msg ← liftM <| e.toMessageData.toString
    return .error <| .inferenceFailed root msg

end GameHop
end VCVioWidgets
