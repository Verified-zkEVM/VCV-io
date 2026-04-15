/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public meta import Lean
public meta import Lean.Server.Requests
public meta import ProofWidgets.Component.Basic
public meta import ProofWidgets.Component.GraphDisplay
public meta import ProofWidgets.Component.OfRpcMethod
public meta import ProofWidgets.Component.Panel.Basic
public meta import ProofWidgets.Data.Html

public meta section

namespace VCVioWidgets
namespace OpenSyntax

open Lean Meta Server ProofWidgets
open scoped ProofWidgets.Jsx

/-!
# Composition diagram widget for OpenSyntax.Raw expressions

This panel widget renders `Raw` expression trees as interactive force-directed
graphs in the Lean 4 infoview, powered by ProofWidgets' `GraphDisplay` (D3).

Nodes are draggable, edges have SVG arrows, and clicking any element shows
contextual details. Mark a definition with `@[show_composition]` and activate
the panel with
`show_panel_widgets [local VCVioWidgets.OpenSyntax.CompositionPanel]`
to see the composition diagram.
-/

-- ============================================================================
-- § Intermediate tree representation
-- ============================================================================

inductive CompTree where
  | atom (label : String)
  | mapNode (child : CompTree)
  | par (left right : CompTree)
  | wire (left right : CompTree)
  | plug (system context : CompTree)
  | opaque (label : String)
  deriving Inhabited

-- ============================================================================
-- § Meta-level expression extraction
-- ============================================================================

private def rawPrefix : Name := `Interaction.UC.OpenSyntax.Raw

partial def extractCompTree (e : Expr) : MetaM CompTree := do
  match e with
  | .mdata _ inner => extractCompTree inner
  | _ =>
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .const n _ =>
      if n == rawPrefix ++ `plug && args.size >= 4 then
        let system ← extractCompTree args[2]!
        let context ← extractCompTree args[3]!
        return .plug system context
      else
        let e ← whnf e
        extractCompTreeCore e
  | _ =>
      let e ← whnf e
      extractCompTreeCore e
where
  extractCompTreeCore (e : Expr) : MetaM CompTree := do
    match e with
    | .mdata _ inner => extractCompTree inner
    | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const n _ =>
        if n == rawPrefix ++ `atom && args.size >= 3 then
          let atomExpr := args[2]!
          let label ← do
            let atomExpr ← whnf atomExpr
            let atomFn := atomExpr.getAppFn
            match atomFn with
            | .const cn _ =>
                match cn with
                | .str _ s => pure s
                | _ => pure (cn.toString false)
            | _ => return .atom (← ppExpr atomExpr).pretty
          return .atom label
        else if n == rawPrefix ++ `map && args.size >= 5 then
          let child ← extractCompTree args[4]!
          return .mapNode child
        else if n == rawPrefix ++ `par && args.size >= 5 then
          let left ← extractCompTree args[3]!
          let right ← extractCompTree args[4]!
          return .par left right
        else if n == rawPrefix ++ `wire && args.size >= 6 then
          let left ← extractCompTree args[4]!
          let right ← extractCompTree args[5]!
          return .wire left right
        else if n == rawPrefix ++ `idWire && args.size >= 2 then
          return .opaque "idWire"
        else
          let fmt ← ppExpr e
          return .opaque fmt.pretty
    | _ =>
        let fmt ← ppExpr e
        return .opaque fmt.pretty

-- ============================================================================
-- § Graph rendering (D3 force-directed via GraphDisplay)
-- ============================================================================

private structure GraphState where
  vertices : Array GraphDisplay.Vertex
  edges : Array GraphDisplay.Edge
  nextId : Nat

private def mkAtomLabel (label : String) : Html :=
  <g>
    <rect x="-52" y="-16" width="104" height="32" rx="6" ry="6"
      fill="#f0f4f8" stroke="#4c78a8" strokeWidth="1.5" />
    <text textAnchor="middle" dominantBaseline="central"
      fill="#333" fontSize="11" fontWeight="600"
      fontFamily="Helvetica, sans-serif">{.text label}</text>
  </g>

private def mkOpaqueLabel (label : String) : Html :=
  <g>
    <rect x="-52" y="-16" width="104" height="32" rx="6" ry="6"
      fill="none" stroke="#888" strokeWidth="1" strokeDasharray="4,2" />
    <text textAnchor="middle" dominantBaseline="central"
      fill="#888" fontSize="10"
      fontFamily="Helvetica, sans-serif">{.text label}</text>
  </g>

private def mkConnectiveLabel (label : String) (color : String) : Html :=
  <g>
    <circle r="5" fill={color} stroke="none" opacity="0.7" />
    <text textAnchor="middle" y="14"
      fill={color} fontSize="8" opacity="0.6"
      fontFamily="Helvetica, sans-serif">{.text label}</text>
  </g>

private def mkEdgeLabel (label : String) (color : String) : Html :=
  <g>
    <circle r="9" fill="white" fillOpacity="0.9" stroke="none" />
    <text textAnchor="middle" dominantBaseline="central"
      fill={color} fontSize="10" fontWeight="700">{.text label}</text>
  </g>

private partial def buildGraph (tree : CompTree) (st : GraphState) : String × GraphState :=
  let myId := s!"v{st.nextId}"
  let st := { st with nextId := st.nextId + 1 }
  match tree with
  | .atom label =>
      let vertex : GraphDisplay.Vertex := {
        id := myId
        label := mkAtomLabel label
        boundingShape := .rect 104 32
        details? := some (.text s!"Atom: {label}")
      }
      (myId, { st with vertices := st.vertices.push vertex })
  | .opaque label =>
      let vertex : GraphDisplay.Vertex := {
        id := myId
        label := mkOpaqueLabel label
        boundingShape := .rect 104 32
        details? := some (.text s!"Opaque term: {label}")
      }
      (myId, { st with vertices := st.vertices.push vertex })
  | .par left right =>
      let (leftId, st) := buildGraph left st
      let (rightId, st) := buildGraph right st
      let vertex : GraphDisplay.Vertex := {
        id := myId
        label := mkConnectiveLabel "par" "#4c78a8"
        boundingShape := .circle 5
        details? := some (.text "Parallel composition (par): places two systems side by side.")
      }
      let edgeL : GraphDisplay.Edge := {
        source := myId, target := leftId
        attrs := #[("stroke", Json.str "#4c78a8"),
                   ("strokeDasharray", Json.str "5,3"),
                   ("strokeWidth", Json.num 1.5)]
      }
      let edgeR : GraphDisplay.Edge := {
        source := myId, target := rightId
        attrs := #[("stroke", Json.str "#4c78a8"),
                   ("strokeDasharray", Json.str "5,3"),
                   ("strokeWidth", Json.num 1.5)]
      }
      (myId, { st with
        vertices := st.vertices.push vertex
        edges := st.edges ++ #[edgeL, edgeR] })
  | .wire left right =>
      let (leftId, st) := buildGraph left st
      let (rightId, st) := buildGraph right st
      let vertex : GraphDisplay.Vertex := {
        id := myId
        label := mkConnectiveLabel "wire" "#e45756"
        boundingShape := .circle 5
        details? := some
          (.text "Wiring (wire): connects two systems through a shared boundary Γ.")
      }
      let edgeL : GraphDisplay.Edge := {
        source := myId, target := leftId
        attrs := #[("stroke", Json.str "#e45756"), ("strokeWidth", Json.num 2)]
        label? := some (mkEdgeLabel "Γ" "#e45756")
      }
      let edgeR : GraphDisplay.Edge := {
        source := myId, target := rightId
        attrs := #[("stroke", Json.str "#e45756"), ("strokeWidth", Json.num 2)]
        label? := some (mkEdgeLabel "Γ" "#e45756")
      }
      (myId, { st with
        vertices := st.vertices.push vertex
        edges := st.edges ++ #[edgeL, edgeR] })
  | .plug system context =>
      let (sysId, st) := buildGraph system st
      let (ctxId, st) := buildGraph context st
      let vertex : GraphDisplay.Vertex := {
        id := myId
        label := mkConnectiveLabel "plug" "#54a24b"
        boundingShape := .circle 5
        details? := some
          (.text "Plugging (plug): fully closes the system against its context.")
      }
      let edgeSys : GraphDisplay.Edge := {
        source := myId, target := sysId
        attrs := #[("stroke", Json.str "#54a24b"), ("strokeWidth", Json.num 2.5),
                   ("markerStart", Json.str "url(#arrow)")]
        label? := some (mkEdgeLabel "Δ" "#54a24b")
      }
      let edgeCtx : GraphDisplay.Edge := {
        source := myId, target := ctxId
        attrs := #[("stroke", Json.str "#54a24b"), ("strokeWidth", Json.num 2.5),
                   ("markerStart", Json.str "url(#arrow)")]
        label? := some (mkEdgeLabel "Δ" "#54a24b")
      }
      (myId, { st with
        vertices := st.vertices.push vertex
        edges := st.edges ++ #[edgeSys, edgeCtx] })
  | .mapNode child =>
      let (childId, st) := buildGraph child st
      let vertex : GraphDisplay.Vertex := {
        id := myId
        label := mkConnectiveLabel "map" "#888"
        boundingShape := .circle 5
        details? := some
          (.text "Boundary adaptation (map): transforms the boundary of the inner system.")
      }
      let edge : GraphDisplay.Edge := {
        source := myId, target := childId
        attrs := #[("stroke", Json.str "#888"),
                   ("strokeDasharray", Json.str "3,3"),
                   ("strokeWidth", Json.num 1.5)]
      }
      (myId, { st with
        vertices := st.vertices.push vertex
        edges := st.edges.push edge })

private def compTreeToGraph (tree : CompTree) : GraphDisplay.Props :=
  let (_, st) := buildGraph tree { vertices := #[], edges := #[], nextId := 0 }
  {
    vertices := st.vertices
    edges := st.edges
    defaultEdgeAttrs := #[
      ("stroke", Json.str "var(--vscode-editor-foreground)"),
      ("strokeWidth", Json.num 1.5),
      ("markerEnd", Json.str "url(#arrow)")
    ]
    forces := #[
      .link { distance? := some 100.0, strength? := some 2.0, iterations? := some 10 },
      .manyBody { strength? := some (-200.0) },
      .collide { radius? := some 35.0, strength? := some 1.0 },
      .x { strength? := some 0.05 },
      .y { strength? := some 0.3 }
    ]
    showDetails := true
  }

-- ============================================================================
-- § Attribute registry
-- ============================================================================

structure RegisteredComp where
  modName : Name
  declName : Name
  deriving Inhabited, Repr

initialize compositionExt :
    SimpleScopedEnvExtension RegisteredComp (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m entry =>
      let prev := match m.find? entry.modName with
        | some prev => prev
        | none => #[]
      m.insert entry.modName (prev.push entry.declName)
    initial := {}
  }

private def getDeclModule (declName : Name) : MetaM Name := do
  match (← Lean.findModuleOf? declName) with
  | some modName => return modName
  | none => return (← getEnv).mainModule

initialize registerBuiltinAttribute {
  name := `show_composition
  descr := "Register a definition for composition diagram visualization."
  add := fun decl _stx kind => MetaM.run' do
    let modName ← getDeclModule decl
    compositionExt.add { modName, declName := decl } kind
}

def getRegisteredCompositions (modName : Name) : CoreM (Array Name) := do
  return match (compositionExt.getState (← getEnv)).find? modName with
    | some names => names
    | none => #[]

-- ============================================================================
-- § Panel widget
-- ============================================================================

private def css (entries : List (String × String)) : Json :=
  Json.mkObj <| entries.map fun (k, v) => (k, Json.str v)

namespace CompositionPanel

private def emptyHtml (modName : Name) : Html :=
  <details «open»={true}>
    <summary className="mv2 pointer">Composition Diagram</summary>
    <div style={css [
      ("display", "flex"),
      ("flexDirection", "column"),
      ("gap", "8px"),
      ("padding", "4px 0 0 0")
    ]}>
      <div>{.text "No @[show_composition] definitions found in this file."}</div>
      <div style={css [
        ("fontSize", "12px"),
        ("opacity", "0.8")
      ]}>
        {.text s!"Current module: {modName}"}
      </div>
    </div>
  </details>

private def errorHtml (modName : Name) (message : String) : Html :=
  <details «open»={true}>
    <summary className="mv2 pointer">Composition Diagram</summary>
    <div style={css [
      ("display", "flex"),
      ("flexDirection", "column"),
      ("gap", "8px"),
      ("padding", "4px 0 0 0")
    ]}>
      <div style={css [("color", "#e45756")]}>{.text message}</div>
      <div style={css [
        ("fontSize", "12px"),
        ("opacity", "0.8")
      ]}>
        {.text s!"Current module: {modName}"}
      </div>
    </div>
  </details>

private def renderOneDef (declName : Name) : MetaM Html := do
  let some info := (← getEnv).find? declName
    | return <div>{.text s!"Definition `{declName}` not found."}</div>
  let value ← match info with
    | .defnInfo defn => pure defn.value
    | .thmInfo thm => pure thm.value
    | _ => return <div>{.text s!"`{declName}` is not a definition."}</div>
  let tree ← extractCompTree value
  let gProps := compTreeToGraph tree
  return <div style={css [
    ("display", "flex"),
    ("flexDirection", "column"),
    ("gap", "8px"),
    ("padding", "8px 0")
  ]}>
    <div style={css [
      ("fontSize", "13px"),
      ("fontWeight", "700"),
      ("fontFamily", "var(--vscode-editor-font-family)")
    ]}>{.text (toString declName)}</div>
    <GraphDisplay
      vertices={gProps.vertices}
      edges={gProps.edges}
      defaultEdgeAttrs={gProps.defaultEdgeAttrs}
      forces={gProps.forces}
      showDetails={gProps.showDetails}
    />
  </div>

private def renderAll (snap : Snapshots.Snapshot) (modName : Name) : RequestM Html := do
  let names ← RequestM.runTermElabM snap do
    liftM <| getRegisteredCompositions modName
  if names.isEmpty then
    return emptyHtml modName
  let items ← names.mapM fun declName => do
    RequestM.runTermElabM snap do renderOneDef declName
  return <details «open»={true}>
    <summary className="mv2 pointer">Force-Directed Graph</summary>
    <div className="ml1" style={css [
      ("display", "flex"),
      ("flexDirection", "column"),
      ("gap", "16px"),
      ("padding", "4px 0")
    ]}>
      {...items}
    </div>
  </details>

private partial def latestReadySnap?
    (snaps : IO.AsyncList IO.Error Snapshots.Snapshot)
    (last? : Option Snapshots.Snapshot := none) : BaseIO (Option Snapshots.Snapshot) := do
  match snaps with
  | .nil => pure last?
  | .cons snap rest => latestReadySnap? rest (some snap)
  | .delayed task =>
      if ← IO.hasFinished task.task then
        match task.task.get with
        | .ok rest => latestReadySnap? rest last?
        | .error _ => pure last?
      else
        pure last?

@[server_rpc_method]
def rpc (_props : PanelWidgetProps) : RequestM (RequestTask Html) := do
  let doc ← RequestM.readDoc
  let finalPos := doc.meta.text.source.rawEndPos
  RequestM.bindWaitFindSnap doc
    (fun snap => snap.endPos >= finalPos)
    (notFoundX := do
      let latestSnap? ← liftM <| latestReadySnap? doc.cmdSnaps
      match latestSnap? with
      | some snap =>
          let html ← renderAll snap doc.meta.mod
          return ServerTask.mk <| Task.pure <| Except.ok html
      | none =>
          return ServerTask.mk <| Task.pure <| Except.ok <|
            emptyHtml doc.meta.mod)
    (x := fun snap => do
      let html ← renderAll snap doc.meta.mod
      return ServerTask.mk <| Task.pure <| Except.ok html)

end CompositionPanel

@[widget_module]
def CompositionPanel : Component PanelWidgetProps :=
  mk_rpc_widget% CompositionPanel.rpc

end OpenSyntax
end VCVioWidgets
