/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public meta import Lean
public meta import Lean.Server.Requests
public meta import ProofWidgets.Component.Basic
public meta import ProofWidgets.Component.OfRpcMethod
public meta import ProofWidgets.Component.Panel.Basic
public meta import ProofWidgets.Data.Html
public meta import VCVioWidgets.OpenSyntax.Panel

public meta section

namespace VCVioWidgets
namespace OpenSyntax

open Lean Meta Server ProofWidgets
open scoped ProofWidgets.Jsx

/-!
# Variant B: Computed tree layout for composition diagrams

Renders `CompTree` as a static SVG with positions computed by a simple
top-down tree layout algorithm. No physics simulation; the diagram is
stable and hierarchical.
-/

-- ============================================================================
-- § Tree layout computation
-- ============================================================================

private structure LayoutNode where
  id : Nat
  x : Float
  y : Float
  label : String
  kind : String
  color : String

private structure LayoutEdge where
  srcId : Nat
  tgtId : Nat
  label : String
  color : String
  dashed : Bool

private structure LayoutState where
  nodes : Array LayoutNode
  edges : Array LayoutEdge
  nextId : Nat
  nextLeafX : Float

private def nodeW : Float := 120
private def nodeH : Float := 32
private def opR : Float := 5
private def opH : Float := 10
private def levelH : Float := 80
private def leafGap : Float := 140

private partial def layoutTree (tree : CompTree) (depth : Float) (st : LayoutState)
    : Nat × Float × LayoutState :=
  let myId := st.nextId
  let st := { st with nextId := st.nextId + 1 }
  match tree with
  | .atom label =>
      let x := st.nextLeafX
      let node : LayoutNode := {
        id := myId, x, y := depth, label, kind := "atom", color := "#4c78a8" }
      (myId, x, { st with
        nodes := st.nodes.push node
        nextLeafX := st.nextLeafX + leafGap })
  | .opaque label =>
      let x := st.nextLeafX
      let node : LayoutNode := {
        id := myId, x, y := depth, label, kind := "opaque", color := "#888" }
      (myId, x, { st with
        nodes := st.nodes.push node
        nextLeafX := st.nextLeafX + leafGap })
  | .par left right =>
      let (leftId, leftX, st) := layoutTree left (depth + levelH) st
      let (rightId, rightX, st) := layoutTree right (depth + levelH) st
      let x := (leftX + rightX) / 2
      let node : LayoutNode := {
        id := myId, x, y := depth, label := "par", kind := "op", color := "#4c78a8" }
      let edgeL : LayoutEdge := {
        srcId := myId, tgtId := leftId, label := "", color := "#4c78a8", dashed := true }
      let edgeR : LayoutEdge := {
        srcId := myId, tgtId := rightId, label := "", color := "#4c78a8", dashed := true }
      (myId, x, { st with
        nodes := st.nodes.push node
        edges := st.edges ++ #[edgeL, edgeR] })
  | .wire left right =>
      let (leftId, leftX, st) := layoutTree left (depth + levelH) st
      let (rightId, rightX, st) := layoutTree right (depth + levelH) st
      let x := (leftX + rightX) / 2
      let node : LayoutNode := {
        id := myId, x, y := depth, label := "wire", kind := "op", color := "#e45756" }
      let edgeL : LayoutEdge := {
        srcId := myId, tgtId := leftId, label := "Γ", color := "#e45756", dashed := false }
      let edgeR : LayoutEdge := {
        srcId := myId, tgtId := rightId, label := "Γ", color := "#e45756", dashed := false }
      (myId, x, { st with
        nodes := st.nodes.push node
        edges := st.edges ++ #[edgeL, edgeR] })
  | .plug system context =>
      let (sysId, sysX, st) := layoutTree system (depth + levelH) st
      let (ctxId, ctxX, st) := layoutTree context (depth + levelH) st
      let x := (sysX + ctxX) / 2
      let node : LayoutNode := {
        id := myId, x, y := depth, label := "plug", kind := "op", color := "#54a24b" }
      let edgeSys : LayoutEdge := {
        srcId := myId, tgtId := sysId, label := "Δ", color := "#54a24b", dashed := false }
      let edgeCtx : LayoutEdge := {
        srcId := myId, tgtId := ctxId, label := "Δ", color := "#54a24b", dashed := false }
      (myId, x, { st with
        nodes := st.nodes.push node
        edges := st.edges ++ #[edgeSys, edgeCtx] })
  | .mapNode child =>
      let (childId, childX, st) := layoutTree child (depth + levelH) st
      let node : LayoutNode := {
        id := myId, x := childX, y := depth, label := "map", kind := "op", color := "#888" }
      let edge : LayoutEdge := {
        srcId := myId, tgtId := childId, label := "", color := "#888", dashed := true }
      (myId, childX, { st with
        nodes := st.nodes.push node
        edges := st.edges.push edge })

-- ============================================================================
-- § SVG rendering via Html.element
-- ============================================================================

private def findNode (nodes : Array LayoutNode) (id : Nat) : Option LayoutNode :=
  nodes.find? (·.id == id)

private abbrev svgEl (tag : String) (attrs : Array (String × Json))
    (children : Array Html := #[]) : Html :=
  .element tag attrs children

private def renderEdgeElem (nodes : Array LayoutNode) (e : LayoutEdge) : Html :=
  match findNode nodes e.srcId, findNode nodes e.tgtId with
  | some src, some tgt =>
      let x1 := src.x
      let y1 := (if src.kind == "op" then src.y + opH / 2 else src.y + nodeH / 2)
      let x2 := tgt.x
      let y2 := (if tgt.kind == "op" then tgt.y - opH / 2 else tgt.y - nodeH / 2)
      let dashAttr := (if e.dashed then "5,3" else "none")
      let mx := (x1 + x2) / 2
      let my := (y1 + y2) / 2
      let line := svgEl "line" #[
        ("x1", Json.str (toString x1)), ("y1", Json.str (toString y1)),
        ("x2", Json.str (toString x2)), ("y2", Json.str (toString y2)),
        ("stroke", Json.str e.color), ("strokeWidth", Json.str "2"),
        ("strokeDasharray", Json.str dashAttr),
        ("markerEnd", Json.str "url(#arrowhead)")]
      let labelElems : Array Html := (if e.label.isEmpty then #[] else #[
        svgEl "circle" #[
          ("cx", Json.str (toString mx)), ("cy", Json.str (toString my)),
          ("r", Json.str "10"), ("fill", Json.str "white"),
          ("fillOpacity", Json.str "0.9"), ("stroke", Json.str "none")],
        svgEl "text" #[
          ("x", Json.str (toString mx)), ("y", Json.str (toString my)),
          ("textAnchor", Json.str "middle"), ("dominantBaseline", Json.str "central"),
          ("fill", Json.str e.color), ("fontSize", Json.str "10"),
          ("fontWeight", Json.str "700")]
          #[.text e.label]])
      svgEl "g" #[] (#[line] ++ labelElems)
  | _, _ => svgEl "g" #[]

private def renderNodeElem (n : LayoutNode) : Html :=
  match n.kind with
  | "op" =>
    svgEl "g" #[] #[
      svgEl "circle" #[
        ("cx", Json.str (toString n.x)), ("cy", Json.str (toString n.y)),
        ("r", Json.str (toString opR)),
        ("fill", Json.str n.color), ("opacity", Json.str "0.7")],
      svgEl "text" #[
        ("x", Json.str (toString n.x)),
        ("y", Json.str (toString (n.y + 16))),
        ("textAnchor", Json.str "middle"),
        ("fill", Json.str n.color), ("fontSize", Json.str "8"),
        ("opacity", Json.str "0.6")]
        #[.text n.label]]
  | "atom" =>
    let rx := n.x - nodeW / 2
    let ry := n.y - nodeH / 2
    svgEl "g" #[] #[
      svgEl "rect" #[
        ("x", Json.str (toString rx)), ("y", Json.str (toString ry)),
        ("width", Json.str (toString nodeW)), ("height", Json.str (toString nodeH)),
        ("rx", Json.str "6"), ("ry", Json.str "6"),
        ("fill", Json.str "#f0f4f8"), ("stroke", Json.str "#4c78a8"),
        ("strokeWidth", Json.str "1.5")],
      svgEl "text" #[
        ("x", Json.str (toString n.x)), ("y", Json.str (toString n.y)),
        ("textAnchor", Json.str "middle"), ("dominantBaseline", Json.str "central"),
        ("fill", Json.str "#333"), ("fontSize", Json.str "11"),
        ("fontWeight", Json.str "600")]
        #[.text n.label]]
  | _ =>
    let rx := n.x - nodeW / 2
    let ry := n.y - nodeH / 2
    svgEl "g" #[] #[
      svgEl "rect" #[
        ("x", Json.str (toString rx)), ("y", Json.str (toString ry)),
        ("width", Json.str (toString nodeW)), ("height", Json.str (toString nodeH)),
        ("rx", Json.str "6"), ("ry", Json.str "6"),
        ("fill", Json.str "none"), ("stroke", Json.str "#888"),
        ("strokeWidth", Json.str "1"), ("strokeDasharray", Json.str "4,2")],
      svgEl "text" #[
        ("x", Json.str (toString n.x)), ("y", Json.str (toString n.y)),
        ("textAnchor", Json.str "middle"), ("dominantBaseline", Json.str "central"),
        ("fill", Json.str "#888"), ("fontSize", Json.str "10")]
        #[.text n.label]]

private def renderTreeSvg (tree : CompTree) : Html :=
  let (_, _, st) := layoutTree tree 30 {
    nodes := #[], edges := #[], nextId := 0, nextLeafX := 80 }
  let maxX := (st.nodes.foldl (fun acc n => max acc n.x) 0)
  let maxY := (st.nodes.foldl (fun acc n => max acc n.y) 0)
  let svgW := toString (maxX + 100)
  let svgH := toString (maxY + 60)
  let edgeElems := (st.edges.map (renderEdgeElem st.nodes))
  let nodeElems := (st.nodes.map renderNodeElem)
  let arrowMarker := svgEl "marker" #[
    ("id", Json.str "arrowhead"),
    ("viewBox", Json.str "0 0 10 10"),
    ("refX", Json.str "8"), ("refY", Json.str "5"),
    ("markerWidth", Json.str "4"), ("markerHeight", Json.str "4"),
    ("orient", Json.str "auto-start-reverse")]
    #[svgEl "path" #[
      ("d", Json.str "M 0 0 L 10 5 L 0 10 z"),
      ("fill", Json.str "context-stroke")]]
  let defs := svgEl "defs" #[] #[arrowMarker]
  svgEl "svg" #[
    ("xmlns", Json.str "http://www.w3.org/2000/svg"),
    ("width", Json.str svgW),
    ("height", Json.str svgH)]
    (#[defs] ++ edgeElems ++ nodeElems)

-- ============================================================================
-- § Panel widget
-- ============================================================================

private def css (entries : List (String × String)) : Json :=
  Json.mkObj <| entries.map fun (k, v) => (k, Json.str v)

namespace TreePanelWidget

private def emptyHtml : Html :=
  <details «open»={true}>
    <summary className="mv2 pointer">Tree Layout</summary>
    <div>{.text "No @[show_composition] definitions found."}</div>
  </details>

private def renderOneDef (declName : Name) : MetaM Html := do
  let some info := (← getEnv).find? declName
    | return <div>{.text s!"Definition `{declName}` not found."}</div>
  let value ← match info with
    | .defnInfo defn => pure defn.value
    | .thmInfo thm => pure thm.value
    | _ => return <div>{.text s!"`{declName}` is not a definition."}</div>
  let tree ← extractCompTree value
  let rendered := renderTreeSvg tree
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
    <div style={css [("overflowX", "auto")]}>{rendered}</div>
  </div>

private def renderAll (snap : Snapshots.Snapshot) (modName : Name) : RequestM Html := do
  let names ← RequestM.runTermElabM snap do
    liftM <| getRegisteredCompositions modName
  if names.isEmpty then return emptyHtml
  let items ← names.mapM fun declName => do
    RequestM.runTermElabM snap do renderOneDef declName
  return <details «open»={true}>
    <summary className="mv2 pointer">Tree Layout</summary>
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
          return ServerTask.mk <| Task.pure <| Except.ok emptyHtml)
    (x := fun snap => do
      let html ← renderAll snap doc.meta.mod
      return ServerTask.mk <| Task.pure <| Except.ok html)

end TreePanelWidget

@[widget_module]
def TreePanel : Component PanelWidgetProps :=
  mk_rpc_widget% TreePanelWidget.rpc

end OpenSyntax
end VCVioWidgets
