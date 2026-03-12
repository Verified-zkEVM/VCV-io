module

public meta import Lean.Server.Requests
public meta import ProofWidgets.Component.OfRpcMethod
public meta import ProofWidgets.Component.Panel.Basic
public meta import VCVioWidgets.GameHop.Lookup
public import VCVioWidgets.GameHop.Render

public meta section

namespace VCVioWidgets
namespace GameHop

open Lean Server ProofWidgets
open scoped ProofWidgets.Jsx

namespace GameHopPanel

private def emptyHtml (modName : Name) : Html :=
  <details «open»={true}>
    <summary className="mv2 pointer">Game Hop</summary>
    <div style={Json.mkObj [
      ("display", Json.str "flex"),
      ("flexDirection", Json.str "column"),
      ("gap", Json.str "8px"),
      ("padding", Json.str "4px 0 0 0")
    ]}>
      <div>{.text "No game-hop diagram is registered for the current file."}</div>
      <div style={Json.mkObj [
        ("fontSize", Json.str "12px"),
        ("opacity", Json.num 0.8)
      ]}>
        {.text s!"Current module: {modName}"}
      </div>
    </div>
  </details>

private def loadingHtml (modName : Name) : Html :=
  <details «open»={true}>
    <summary className="mv2 pointer">Game Hop</summary>
    <div style={Json.mkObj [
      ("display", Json.str "flex"),
      ("flexDirection", Json.str "column"),
      ("gap", Json.str "8px"),
      ("padding", Json.str "4px 0 0 0")
    ]}>
      <div>{.text "Game-hop diagram is still elaborating for the current file."}</div>
      <div style={Json.mkObj [
        ("fontSize", Json.str "12px"),
        ("opacity", Json.num 0.8)
      ]}>
        {.text s!"Current module: {modName}"}
      </div>
    </div>
  </details>

@[server_rpc_method_cancellable]
def rpc (props : PanelWidgetProps) : RequestM (RequestTask Html) := do
  let doc ← RequestM.readDoc
  RequestM.withWaitFindSnapAtPos props.pos fun snap => do
    let some diagramDecl := diagramForModule? snap.env doc.meta.mod
      | return emptyHtml doc.meta.mod
    if !snap.env.contains diagramDecl then
      return loadingHtml doc.meta.mod
    let rendered ← RequestM.runTermElabM snap do
      let diagram ← unsafe evalConstCheck GameDiagram ``GameDiagram diagramDecl
      GameDiagram.renderHtml doc.meta.mod diagram
    return <details «open»={true}>
      <summary className="mv2 pointer">Game Hop</summary>
      <div className="ml1">{rendered}</div>
    </details>

end GameHopPanel

@[widget_module]
def GameHopPanel : Component PanelWidgetProps :=
  mk_rpc_widget% GameHopPanel.rpc

end GameHop
end VCVioWidgets
