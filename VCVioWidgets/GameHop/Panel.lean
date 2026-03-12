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
      <div>{.text "Game-hop diagram is initializing for the current file."}</div>
      <div style={Json.mkObj [
        ("fontSize", Json.str "12px"),
        ("opacity", Json.num 0.8)
      ]}>
        {.text s!"Current module: {modName}"}
      </div>
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

private def wrapPanel (rendered : Html) : Html :=
  <details «open»={true}>
    <summary className="mv2 pointer">Game Hop</summary>
    <div className="ml1">{rendered}</div>
  </details>

private def renderDiagram (snap : Snapshots.Snapshot) (modName : Name) (diagram : GameDiagram) :
    RequestM Html := do
  let rendered ← RequestM.runTermElabM snap do
    GameDiagram.renderHtml modName diagram
  return wrapPanel rendered

@[server_rpc_method_cancellable]
def rpc (_props : PanelWidgetProps) : RequestM (RequestTask Html) := do
  let doc ← RequestM.readDoc
  let some diagram := diagramForModule? doc.meta.mod
    | return ServerTask.mk <| Task.pure <| Except.ok <| emptyHtml doc.meta.mod

  let latestSnap? ← liftM <| latestReadySnap? doc.cmdSnaps
  match latestSnap? with
  | some snap =>
      let html ← renderDiagram snap doc.meta.mod diagram
      return ServerTask.mk <| Task.pure <| Except.ok html
  | none =>
      RequestM.bindWaitFindSnap doc
        (fun _ => true)
        (notFoundX := return ServerTask.mk <| Task.pure <| Except.ok <| loadingHtml doc.meta.mod)
        (x := fun snap => do
          let html ← renderDiagram snap doc.meta.mod diagram
          return ServerTask.mk <| Task.pure <| Except.ok html)

end GameHopPanel

@[widget_module]
def GameHopPanel : Component PanelWidgetProps :=
  mk_rpc_widget% GameHopPanel.rpc

end GameHop
end VCVioWidgets
