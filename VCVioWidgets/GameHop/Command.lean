module

public meta import Lean.Elab.Command
public meta import ProofWidgets.Component.HtmlDisplay
public import VCVioWidgets.GameHop.Render

public meta section

namespace VCVioWidgets
namespace GameHop

open Lean Server Elab Command

class GameDiagramEval (α : Type) where
  eval : α → CommandElabM GameDiagram

instance : GameDiagramEval GameDiagram where
  eval diagram := pure diagram

instance {m : Type → Type} [MonadLiftT m CommandElabM] : GameDiagramEval (m GameDiagram) where
  eval := monadLift

namespace Command

unsafe def evalCommandMDiagramUnsafe (stx : Term) : TermElabM (CommandElabM GameDiagram) := do
  let tp := mkApp (mkConst ``CommandElabM) (mkConst ``GameDiagram)
  Term.evalTerm _ tp stx

@[implemented_by evalCommandMDiagramUnsafe]
opaque evalCommandMDiagram : Term → TermElabM (CommandElabM GameDiagram)

syntax (name := gameHopCmd) "game_hop_widget " term : command

@[command_elab gameHopCmd]
def elabGameHopCmd : CommandElab := fun
  | stx@`(game_hop_widget $t:term) => do
      let diagX ← liftTermElabM <| evalCommandMDiagram <| ← ``(GameDiagramEval.eval $t)
      let diagram ← diagX
      let html ← liftTermElabM <| GameDiagram.renderHtml diagram
      liftCoreM <| Widget.savePanelWidgetInfo
        (hash ProofWidgets.HtmlDisplayPanel.javascript)
        (return json% { html: $(← rpcEncode html) })
        stx
  | stx => throwError "Unexpected syntax {stx}."

end Command

end GameHop
end VCVioWidgets
