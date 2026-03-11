module

public import Lean
public import VCVioWidgets.GameHop.Examples.ElGamal
public import VCVioWidgets.GameHop.Examples.OneTimePad

public section

namespace VCVioWidgets
namespace GameHop

open Lean

/--
Maps modules to the game-hop diagram that should be shown while browsing them.

For the first persistent cutover we keep lookup file-scoped instead of trying to
recover declaration-local context from the infotree. This is enough to keep the
diagram visible while moving around the relevant proof files.
-/
structure DiagramBinding where
  modules : Array Name
  diagram : GameDiagram
  deriving Inhabited, Repr

namespace DiagramBinding

def matchesModule (binding : DiagramBinding) (modName : Name) : Bool :=
  binding.modules.contains modName

end DiagramBinding

private def bindings : Array DiagramBinding := #[
  { modules := #[
      `Examples.OneTimePad,
      `VCVio.CryptoFoundations.SymmEncAlg,
      `VCVioWidgets.GameHop.Examples.OneTimePad
    ]
    diagram := Examples.OneTimePad.cipherGivenMsgEquivDiagram }
  , { modules := #[
        `Examples.ElGamal,
        `VCVioWidgets.GameHop.Examples.ElGamal
      ]
      diagram := Examples.ElGamal.hybridSequenceDiagram }
]

def diagramForModule? (modName : Name) : Option GameDiagram :=
  (bindings.find? fun binding => binding.matchesModule modName).map (·.diagram)

end GameHop
end VCVioWidgets
