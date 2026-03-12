module

public import Lean
public import VCVioWidgets.GameHop.Model

public section

namespace VCVioWidgets
namespace GameHop

open Lean

/--
Maps modules to the source-local GameHop diagram declaration that should be shown while browsing them.

The diagram declarations themselves live in the proof files; this table only points to
those declarations by name so the panel can evaluate them from the fully elaborated file
snapshot.
-/
structure DiagramBinding where
  modules : Array Name
  diagramDecl : Name
  deriving Inhabited, Repr

namespace DiagramBinding

def matchesModule (binding : DiagramBinding) (modName : Name) : Bool :=
  binding.modules.contains modName

end DiagramBinding

private def bindings : Array DiagramBinding := #[
  { modules := #[`Examples.OneTimePad]
    diagramDecl := `oneTimePadGameHopDiagram }
  , { modules := #[`Examples.ElGamal]
      diagramDecl := `elGamalGameHopDiagram }
]

def diagramForModule? (_env : Environment) (modName : Name) : Option Name :=
  (bindings.find? (·.matchesModule modName)).map (·.diagramDecl)

end GameHop
end VCVioWidgets
