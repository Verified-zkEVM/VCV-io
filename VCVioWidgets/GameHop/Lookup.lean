module

public meta import VCVioWidgets.GameHop.Hints
public meta import VCVioWidgets.GameHop.Registry
public meta import VCVioWidgets.GameHop.Infer

public meta section

namespace VCVioWidgets
namespace GameHop

/-- Compatibility wrapper while the panel transitions to inferred diagrams. -/
abbrev diagramForModule? := inferDiagramForModule?

end GameHop
end VCVioWidgets
