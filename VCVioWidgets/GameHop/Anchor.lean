module

public meta import Lean.DeclarationRange
public meta import Lean.Data.Lsp.Utf16
public meta import Lean.Server.Utils
public import VCVioWidgets.GameHop.Model

public meta section

namespace VCVioWidgets
namespace GameHop

open Lean

structure ResolvedAnchor where
  declName : Name
  kind : AnchorKind
  uri : Lsp.DocumentUri
  declarationRange : Lsp.Range
  selectionRange : Lsp.Range

namespace AnchorKind

def chipLabel : AnchorKind → String
  | .defn => "def"
  | .theorem => "thm"
  | .reduction => "red"
  | .result => "result"

end AnchorKind

namespace AnchorRef

def targetRange (anchor : AnchorRef) (resolved : ResolvedAnchor) : Lsp.Range :=
  match anchor.mode with
  | AnchorMode.declaration => resolved.declarationRange
  | AnchorMode.selection => resolved.selectionRange

def resolve? (anchor : AnchorRef) : MetaM (Option ResolvedAnchor) := do
  if !(← getEnv).contains anchor.declName then
    return none
  let some ranges ← Lean.findDeclarationRanges? anchor.declName
    | return none
  let some modName ← Lean.findModuleOf? anchor.declName
    | return none
  let some uri ← Lean.Server.documentUriFromModule? modName
    | return none
  return some {
    declName := anchor.declName
    kind := anchor.kind
    uri
    declarationRange := ranges.range.toLspRange
    selectionRange := ranges.selectionRange.toLspRange
  }

end AnchorRef

end GameHop
end VCVioWidgets
