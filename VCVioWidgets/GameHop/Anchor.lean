module

public meta import Lean.DeclarationRange
public meta import Lean.Data.Lsp.Utf16
public meta import Lean.Server.Utils
public import VCVioWidgets.GameHop.Model

public meta section

namespace VCVioWidgets
namespace GameHop

open Lean

/-- A declaration reference resolved to a source URI and navigation ranges. -/
structure ResolvedAnchor where
  /-- Fully qualified name of the resolved declaration. -/
  declName : Name
  /-- Diagram role of the resolved declaration. -/
  kind : AnchorKind
  /-- URI of the source document containing the declaration. -/
  uri : Lsp.DocumentUri
  /-- Source range containing the complete declaration. -/
  declarationRange : Lsp.Range
  /-- Source range containing the declaration's selected name. -/
  selectionRange : Lsp.Range

namespace AnchorKind

/-- Abbreviated role label displayed beside a declaration reference. -/
def chipLabel : AnchorKind → String
  | .defn => "def"
  | .theorem => "thm"
  | .reduction => "red"
  | .result => "result"

end AnchorKind

namespace AnchorRef

/-- Select the resolved source range requested by the reference's navigation mode. -/
def targetRange (anchor : AnchorRef) (resolved : ResolvedAnchor) : Lsp.Range :=
  match anchor.mode with
  | AnchorMode.declaration => resolved.declarationRange
  | AnchorMode.selection => resolved.selectionRange

/-- Resolve a declaration reference to its source location, if available. -/
def resolve? (anchor : AnchorRef) (currentUri? : Option Lsp.DocumentUri := none) :
    MetaM (Option ResolvedAnchor) := do
  if !(← getEnv).contains anchor.declName then
    return none
  let currentModule := (← getEnv).mainModule
  let some ranges ← Lean.findDeclarationRanges? anchor.declName
    | return none
  let uri? ←
    match ← Lean.findModuleOf? anchor.declName with
    | some modName =>
        match ← Lean.Server.documentUriFromModule? modName with
        | some uri => pure (some uri)
        | none =>
            if modName == currentModule then pure currentUri? else pure none
    | none => pure currentUri?
  let some uri := uri?
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
