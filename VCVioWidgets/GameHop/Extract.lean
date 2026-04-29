module

public meta import Lean.DocString
public meta import Lean.Data.Lsp.Utf16
public meta import Lean.Server.Utils
public meta import Lean.Widget.InteractiveCode
public meta import VCVioWidgets.GameHop.Anchor
public meta import VCVioWidgets.GameHop.Model

public meta section

namespace VCVioWidgets
namespace GameHop

open Lean

private def hasDecl (declName : Name) : MetaM Bool := do
  return (← getEnv).contains declName

private def pendingDeclText (declName : Name) : String :=
  s!"Waiting for `{declName}` to elaborate."

private def declBasename : Name → String
  | .anonymous => ""
  | .str _ s => s
  | .num p _ => declBasename p

private def stripLeadingDocComment (source : String) : String :=
  if source.startsWith "/--" || source.startsWith "/-!" then
    match source.find? "-/" with
    | some closePos =>
        let afterComment := closePos.offset.next source |>.next source
        let trimmedStart := String.Pos.Raw.nextWhile source Char.isWhitespace afterComment
        String.Pos.Raw.extract source trimmedStart source.rawEndPos
    | none => source
  else
    source

private def declSearchPatterns (declName : Name) : List String :=
  let base := declBasename declName
  [
    s!"def {base}",
    s!"abbrev {base}",
    s!"lemma {base}",
    s!"theorem {base}",
    s!"opaque {base}",
    s!"instance {base}",
    s!"structure {base}",
    s!"class {base}"
  ]

structure RevealTarget where
  uri : Lsp.DocumentUri
  range : Lsp.Range
  title? : Option String := none

inductive ResolvedText where
  | text (contents : String) (target? : Option RevealTarget := none)
  | markdown (contents : String) (target? : Option RevealTarget := none)

inductive ResolvedSnippet where
  | interactiveCode (fmt : Widget.CodeWithInfos) (target? : Option RevealTarget := none)
  | code (contents : String) (target? : Option RevealTarget := none)
  | text (contents : String) (target? : Option RevealTarget := none)
  | markdown (contents : String) (target? : Option RevealTarget := none)

namespace RevealTarget

def ofAnchor (anchor : AnchorRef) (resolved : ResolvedAnchor) : RevealTarget :=
  { uri := resolved.uri, range := anchor.targetRange resolved, title? := some anchor.declName.toString }

end RevealTarget

private def unresolvedDeclTarget? (currentModule : Name) (declName : Name) :
    MetaM (Option RevealTarget) := do
  let some uri ← Lean.Server.documentUriFromModule? currentModule
    | return none
  let some path := System.Uri.fileUriToPath? uri
    | return none
  let contents ← IO.FS.readFile path
  let patterns := declSearchPatterns declName
  let patternCpLengths := patterns.map fun pattern =>
    String.Pos.Raw.offsetOfPos pattern pattern.endPos.offset
  let rec searchLines (lineNo : Nat) (lines : List String) : Option RevealTarget :=
    match lines with
    | [] => none
    | line :: rest =>
        let rec searchPatterns (remainingPatterns : List String) (remainingLengths : List Nat) :
            Option RevealTarget :=
          match remainingPatterns, remainingLengths with
          | pattern :: patterns, cpLen :: lengths =>
              match line.find? pattern with
              | some startPos =>
                  let startCp := String.Pos.Raw.offsetOfPos line startPos.offset
                  let startChar := String.codepointPosToUtf16Pos line startCp
                  let endChar := String.codepointPosToUtf16Pos line (startCp + cpLen)
                  some {
                    uri
                    range := {
                      start := ⟨lineNo, startChar⟩
                      «end» := ⟨lineNo, endChar⟩
                    }
                    title? := some declName.toString
                  }
              | none =>
                  searchPatterns patterns lengths
          | _, _ => none
        match searchPatterns patterns patternCpLengths with
        | some target => some target
        | none => searchLines (lineNo + 1) rest
  return searchLines 0 (contents.splitOn "\n")

def declTarget? (currentModule : Name) (declName : Name) : MetaM (Option RevealTarget) := do
  let anchor := AnchorRef.withSelection <| AnchorRef.result declName
  match (← anchor.resolve? (← Lean.Server.documentUriFromModule? currentModule)) with
  | some resolved => return some <| RevealTarget.ofAnchor anchor resolved
  | none => unresolvedDeclTarget? currentModule declName

private def moduleDocTarget? (modName : Name) : MetaM (Option RevealTarget) := do
  let some docs := Lean.getModuleDoc? (← getEnv) modName
    | return none
  let some doc := docs[0]?
    | return none
  let some uri ← Lean.Server.documentUriFromModule? modName
    | return none
  return some {
    uri
    range := ModuleDoc.declarationRange doc |>.toLspRange
    title? := some modName.toString
  }

private def readSourceRange (uri : Lsp.DocumentUri) (range : Lsp.Range) : IO (Option String) := do
  let some path := System.Uri.fileUriToPath? uri
    | return none
  let contents ← IO.FS.readFile path
  let text := contents.toFileMap
  let utf8Range := text.lspRangeToUtf8Range range
  return some <| String.Pos.Raw.extract text.source utf8Range.start utf8Range.stop

private def declSource? (currentModule : Name) (declName : Name) :
    MetaM (Option (String × RevealTarget)) := do
  let anchor := AnchorRef.result declName
  let some resolved ← anchor.resolve? (← Lean.Server.documentUriFromModule? currentModule)
    | return none
  let some contents ← readSourceRange resolved.uri resolved.declarationRange
    | return none
  return some (stripLeadingDocComment contents, RevealTarget.ofAnchor anchor resolved)

private def moduleDoc? (modName : Name) : MetaM (Option (String × RevealTarget)) := do
  let some docs := Lean.getModuleDoc? (← getEnv) modName
    | return none
  let some doc := docs[0]?
    | return none
  let some target ← moduleDocTarget? modName
    | return none
  return some (ModuleDoc.doc doc, target)

private def prettySignature (declName : Name) : MetaM String := do
  withOptions
      (fun opts =>
        opts.set `format.width (68 : Nat)
          |>.set `pp.universes false
          |>.set `pp.fullNames false) do
    let fmt ← PrettyPrinter.ppSignature declName
    return Format.pretty fmt.fmt 68

private def prettyExprCode (expr : Expr) : MetaM Widget.CodeWithInfos := do
  withOptions
      (fun opts =>
        opts.set `format.width (54 : Nat)
          |>.set `pp.universes false
          |>.set `pp.fullNames false) do
    Widget.ppExprTagged expr

def resolveTextSource (currentModule : Name) (anchor? : Option AnchorRef) (source : TextSource) :
    MetaM (Option ResolvedText) := do
  match source with
  | .none => return none
  | .text contents => return some <| .text contents
  | .declDoc declName =>
      if !(← hasDecl declName) then
        return none
      let doc? ← Lean.findDocString? (← getEnv) declName
      match doc? with
      | some contents =>
          return some <| .markdown contents (target? := (← declTarget? currentModule declName))
      | none =>
          return none
  | .moduleDoc modName? =>
      let modName := modName?.getD currentModule
      let doc? ← moduleDoc? modName
      return doc?.map fun (contents, target) =>
        .markdown contents (target? := some target)
  | .anchorDoc =>
      let some anchor := anchor?
        | return none
      if !(← hasDecl anchor.declName) then
        return none
      let doc? ← Lean.findDocString? (← getEnv) anchor.declName
      match doc? with
      | some contents =>
          return some <| .markdown contents (target? := (← declTarget? currentModule anchor.declName))
      | none =>
          return none

def resolveSnippet (currentModule : Name) (snippet : CodeSnippet) :
    MetaM ResolvedSnippet := do
  match snippet with
  | .declName declName =>
      if !(← hasDecl declName) then
        return .text (pendingDeclText declName) (target? := (← declTarget? currentModule declName))
      let fmt ← prettyExprCode (← mkConstWithLevelParams declName)
      return .interactiveCode fmt (target? := (← declTarget? currentModule declName))
  | .declType declName =>
      if !(← hasDecl declName) then
        return .text (pendingDeclText declName) (target? := (← declTarget? currentModule declName))
      let expr ← mkConstWithLevelParams declName
      let fmt ← prettyExprCode (← Meta.inferType expr)
      return .interactiveCode fmt (target? := (← declTarget? currentModule declName))
  | .declSignature declName =>
      if !(← hasDecl declName) then
        return .text (pendingDeclText declName) (target? := (← declTarget? currentModule declName))
      return .code (← prettySignature declName) (target? := (← declTarget? currentModule declName))
  | .declDoc declName =>
      if !(← hasDecl declName) then
        return .text (pendingDeclText declName) (target? := (← declTarget? currentModule declName))
      let doc? ← Lean.findDocString? (← getEnv) declName
      match doc? with
      | some contents =>
          return .markdown contents (target? := (← declTarget? currentModule declName))
      | none =>
          return .code (← prettySignature declName) (target? := (← declTarget? currentModule declName))
  | .declSource declName =>
      if !(← hasDecl declName) then
        return .text (pendingDeclText declName) (target? := (← declTarget? currentModule declName))
      match (← declSource? currentModule declName) with
      | some (contents, target) =>
          return .code contents (target? := some target)
      | none =>
          return .code (← prettySignature declName) (target? := (← declTarget? currentModule declName))
  | .moduleDoc modName? =>
      let modName := modName?.getD currentModule
      match (← moduleDoc? modName) with
      | some (contents, target) =>
          return .markdown contents (target? := some target)
      | none =>
          return .text modName.toString
  | .text contents anchor? =>
      let target? ←
        match anchor? with
        | none => pure none
        | some anchor =>
            pure <| (← anchor.resolve? (← Lean.Server.documentUriFromModule? currentModule)).map <|
              RevealTarget.ofAnchor anchor
      return .text contents (target? := target?)

end GameHop
end VCVioWidgets
