module

public meta import ProofWidgets.Component.Basic
public meta import ProofWidgets.Data.Html
public meta import VCVioWidgets.GameHop.Model
public import VCVioWidgets.Component.RevealLocation
public import VCVioWidgets.GameHop.Anchor

public meta section

namespace VCVioWidgets
namespace GameHop

open Lean Meta ProofWidgets
open scoped ProofWidgets.Jsx

private def css (entries : List (String × String)) : Json :=
  Json.mkObj <| entries.map fun (k, v) => (k, Json.str v)

private def nodeAccent : NodeKind → String
  | .game => "#4c78a8"
  | .hybrid => "#f58518"
  | .endpoint => "#54a24b"
  | .result => "#b279a2"

private def edgeAccent : EdgeKind → String
  | .step => "#6c757d"
  | .equivalence => "#4c78a8"
  | .equality => "#54a24b"
  | .bound => "#e45756"
  | .consequence => "#b279a2"

private def wrapReveal (resolved? : Option (AnchorRef × ResolvedAnchor))
    (title? : Option String) (child : Html) (block : Bool := false) : Html :=
  match resolved? with
  | some (anchor, resolved) =>
      Html.ofComponent VCVioWidgets.RevealLocation
        { uri := resolved.uri, range := anchor.targetRange resolved, title?, block } #[child]
  | none => child

private def declAnchor (declName : Name) : AnchorRef :=
  AnchorRef.withSelection <| AnchorRef.result declName

private def ppExprCard (expr : Expr) : MetaM Widget.CodeWithInfos :=
  withOptions
      (fun opts =>
        opts.set `format.width (54 : Nat)
          |>.set `pp.universes false
          |>.set `pp.fullNames false) do
    Widget.ppExprTagged expr

private def resolveAnchor? (anchor? : Option AnchorRef) :
    MetaM (Option (AnchorRef × ResolvedAnchor)) := do
  match anchor? with
  | none => pure none
  | some anchor =>
      return (← anchor.resolve?).map fun resolved => (anchor, resolved)

private def renderAnchorChip (anchor? : Option AnchorRef) :
    MetaM (Option Html) := do
  let some anchor := anchor?
    | return none
  let resolved? ← resolveAnchor? anchor?
  let base : Html :=
    <span style={css [
      ("border", "1px solid var(--vscode-editor-foreground)"),
      ("borderRadius", "999px"),
      ("padding", "2px 8px"),
      ("fontSize", "11px"),
      ("fontWeight", "600"),
      ("textTransform", "uppercase")
    ]}>
      {.text anchor.kind.chipLabel}
    </span>
  return some <| wrapReveal resolved? (some anchor.declName.toString) base

private def renderSnippet (snippet : CodeSnippet) : MetaM Html := do
  match snippet with
  | .declName declName =>
      let resolved? ← resolveAnchor? (some <| declAnchor declName)
      try
        let fmt ← ppExprCard (← mkConstWithLevelParams declName)
        pure <| wrapReveal resolved? (some declName.toString)
          <div style={css [
          ("fontFamily", "var(--vscode-editor-font-family)"),
          ("fontSize", "12px"),
          ("lineHeight", "1.45"),
          ("whiteSpace", "normal"),
          ("overflowX", "auto")
        ]}>
            <InteractiveCode fmt={fmt} />
          </div>
          (block := true)
      catch _ =>
        pure <| wrapReveal resolved? (some declName.toString)
          <div style={css [
          ("fontFamily", "var(--vscode-editor-font-family)"),
          ("fontSize", "12px"),
          ("lineHeight", "1.45"),
          ("whiteSpace", "pre-wrap")
        ]}>{.text declName.toString}</div>
          (block := true)
  | .declType declName =>
      let resolved? ← resolveAnchor? (some <| declAnchor declName)
      try
        let expr ← mkConstWithLevelParams declName
        let fmt ← ppExprCard (← Meta.inferType expr)
        pure <| wrapReveal resolved? (some declName.toString)
          <div style={css [
          ("fontFamily", "var(--vscode-editor-font-family)"),
          ("fontSize", "12px"),
          ("lineHeight", "1.45"),
          ("whiteSpace", "normal"),
          ("overflowX", "auto")
        ]}>
            <InteractiveCode fmt={fmt} />
          </div>
          (block := true)
      catch _ =>
        pure <| wrapReveal resolved? (some declName.toString)
          <div style={css [
          ("fontFamily", "var(--vscode-editor-font-family)"),
          ("fontSize", "12px"),
          ("lineHeight", "1.45"),
          ("whiteSpace", "pre-wrap")
        ]}>{.text declName.toString}</div>
          (block := true)
  | .text contents anchor? =>
      let resolved? ← resolveAnchor? anchor?
      let body : Html :=
        <div style={css [
          ("fontFamily", "var(--vscode-editor-font-family)"),
          ("fontSize", "12px"),
          ("lineHeight", "1.45"),
          ("whiteSpace", "pre-wrap")
        ]}>{.text contents}</div>
      pure <| wrapReveal resolved? (anchor?.map fun a => a.declName.toString) body
        (block := true)

private def renderNode (node : GameNode) : MetaM Html := do
  let resolved? ← resolveAnchor? node.anchor?
  let chip? ← renderAnchorChip node.anchor?
  let snippets ← node.snippets.mapM renderSnippet
  let titleHtml : Html :=
    wrapReveal resolved? (node.anchor?.map fun a => a.declName.toString)
      <span style={css [
        ("fontSize", "14px"),
        ("fontWeight", "700")
      ]}>{.text node.title}</span>
  let body : Html :=
    <div style={css [
    ("display", "flex"),
    ("flexDirection", "column"),
    ("gap", "10px"),
    ("minWidth", "240px"),
    ("maxWidth", "380px"),
    ("padding", "12px"),
    ("border", s!"1px solid {nodeAccent node.kind}"),
    ("borderLeft", s!"4px solid {nodeAccent node.kind}"),
    ("borderRadius", "8px"),
    ("background", "var(--vscode-editor-background)")
  ]}>
    <div style={css [
      ("display", "flex"),
      ("justifyContent", "space-between"),
      ("alignItems", "flex-start"),
      ("gap", "10px")
    ]}>
      {titleHtml}
      {match chip? with
       | some chip => chip
       | none => Html.text ""}
    </div>
    <div style={css [
      ("fontSize", "12px"),
      ("lineHeight", "1.45"),
      ("whiteSpace", "pre-wrap")
    ]}>{.text node.summary}</div>
    {if snippets.isEmpty then
      Html.text ""
    else
      <div style={css [
        ("display", "flex"),
        ("flexDirection", "column"),
        ("gap", "6px"),
        ("padding", "8px"),
        ("borderRadius", "6px"),
        ("background", "var(--vscode-editorHoverWidget-background)"),
        ("overflowX", "auto")
      ]}>
        {...snippets}
      </div>}
  </div>
  pure <| wrapReveal resolved? (node.anchor?.map fun a => a.declName.toString) body
    (block := true)

private def renderEdgeNote (edge : GameEdge) (note : GameEdgeNote) : MetaM Html := do
  let resolved? ← resolveAnchor? note.anchor?
  let labelHtml : Html :=
    wrapReveal resolved? (note.anchor?.map fun a => a.declName.toString)
      <span style={css [
        ("fontSize", "11px"),
        ("fontWeight", "600")
      ]}>{.text note.label}</span>
  let body : Html :=
    <div style={css [
    ("display", "flex"),
    ("flexDirection", "column"),
    ("gap", "3px"),
    ("padding", "6px 8px"),
    ("borderRadius", "6px"),
    ("border", s!"1px solid {edgeAccent edge.kind}"),
    ("maxWidth", "260px"),
    ("textAlign", "center"),
    ("background", "var(--vscode-editorHoverWidget-background)")
  ]}>
    {labelHtml}
    {match note.detail? with
     | some detail =>
         <div style={css [
           ("fontSize", "11px"),
           ("lineHeight", "1.35"),
           ("whiteSpace", "pre-wrap")
         ]}>{.text detail}</div>
     | none => Html.text ""}
  </div>
  pure <| wrapReveal resolved? (note.anchor?.map fun a => a.declName.toString) body
    (block := true)

private def renderEdge (layout : LayoutHint) (edge? : Option GameEdge) : MetaM Html := do
  let some edge := edge?
    | pure <div style={css [
      ("display", "flex"),
      ("alignItems", "center"),
      ("justifyContent", "center"),
      ("minWidth", "110px"),
      ("fontSize", "28px")
    ]}>{.text "⟶"}</div>
  let resolved? ← resolveAnchor? edge.anchor?
  let chip? ← renderAnchorChip edge.anchor?
  let notes ←
    if layout = .sequenceWithSideEdges then
      edge.notes.mapM (renderEdgeNote edge)
    else
      pure #[]
  let labelHtml : Html :=
    wrapReveal resolved? (edge.anchor?.map fun a => a.declName.toString)
      <span style={css [
        ("fontSize", "12px"),
        ("fontWeight", "700"),
        ("color", edgeAccent edge.kind),
        ("textAlign", "center")
      ]}>{.text edge.label}</span>
  let body : Html :=
    <div style={css [
    ("display", "flex"),
    ("flexDirection", "column"),
    ("alignItems", "center"),
    ("justifyContent", "center"),
    ("gap", "8px"),
    ("minWidth", "190px"),
    ("maxWidth", "260px")
  ]}>
    <div style={css [
      ("fontSize", "28px"),
      ("lineHeight", "1"),
      ("color", edgeAccent edge.kind)
    ]}>{.text "⟶"}</div>
    {labelHtml}
    {match edge.detail? with
     | some detail =>
         <div style={css [
           ("fontSize", "11px"),
           ("lineHeight", "1.35"),
           ("textAlign", "center"),
           ("whiteSpace", "pre-wrap")
         ]}>{.text detail}</div>
     | none => Html.text ""}
    {match chip? with
     | some chip => chip
     | none => Html.text ""}
    {if notes.isEmpty then
      Html.text ""
    else
      <div style={css [
        ("display", "flex"),
        ("flexDirection", "column"),
        ("alignItems", "center"),
        ("gap", "6px")
      ]}>
        {...notes}
      </div>}
  </div>
  pure <| wrapReveal resolved? (edge.anchor?.map fun a => a.declName.toString) body
    (block := true)

private def renderMissingNode (nodeId : NodeId) : Html :=
  <div style={css [
    ("minWidth", "220px"),
    ("padding", "12px"),
    ("border", "1px dashed #e45756"),
    ("borderRadius", "8px"),
    ("color", "#e45756")
  ]}>
    {.text s!"Missing node: {nodeId}"}
  </div>

private def renderPathItems (diagram : GameDiagram) (path : List NodeId) :
    MetaM (Array Html) := do
  match path with
  | [] => pure #[]
  | [nodeId] =>
      let nodeHtml ←
        match diagram.findNode? nodeId with
        | some node => renderNode node
        | none => pure <| renderMissingNode nodeId
      pure #[nodeHtml]
  | nodeId :: nextId :: rest =>
      let nodeHtml ←
        match diagram.findNode? nodeId with
        | some node => renderNode node
        | none => pure <| renderMissingNode nodeId
      let edgeHtml ← renderEdge diagram.layout (diagram.findEdge? nodeId nextId)
      let tail ← renderPathItems diagram (nextId :: rest)
      pure <| #[nodeHtml, edgeHtml] ++ tail

def GameDiagram.renderHtml (diagram : GameDiagram) : MetaM Html := do
  let items ← renderPathItems diagram diagram.mainPath.toList
  pure <div style={css [
    ("display", "flex"),
    ("flexDirection", "column"),
    ("gap", "12px"),
    ("padding", "8px 2px")
  ]}>
    <div style={css [
      ("display", "flex"),
      ("flexDirection", "column"),
      ("gap", "4px")
    ]}>
      <div style={css [
        ("fontSize", "16px"),
        ("fontWeight", "700")
      ]}>{.text diagram.title}</div>
      {match diagram.subtitle? with
       | some subtitle =>
           <div style={css [
             ("fontSize", "12px"),
             ("lineHeight", "1.4"),
             ("whiteSpace", "pre-wrap")
           ]}>{.text subtitle}</div>
       | none => Html.text ""}
    </div>
    <div style={css [
      ("display", "flex"),
      ("alignItems", "stretch"),
      ("gap", "12px"),
      ("overflowX", "auto"),
      ("padding", "4px 0 8px 0")
    ]}>
      {...items}
    </div>
  </div>

end GameHop
end VCVioWidgets
