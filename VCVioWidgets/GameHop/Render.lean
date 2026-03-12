module

public meta import ProofWidgets.Component.Basic
public meta import ProofWidgets.Data.Html
public import VCVioWidgets.Component.RevealLocation
public import VCVioWidgets.GameHop.Extract

public meta section

namespace VCVioWidgets
namespace GameHop

open Lean Meta ProofWidgets
open scoped ProofWidgets.Jsx

private def css (entries : List (String × String)) : Json :=
  Json.mkObj <| entries.map fun (k, v) => (k, Json.str v)

private structure RenderCache where
  anchorTargets : Std.HashMap AnchorRef (Option RevealTarget) := {}
  resolvedTexts : Std.HashMap (Option AnchorRef × TextSource) (Option ResolvedText) := {}
  resolvedSnippets : Std.HashMap CodeSnippet ResolvedSnippet := {}
  deriving Inhabited

private abbrev RenderM := StateT RenderCache MetaM

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

private def wrapReveal (target? : Option RevealTarget) (child : Html) (block : Bool := false) : Html :=
  match target? with
  | some target =>
      Html.ofComponent VCVioWidgets.RevealLocation
        { uri := target.uri, range := target.range, title? := target.title?, block } #[child]
  | none => child

private def anchorTargetCore? (currentModule : Name) (anchor? : Option AnchorRef) :
    MetaM (Option RevealTarget) := do
  match anchor? with
  | none => pure none
  | some anchor =>
      match (← anchor.resolve?) with
      | some resolved => pure <| some <| RevealTarget.ofAnchor anchor resolved
      | none => declTarget? currentModule anchor.declName

private def anchorTarget? (currentModule : Name) (anchor? : Option AnchorRef) :
    RenderM (Option RevealTarget) := do
  match anchor? with
  | none => pure none
  | some anchor =>
      let cache ← get
      match cache.anchorTargets.get? anchor with
      | some target? => pure target?
      | none =>
          let target? ← liftM <| anchorTargetCore? currentModule anchor?
          modify fun cache =>
            { cache with anchorTargets := cache.anchorTargets.insert anchor target? }
          pure target?

private def resolveTextCached (currentModule : Name) (anchor? : Option AnchorRef)
    (source : TextSource) : RenderM (Option ResolvedText) := do
  let key := (anchor?, source)
  let cache ← get
  match cache.resolvedTexts.get? key with
  | some resolved => pure resolved
  | none =>
      let resolved ← liftM <| resolveTextSource currentModule anchor? source
      modify fun cache =>
        { cache with resolvedTexts := cache.resolvedTexts.insert key resolved }
      pure resolved

private def resolveSnippetCached (currentModule : Name) (snippet : CodeSnippet) :
    RenderM ResolvedSnippet := do
  let cache ← get
  match cache.resolvedSnippets.get? snippet with
  | some resolved => pure resolved
  | none =>
      let resolved ← liftM <| resolveSnippet currentModule snippet
      modify fun cache =>
        { cache with resolvedSnippets := cache.resolvedSnippets.insert snippet resolved }
      pure resolved

private def renderResolvedText (resolved : ResolvedText) : Html :=
  match resolved with
  | .text contents target? =>
      wrapReveal target?
        <div style={css [
          ("fontSize", "12px"),
          ("lineHeight", "1.45"),
          ("whiteSpace", "pre-wrap")
        ]}>{.text contents}</div>
        (block := true)
  | .markdown contents target? =>
      wrapReveal target?
        <div style={css [
          ("fontSize", "12px"),
          ("lineHeight", "1.45")
        ]}>
          <MarkdownDisplay contents={contents} />
        </div>
        (block := true)

private def renderResolvedSnippet (snippet : ResolvedSnippet) : Html :=
  match snippet with
  | .interactiveCode fmt target? =>
      wrapReveal target?
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
  | .code contents target? =>
      wrapReveal target?
        <div style={css [
          ("fontFamily", "var(--vscode-editor-font-family)"),
          ("fontSize", "12px"),
          ("lineHeight", "1.45"),
          ("whiteSpace", "pre-wrap"),
          ("overflowX", "auto")
        ]}>{.text contents}</div>
        (block := true)
  | .text contents target? =>
      wrapReveal target?
        <div style={css [
          ("fontSize", "12px"),
          ("lineHeight", "1.45"),
          ("whiteSpace", "pre-wrap")
        ]}>{.text contents}</div>
        (block := true)
  | .markdown contents target? =>
      wrapReveal target?
        <div style={css [
          ("fontSize", "12px"),
          ("lineHeight", "1.45")
        ]}>
          <MarkdownDisplay contents={contents} />
        </div>
        (block := true)

private def renderAnchorChip (anchor? : Option AnchorRef) (target? : Option RevealTarget) :
    Option Html :=
  match anchor? with
  | none => none
  | some anchor =>
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
      some <| wrapReveal target? base

private def renderSnippet (currentModule : Name) (snippet : CodeSnippet) : RenderM Html := do
  renderResolvedSnippet <$> resolveSnippetCached currentModule snippet

private def renderNode (currentModule : Name) (node : GameNode) : RenderM Html := do
  let target? ← anchorTarget? currentModule node.anchor?
  let chip? := renderAnchorChip node.anchor? target?
  let snippets ← node.snippets.mapM (renderSnippet currentModule)
  let summary? ← resolveTextCached currentModule node.anchor? node.summary
  let titleHtml : Html :=
    wrapReveal target?
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
    {match summary? with
     | some summary => renderResolvedText summary
     | none => Html.text ""}
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
  pure <| wrapReveal target? body
    (block := true)

private def renderEdgeNote (currentModule : Name) (edge : GameEdge) (note : GameEdgeNote) :
    RenderM Html := do
  let target? ← anchorTarget? currentModule note.anchor?
  let labelHtml : Html :=
    wrapReveal target?
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
  pure <| wrapReveal target? body
    (block := true)

private def renderEdge (currentModule : Name) (layout : LayoutHint) (edge? : Option GameEdge) :
    RenderM Html := do
  let some edge := edge?
    | pure <div style={css [
      ("display", "flex"),
      ("alignItems", "center"),
      ("justifyContent", "center"),
      ("minWidth", "110px"),
      ("fontSize", "28px")
    ]}>{.text "⟶"}</div>
  let target? ← anchorTarget? currentModule edge.anchor?
  let chip? := renderAnchorChip edge.anchor? target?
  let notes ←
    if layout = .sequenceWithSideEdges then
      edge.notes.mapM (renderEdgeNote currentModule edge)
    else
      pure #[]
  let labelHtml : Html :=
    wrapReveal target?
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
  pure <| wrapReveal target? body
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

private def renderPathItemsFor (currentModule : Name) (diagram : GameDiagram) (path : List NodeId) :
    RenderM (Array Html) := do
  match path with
  | [] => pure #[]
  | [nodeId] =>
      let nodeHtml ←
        match diagram.findNode? nodeId with
        | some node => renderNode currentModule node
        | none => pure <| renderMissingNode nodeId
      pure #[nodeHtml]
  | nodeId :: nextId :: rest =>
      let nodeHtml ←
        match diagram.findNode? nodeId with
        | some node => renderNode currentModule node
        | none => pure <| renderMissingNode nodeId
      let edgeHtml ← renderEdge currentModule diagram.layout (diagram.findEdge? nodeId nextId)
      let tail ← renderPathItemsFor currentModule diagram (nextId :: rest)
      pure <| #[nodeHtml, edgeHtml] ++ tail

private def renderHtmlCached (currentModule : Name) (diagram : GameDiagram) : RenderM Html := do
  let items ← renderPathItemsFor currentModule diagram diagram.mainPath.toList
  let subtitle? ← resolveTextCached currentModule none diagram.subtitle
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
      {match subtitle? with
       | some subtitle => renderResolvedText subtitle
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

def GameDiagram.renderHtml (currentModule : Name) (diagram : GameDiagram) : MetaM Html := do
  let (html, _) ← (renderHtmlCached currentModule diagram).run {}
  pure html

end GameHop
end VCVioWidgets
