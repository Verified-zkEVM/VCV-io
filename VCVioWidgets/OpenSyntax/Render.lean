/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.UC.OpenSyntax.Raw

/-!
# Graphviz DOT rendering for Raw expressions

This module provides `Raw.toDot`, which converts a raw open-system expression
tree into a Graphviz DOT string suitable for visualization.

Each native constructor of `Raw` maps to a distinct visual element:

* `atom` becomes a rounded box node labeled by a user-supplied rendering
  function.
* `par` becomes a dashed cluster containing both sub-expressions.
* `wire` becomes a solid cluster with a bold edge connecting the shared
  boundary between its two children.
* `idWire` becomes a small relay-style node.
* `map` becomes a dotted cluster wrapping the adapted inner expression.

Since `plug` and `unit` are derived abbreviations (expanding to `map`/`wire`
combinations), they are rendered through their constituent parts.

Boundaries (`PortBoundary`) are rendered structurally: the visualization shows
the composition topology rather than individual port details, since port types
are abstract at this level.

## Usage

```
#eval IO.println (Raw.toDot (fun a => toString a) myExpr)
```

The output can be piped to `dot -Tsvg` or pasted into any Graphviz renderer.
-/

universe u

namespace Interaction
namespace UC
namespace OpenSyntax
namespace Raw

private def escapeLabel (s : String) : String :=
  s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n"

private structure DotResult where
  nodeRef : String
  nextId : Nat
  lines : Array String

private def mkPad (depth : Nat) : String :=
  "".pushn ' ' (2 * depth)

private def ob : String := "{"
private def cb : String := "}"

/--
Recursive DOT rendering of a `Raw` expression. Returns the DOT node ID of the
expression's representative node (for use by parent expressions when drawing
edges), the next available counter, and the accumulated DOT statements.
-/
private def toDotAux
    {Atom : PortBoundary → Type u}
    (renderAtom : ∀ {Δ : PortBoundary}, Atom Δ → String)
    {Δ : PortBoundary}
    (e : Raw Atom Δ)
    (nextId : Nat)
    (depth : Nat) : DotResult :=
  let pad := mkPad depth
  let ipad := mkPad (depth + 1)
  match e with
  | .atom a =>
      let id := nextId
      let label := escapeLabel (renderAtom a)
      { nodeRef := s!"n{id}",
        nextId := id + 1,
        lines := #[s!"{pad}n{id} [shape=box, style=\"rounded,filled\", " ++
          s!"fillcolor=\"#f0f4f8\", color=\"#4c78a8\", label=\"{label}\"];"] }
  | .map _f inner =>
      let cid := nextId
      let r := toDotAux renderAtom inner (cid + 1) (depth + 1)
      { nodeRef := r.nodeRef,
        nextId := r.nextId,
        lines := #[s!"{pad}subgraph cluster_{cid} {ob}",
                    s!"{ipad}label=\"map\";",
                    s!"{ipad}style=dotted;",
                    s!"{ipad}color=\"#888888\";"]
                 ++ r.lines
                 ++ #[s!"{pad}{cb}"] }
  | .par e₁ e₂ =>
      let cid := nextId
      let r₁ := toDotAux renderAtom e₁ (cid + 1) (depth + 1)
      let r₂ := toDotAux renderAtom e₂ r₁.nextId (depth + 1)
      { nodeRef := r₁.nodeRef,
        nextId := r₂.nextId,
        lines := #[s!"{pad}subgraph cluster_{cid} {ob}",
                    s!"{ipad}label=\"∥ par\";",
                    s!"{ipad}style=dashed;",
                    s!"{ipad}color=\"#4c78a8\";"]
                 ++ r₁.lines ++ r₂.lines
                 ++ #[s!"{pad}{cb}"] }
  | .wire e₁ e₂ =>
      let cid := nextId
      let r₁ := toDotAux renderAtom e₁ (cid + 1) (depth + 1)
      let r₂ := toDotAux renderAtom e₂ r₁.nextId (depth + 1)
      { nodeRef := r₁.nodeRef,
        nextId := r₂.nextId,
        lines := #[s!"{pad}subgraph cluster_{cid} {ob}",
                    s!"{ipad}label=\"wire\";",
                    s!"{ipad}style=solid;",
                    s!"{ipad}color=\"#e45756\";"]
                 ++ r₁.lines ++ r₂.lines
                 ++ #[s!"{pad}{cb}",
                      s!"{pad}{r₁.nodeRef} -> {r₂.nodeRef} " ++
                        s!"[color=\"#e45756\", style=bold, penwidth=2, " ++
                        s!"label=\"Γ\"];"] }
  | .idWire _Γ =>
      let id := nextId
      { nodeRef := s!"n{id}",
        nextId := id + 1,
        lines := #[s!"{pad}n{id} [shape=diamond, style=\"filled\", " ++
          s!"fillcolor=\"#e8f0fe\", color=\"#888888\", " ++
          s!"label=\"idWire\", fontsize=9];"] }

/--
Convert a `Raw` expression tree to a Graphviz DOT string.

`renderAtom` controls how primitive atoms are labeled. Pass a `ToString`-based
function, or any custom labeling logic.

The output is a complete `digraph` that can be rendered with
`dot -Tsvg -o out.svg` or pasted into an online Graphviz viewer.
-/
def toDot
    {Atom : PortBoundary → Type u}
    (renderAtom : ∀ {Δ : PortBoundary}, Atom Δ → String)
    {Δ : PortBoundary}
    (e : Raw Atom Δ) : String :=
  let r := toDotAux renderAtom e 0 1
  let header := #[
    s!"digraph RawExpr {ob}",
    "  rankdir=TB;",
    "  fontname=\"Helvetica,sans-serif\";",
    "  node [fontname=\"Helvetica,sans-serif\", fontsize=11];",
    "  edge [fontname=\"Helvetica,sans-serif\", fontsize=9];",
    ""]
  let footer := #[s!"{cb}", ""]
  "\n".intercalate (header ++ r.lines ++ footer).toList

end Raw
end OpenSyntax
end UC
end Interaction
