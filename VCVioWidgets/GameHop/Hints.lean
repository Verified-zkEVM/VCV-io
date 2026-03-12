module

public meta import Lean
public meta import VCVioWidgets.GameHop.Model

public meta section

namespace VCVioWidgets
namespace GameHop

open Lean Elab Meta

/-- Dormant proof-local hint vocabulary for refining raw game-hop inference. -/
structure GameHopHint where
  hide : Bool := false
  focus : Bool := false
  title? : Option String := none
  kind? : Option NodeKind := none
  deriving Inhabited

structure GameHopHintUpdate where
  declName : Name
  hide? : Option Bool := none
  focus? : Option Bool := none
  title? : Option String := none
  kind? : Option NodeKind := none
  deriving Inhabited

private def GameHopHint.applyUpdate (hint : GameHopHint) (update : GameHopHintUpdate) : GameHopHint :=
  { hide := update.hide?.getD hint.hide
    focus := update.focus?.getD hint.focus
    title? := update.title? <|> hint.title?
    kind? := update.kind? <|> hint.kind? }

initialize gameHopHintExt :
    SimpleScopedEnvExtension GameHopHintUpdate (NameMap GameHopHint) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m entry =>
      let prev := match m.find? entry.declName with
        | some prev => prev
        | none => {}
      m.insert entry.declName (prev.applyUpdate entry)
    initial := {}
  }

syntax (name := gameHopHideAttr) "game_hop_hide" : attr
syntax (name := gameHopFocusAttr) "game_hop_focus" : attr
syntax (name := gameHopTitleAttr) "game_hop_title" str : attr
syntax (name := gameHopKindAttr) "game_hop_kind" ("game" <|> "hybrid" <|> "endpoint" <|> "result") : attr

private def addHintUpdate (update : GameHopHintUpdate) (kind : AttributeKind) :
    AttrM Unit := do
  gameHopHintExt.add update kind

initialize
  registerBuiltinAttribute {
    name := `game_hop_hide
    descr := "Hide this declaration from the inferred game-hop diagram."
    add := fun decl stx kind => match stx with
      | `(attr| game_hop_hide) =>
          addHintUpdate { declName := decl, hide? := some true } kind
      | _ => throwUnsupportedSyntax
  }
  registerBuiltinAttribute {
    name := `game_hop_focus
    descr := "Prefer this declaration when selecting the main inferred game-hop path."
    add := fun decl stx kind => match stx with
      | `(attr| game_hop_focus) =>
          addHintUpdate { declName := decl, focus? := some true } kind
      | _ => throwUnsupportedSyntax
  }
  registerBuiltinAttribute {
    name := `game_hop_title
    descr := "Override the inferred title for this declaration in a game-hop diagram."
    add := fun decl stx kind => match stx with
      | `(attr| game_hop_title $title:str) =>
          addHintUpdate { declName := decl, title? := some title.getString } kind
      | _ => throwUnsupportedSyntax
  }
  registerBuiltinAttribute {
    name := `game_hop_kind
    descr := "Override the inferred node kind for this declaration in a game-hop diagram."
    add := fun decl stx kind => do
      let nodeKind ← match stx with
        | `(attr| game_hop_kind game) => pure .game
        | `(attr| game_hop_kind hybrid) => pure .hybrid
        | `(attr| game_hop_kind endpoint) => pure .endpoint
        | `(attr| game_hop_kind result) => pure .result
        | _ => throwUnsupportedSyntax
      addHintUpdate { declName := decl, kind? := some nodeKind } kind
  }

/-- Return the currently registered dormant hint bundle for a declaration, if any. -/
def getGameHopHint? (declName : Name) : CoreM (Option GameHopHint) := do
  return (gameHopHintExt.getState (← getEnv)).find? declName

end GameHop
end VCVioWidgets
