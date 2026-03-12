module

public meta import Lean

public meta section

namespace VCVioWidgets
namespace GameHop

open Lean Elab Meta

/-- Root theorem registrations used by the game-hop widget inference pipeline. -/
structure RegisteredRoot where
  modName : Name
  declName : Name
  deriving Inhabited, Repr

initialize gameHopRootExt :
    SimpleScopedEnvExtension RegisteredRoot (NameMap (Array Name)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun m entry =>
      let prev := match m.find? entry.modName with
        | some prev => prev
        | none => #[]
      m.insert entry.modName (prev.push entry.declName)
    initial := {}
  }

private def getDeclModule (declName : Name) : MetaM Name := do
  match (← Lean.findModuleOf? declName) with
  | some modName => return modName
  | none => return (← getEnv).mainModule

initialize registerBuiltinAttribute {
  name := `game_hop_root
  descr := "Register a theorem as the root of an inferred game-hop diagram."
  add := fun decl _ kind => MetaM.run' do
    let info ← getConstInfo decl
    match info with
    | .thmInfo _ =>
        let modName ← getDeclModule decl
        gameHopRootExt.add { modName, declName := decl } kind
    | _ =>
        throwError m!"@[game_hop_root] only supports theorems/lemmas, got `{decl}` of type:{indentExpr info.type}"
}

/-- Return all root theorems registered for a module. -/
def getRegisteredGameHopRoots (modName : Name) : CoreM (Array Name) := do
  return match (gameHopRootExt.getState (← getEnv)).find? modName with
    | some roots => roots
    | none => #[]

end GameHop
end VCVioWidgets
