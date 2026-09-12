module

public meta import Lean

public meta section

namespace VCVioWidgets
namespace GameHop

open Lean Elab Meta

/-- Root theorem registrations used by the game-hop widget inference pipeline. -/
structure RegisteredRoot where
  /-- Module containing the registered root theorem. -/
  modName : Name
  /-- Name of the theorem used as a diagram root. -/
  declName : Name
  deriving Inhabited, Repr

/-- Scoped index of registered game-hopping root theorems by module. -/
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
    unless ← isProp info.type do
      throwError m!"@[game_hop_root] only supports propositions, got `{decl}` of type:{indentExpr info.type}"
    let modName ← getDeclModule decl
    gameHopRootExt.add { modName, declName := decl } kind
}

/-- Return all root theorems registered for a module. -/
def getRegisteredGameHopRoots (modName : Name) : CoreM (Array Name) := do
  return match (gameHopRootExt.getState (← getEnv)).find? modName with
    | some roots => roots
    | none => #[]

end GameHop
end VCVioWidgets
