import Lean.Meta.Sym.Pattern

namespace Lean.Meta.Sym

/-- Lean 4.28 compatibility helper for the keyed pattern constructor added later upstream. -/
public def mkPatternFromDeclWithKey {α : Type}
    (declName : Name) (select : Expr → MetaM (Expr × α)) :
    MetaM (Pattern × α) := do
  let pattern ← mkPatternFromDecl declName
  let (key, extra) ← select pattern.pattern
  return ({ pattern with pattern := key }, extra)

end Lean.Meta.Sym
