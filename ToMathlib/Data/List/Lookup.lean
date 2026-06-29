/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Data.List.Basic

/-!
# Looking up an entry of a self-indexed association list

`List.map_lookup` evaluates `List.lookup` on an association list of the form
`L.map (fun i => (i, f i))`: for any key `t` present in `L`, the lookup returns `some (f t)`. This
is the shape produced when one tabulates a function `f` over a list of keys.
-/

namespace List

variable {ι Sym : Type*} [BEq ι] [LawfulBEq ι]

/-- Looking up a present key among `(i, f i)` entries returns its value. -/
theorem map_lookup (f : ι → Sym) (t : ι) :
    ∀ L : List ι, t ∈ L → (L.map (fun i => (i, f i))).lookup t = some (f t)
  | a :: L, h => by
    simp only [List.map_cons, List.lookup_cons]
    rcases eq_or_ne a t with rfl | hat
    · simp
    · rw [show (t == a) = false from by simpa using hat.symm]
      exact map_lookup f t L ((List.mem_cons.1 h).resolve_left (fun h' => hat h'.symm))

end List
