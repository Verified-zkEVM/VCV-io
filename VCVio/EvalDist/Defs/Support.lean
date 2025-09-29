/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.EvalDist.Defs.Basic

/-!
# Possible Ouptuts of Computations

This file contains lemmas about `HasEvalSet` and `HasEvalFinset`.
We need to treat these somewhat uniquely due to the lack of global `Monad` instances.

dtumad: should consider when/where we use `Set` vs. `SetM`.
-/

open ENNReal

universe u v w

namespace HasEvalSet

variable {m : Type u → Type v} {α β γ : Type u} [Monad m] [HasEvalSet m]

end HasEvalSet
