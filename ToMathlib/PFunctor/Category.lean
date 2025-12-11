/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ToMathlib.PFunctor.Lens.Basic
import ToMathlib.PFunctor.Chart.Basic
import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Categories of Polynomial Functors

We define the various categories of polynomial functors, where morphisms are lenses or charts.
-/

universe u v uA uB

open CategoryTheory

namespace PFunctor

-- Category instance using Lens as morphisms
instance lensCategory : Category PFunctor.{uA, uB} where
  Hom P Q := Lens P Q
  id P := Lens.id P
  comp f g := Lens.comp g f -- Note the order: g ∘ f for f ≫ g
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

-- Category instance using Chart as morphisms
instance chartCategory : Category PFunctor.{uA, uB} where
  Hom P Q := Chart P Q
  id P := Chart.id P
  comp f g := Chart.comp g f -- Note the order: g ∘ f for f ≫ g
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end PFunctor
