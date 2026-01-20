/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import VCVio.OracleComp.Coercions.SubSpec

/-!
# Coercing Computations to Larger Oracle Sets

This file defines `SubSpec` instances for oracle specs constructed with
either `OracleSpec.add` or `OracleSpec.sigma`.

TODO: document the "canonical forms" that work well with this
-/

open OracleQuery Sum

namespace OracleQuery

universe u v w

variable {ι₁} {ι₂} {ι₃} {ι₄}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄} {α β γ : Type u}

section instances

/-- We need `Inhabited` to prevent infinite type-class searching. -/
instance {τ : Type u} [Inhabited τ] {spec : OracleSpec τ} : OracleSpec.emptySpec ⊂ₒ spec where
  monadLift | q => PEmpty.elim q.input

section add_left

/-- Add additional oracles to the right side of the existing ones. -/
instance subSpec_add_left : spec₁ ⊂ₒ (spec₁ + spec₂) where
  monadLift | q => .mk (.inl q.input) q.cont

@[simp] lemma liftM_add_left_def (q : OracleQuery spec₁ α) :
    (liftM q : OracleQuery (spec₁ + spec₂) α) = .mk (.inl q.input) q.cont := rfl

@[simp high] lemma liftM_add_left_query (t : spec₁.Domain) :
    (liftM (query t) : OracleQuery (spec₁ + spec₂) (spec₁.Range t)) = query (Sum.inl t) := rfl

end add_left

section add_right

/-- Add additional oracles to the left side of the exiting ones-/
instance subSpec_add_right : spec₂ ⊂ₒ (spec₁ + spec₂) where
  monadLift | q => .mk (.inr q.input) q.cont

@[simp] lemma liftM_add_right_def (q : OracleQuery spec₂ α) :
    (liftM q : OracleQuery (spec₁ + spec₂) α) = .mk (.inr q.input) q.cont := rfl

@[simp high] lemma liftM_add_right_query (t : spec₂.Domain) :
    (liftM (query t) : OracleQuery (spec₁ + spec₂) (spec₂.Range t)) = query (Sum.inr t) := rfl

end add_right

section left_add_left_add

instance subSpec_left_add_left_add_of_subSpec [h : spec₁ ⊂ₒ spec₃] :
    spec₁ + spec₂ ⊂ₒ spec₃ + spec₂ where
  monadLift
    | .mk (.inl q) f => liftM (OracleQuery.mk q f)
    | .mk (.inr q) f => .mk (.inr q) f

@[simp] lemma liftM_left_add_left_add_def
    [h : spec₁ ⊂ₒ spec₃] (q : OracleQuery (spec₁ + spec₂) α) :
    (liftM q : OracleQuery (spec₃ + spec₂) α) = match q with
      | .mk (.inl q) f => liftM ((liftM (OracleQuery.mk q f) : OracleQuery spec₃ _))
      | .mk (.inr q) f => .mk (.inr q) f := rfl

@[simp high] lemma liftM_left_add_left_add_query
    [h : spec₁ ⊂ₒ spec₃] (t : (spec₁ + spec₂).Domain) :
    (liftM (query t) : OracleQuery (spec₃ + spec₂) ((spec₁ + spec₂).Range t)) =
      match t with
        | .inl t => liftM (liftM (query t)  : OracleQuery spec₃ _)
        | .inr t => query (Sum.inr t) := by aesop

end left_add_left_add

section right_add_right_add

instance subSpec_right_add_right_add_of_subSpec [h : spec₂ ⊂ₒ spec₃] :
    spec₁ + spec₂ ⊂ₒ spec₁ + spec₃ where
  monadLift
    | .mk (.inl q) f => .mk (.inl q) f
    | .mk (.inr q) f => liftM (OracleQuery.mk q f)

@[simp] lemma liftM_right_add_right_add_def
    [h : spec₂ ⊂ₒ spec₃] (q : OracleQuery (spec₁ + spec₂) α) :
    (liftM q : OracleQuery (spec₁ + spec₃) α) = match q with
      | .mk (.inl q) f => .mk (.inl q) f
      | .mk (.inr q) f => (liftM (liftM (OracleQuery.mk q f) : OracleQuery spec₃ _)) := rfl

@[simp high] lemma liftM_right_add_right_add_query
    [h : spec₂ ⊂ₒ spec₃] (t : (spec₁ + spec₂).Domain) :
    (liftM (query t) : OracleQuery (spec₁ + spec₃) ((spec₁ + spec₂).Range t)) =
      match t with
        | .inl t => query (Sum.inl t)
        | .inr t => liftM (liftM (query t) : OracleQuery spec₃ _) := by aesop

end right_add_right_add

section add_assoc

instance subSpec_add_assoc : spec₁ + (spec₂ + spec₃) ⊂ₒ spec₁ + spec₂ + spec₃ where
  monadLift
    | ⟨.inl t, f⟩ => ⟨.inl (.inl t), f⟩
    | ⟨.inr (.inl t), f⟩ => ⟨.inl (.inr t), f⟩
    | ⟨.inr (.inr t), f⟩ => ⟨.inr t, f⟩

@[simp] lemma liftM_add_assoc_def (q : OracleQuery (spec₁ + (spec₂ + spec₃)) α) :
    (liftM q : OracleQuery (spec₁ + spec₂ + spec₃) α) =
    match q with
    | ⟨.inl t, f⟩ => ⟨.inl (.inl t), f⟩
    | ⟨.inr (.inl t), f⟩ => ⟨.inl (.inr t), f⟩
    | ⟨.inr (.inr t), f⟩ => ⟨.inr t, f⟩ := rfl

@[simp] lemma liftM_add_assoc_query (t : (spec₁ + (spec₂ + spec₃)).Domain) :
    (liftM (query t) : OracleQuery (spec₁ + spec₂ + spec₃) ((spec₁ + (spec₂ + spec₃)).Range t)) =
      match t with
        | .inl t => query (Sum.inl (Sum.inl t))
        | .inr (.inl t) => query (Sum.inl (Sum.inr t))
        | .inr (.inr t) => query (Sum.inr t) := by
  rcases t with t | t | t <;> simp [query_def]

end add_assoc

section sigma

variable {σ ι} (specs : σ → OracleSpec ι)

-- dtumad: we could expand this more to lifting a finite sum to the sigma type

instance subSpec_sigma {σ ι} (specs : σ → OracleSpec ι) (j : σ) :
    specs j ⊂ₒ OracleSpec.sigma specs where
  monadLift | .mk t f => .mk ⟨j, t⟩ f

@[simp low] lemma liftM_sigma_def (j : σ) (q : OracleQuery (specs j) α) :
    (liftM q : OracleQuery (OracleSpec.sigma specs) _) = .mk ⟨j, q.input⟩ q.cont := rfl

@[simp] lemma liftM_sigma_query (j : σ) (t : (specs j).Domain) :
    (liftM (query t) : OracleQuery (OracleSpec.sigma specs) ((specs j).Range t)) =
      query (spec := OracleSpec.sigma specs) ⟨j, t⟩ := rfl

end sigma

end instances

@[simp low] -- dtumad: the `simp` tag could be dangerous even at low I think
lemma liftM_eq_liftM_liftM [spec₁ ⊂ₒ spec₂]
    [MonadLift (OracleQuery spec₂) (OracleQuery spec₃)] (q : OracleQuery spec₁ α) :
    (liftM q : OracleQuery spec₃ α) =
      (liftM (liftM q : OracleQuery spec₂ α) : OracleQuery spec₃ α) := by rfl

end OracleQuery

section tests

set_option linter.unusedVariables false

-- This set of examples serves as sort of a "unit test" for the coercions above
variable (α : Type)
  {ι₁ ι₂ ι₃ ι₄ ι ι'}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄}
  (coeSpec : OracleSpec ι) (coeSuperSpec : OracleSpec ι')
  [coeSpec ⊂ₒ coeSuperSpec]

-- coerce a single `coin_spec` and then add extra oracles
example (oa : OracleComp coeSpec α) :
  OracleComp (coeSuperSpec + spec₂ + spec₃) α := oa
example (oa : OracleComp coeSpec α) :
  OracleComp (spec₁ + coeSuperSpec + spec₂) α := oa
example (oa : OracleComp coeSpec α) :
  OracleComp (spec₁ + spec₂ + coeSuperSpec) α := oa

-- coerce left side of add and then add on additional oracles
example (oa : OracleComp (coeSpec + spec₁) α) :
  OracleComp (coeSuperSpec + spec₁ + spec₂) α := oa
example (oa : OracleComp (coeSpec + spec₁) α) :
  OracleComp (coeSuperSpec + spec₂ + spec₁) α := oa
example (oa : OracleComp (coeSpec + spec₁) α) :
  OracleComp (spec₂ + coeSuperSpec + spec₁) α := oa

-- coerce right side of add and then add on additional oracles
example (oa : OracleComp (spec₁ + coeSpec) α) :
  OracleComp (spec₁ + coeSuperSpec + spec₂) α := oa
example (oa : OracleComp (spec₁ + coeSpec) α) :
  OracleComp (spec₁ + spec₂ + coeSuperSpec) α := oa
example (oa : OracleComp (spec₁ + coeSpec) α) :
  OracleComp (spec₂ + spec₁ + coeSuperSpec) α := oa

-- coerce an inside part while also applying associativity
example (oa : OracleComp (spec₁ + (spec₂ + coeSpec)) α) :
  OracleComp (spec₁ + spec₂ + coeSuperSpec) α := oa
example (oa : OracleComp (spec₁ + (coeSpec + spec₂)) α) :
  OracleComp (spec₁ + coeSuperSpec + spec₂) α := oa
example (oa : OracleComp (coeSpec + (spec₁ + spec₂)) α) :
  OracleComp (coeSuperSpec + spec₁ + spec₂) α := oa

-- coerce two oracles up to four oracles
example (oa : OracleComp (spec₁ + spec₂) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₁ + spec₃) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₁ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₂ + spec₃) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₂ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₃ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- coerce threee oracles up to four oracles
example (oa : OracleComp (spec₁ + spec₂ + spec₃) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₁ + spec₂ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₁ + spec₃ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp (spec₂ + spec₃ + spec₄) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + spec₄) α := oa

-- four oracles with associativity and internal coercion
example (oa : OracleComp ((coeSpec + spec₂) + (spec₃ + spec₄)) α) :
  OracleComp (coeSuperSpec + spec₂ + spec₃ + spec₄) α := oa
example (oa : OracleComp ((spec₁ + spec₂) + (coeSpec + spec₄)) α) :
  OracleComp (spec₁ + spec₂ + coeSuperSpec + spec₄) α := oa
example (oa : OracleComp ((spec₁ + coeSpec) + (spec₃ + spec₄)) α) :
  OracleComp (spec₁ + coeSuperSpec + spec₃ + spec₄) α := oa
example (oa : OracleComp ((spec₁ + spec₂) + (spec₃ + coeSuperSpec)) α) :
  OracleComp (spec₁ + spec₂ + spec₃ + coeSuperSpec) α := oa

/-- coercion makes it possible to mix computations on individual oracles -/
example : OracleComp (unifSpec + spec₁) Bool := do
  let n : Fin 315 ←$[0..314]; let m : Fin 315 ←$[0..314]
  if n = m then return true else $! #v[true, false]

-- Testing that simp pathways work well different lifting orders
example (q : OracleQuery spec₁ α) :
    (liftM (liftM q : OracleQuery (spec₁ + spec₂) α) :
      OracleQuery (spec₁ + spec₂ + spec₃) α) =
    (liftM (liftM q : OracleQuery (spec₁ + spec₃) α) :
      OracleQuery (spec₁ + spec₂ + spec₃) α) := by simp
example (q : OracleQuery spec₁ α) :
    (liftM (liftM q : OracleQuery (spec₁ + (spec₂ + spec₃)) α) :
      OracleQuery (spec₁ + spec₂ + spec₃) α) =
    (liftM (liftM q : OracleQuery (spec₁ + spec₃) α) :
      OracleQuery (spec₁ + spec₂ + spec₃) α) := by simp

end tests
