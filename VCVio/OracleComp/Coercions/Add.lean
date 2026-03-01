/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/
import VCVio.OracleComp.Coercions.SubSpec
import VCVio.OracleComp.ProbComp

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
instance (priority := low) {τ : Type u} [Inhabited τ] {spec : OracleSpec.{u,v} τ} :
    OracleSpec.emptySpec.{u,v} ⊂ₒ spec where
  monadLift | q => PEmpty.elim q.input
  liftM_map q := PEmpty.elim q.input

instance (priority := low) {τ : Type u} [Inhabited τ] {spec : OracleSpec.{u,v} τ} :
    OracleSpec.LawfulSubSpec OracleSpec.emptySpec spec where
  cont_bijective t := PEmpty.elim t

section add_left

/-- Add additional oracles to the right side of the existing ones. -/
instance subSpec_add_left : spec₁ ⊂ₒ (spec₁ + spec₂) where
  monadLift | q => .mk (.inl q.input) q.cont
  liftM_map | q => by simp [liftM, monadLift]

@[simp] lemma liftM_add_left_def (q : OracleQuery spec₁ α) :
    (liftM q : OracleQuery (spec₁ + spec₂) α) = .mk (.inl q.input) q.cont := rfl

@[simp high] lemma liftM_add_left_query (t : spec₁.Domain) :
    (liftM (query t) : OracleQuery (spec₁ + spec₂) (spec₁.Range t)) = query (Sum.inl t) := rfl

instance lawfulSubSpec_add_left : OracleSpec.LawfulSubSpec spec₁ (spec₁ + spec₂) where
  cont_bijective _ := Function.bijective_id

end add_left

section add_right

/-- Add additional oracles to the left side of the exiting ones-/
instance subSpec_add_right : spec₂ ⊂ₒ (spec₁ + spec₂) where
  monadLift | q => .mk (.inr q.input) q.cont
  liftM_map | ⟨t, g⟩ => by simp [liftM, monadLift]

@[simp] lemma liftM_add_right_def (q : OracleQuery spec₂ α) :
    (liftM q : OracleQuery (spec₁ + spec₂) α) = .mk (.inr q.input) q.cont := rfl

@[simp high] lemma liftM_add_right_query (t : spec₂.Domain) :
    (liftM (query t) : OracleQuery (spec₁ + spec₂) (spec₂.Range t)) = query (Sum.inr t) := rfl

instance lawfulSubSpec_add_right : OracleSpec.LawfulSubSpec spec₂ (spec₁ + spec₂) where
  cont_bijective _ := Function.bijective_id

end add_right

section left_add_left_add

instance subSpec_left_add_left_add_of_subSpec [h : spec₁ ⊂ₒ spec₃] :
    spec₁ + spec₂ ⊂ₒ spec₃ + spec₂ where
  monadLift
    | .mk (.inl q) f => liftM (OracleQuery.mk q f)
    | .mk (.inr q) f => .mk (.inr q) f
  liftM_map
    | .mk (.inl q) f => by
      intro g
      calc
        (liftM (liftM (OracleQuery.mk q (g ∘ f)) : OracleQuery spec₃ _) :
            OracleQuery (spec₃ + spec₂) _) =
            (liftM (g <$> (liftM (OracleQuery.mk q f) : OracleQuery spec₃ _)) :
              OracleQuery (spec₃ + spec₂) _) := by
              simpa [liftM, monadLift] using
                congrArg (fun z => (liftM z : OracleQuery (spec₃ + spec₂) _))
                  (OracleSpec.SubSpec.liftM_map (spec := spec₁) (superSpec := spec₃)
                    (q := OracleQuery.mk q f) (f := g))
        _ = g <$> (liftM (liftM (OracleQuery.mk q f) : OracleQuery spec₃ _) :
            OracleQuery (spec₃ + spec₂) _) := by
              simpa [liftM, monadLift] using
                (OracleSpec.SubSpec.liftM_map (spec := spec₃) (superSpec := spec₃ + spec₂)
                  (q := (liftM (OracleQuery.mk q f) : OracleQuery spec₃ _)) (f := g))
    | .mk (.inr q) f => by simp [liftM, monadLift]

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

instance lawfulSubSpec_left_add_left_add [spec₁ ⊂ₒ spec₃]
    [OracleSpec.LawfulSubSpec spec₁ spec₃] :
    OracleSpec.LawfulSubSpec (spec₁ + spec₂) (spec₃ + spec₂) where
  cont_bijective t := by
    match t with
    | .inl t => exact OracleSpec.LawfulSubSpec.cont_bijective (spec := spec₁) (superSpec := spec₃) t
    | .inr _ => exact Function.bijective_id

end left_add_left_add

section right_add_right_add

instance subSpec_right_add_right_add_of_subSpec [h : spec₂ ⊂ₒ spec₃] :
    spec₁ + spec₂ ⊂ₒ spec₁ + spec₃ where
  monadLift
    | .mk (.inl q) f => .mk (.inl q) f
    | .mk (.inr q) f => liftM (OracleQuery.mk q f)
  liftM_map
    | .mk (.inl q) f => by simp [liftM, monadLift]
    | .mk (.inr q) f => by
      intro g
      calc
        (liftM (liftM (OracleQuery.mk q (g ∘ f)) : OracleQuery spec₃ _) :
            OracleQuery (spec₁ + spec₃) _) =
            (liftM (g <$> (liftM (OracleQuery.mk q f) : OracleQuery spec₃ _)) :
              OracleQuery (spec₁ + spec₃) _) := by
              simpa [liftM, monadLift] using
                congrArg (fun z => (liftM z : OracleQuery (spec₁ + spec₃) _))
                  (OracleSpec.SubSpec.liftM_map (spec := spec₂) (superSpec := spec₃)
                    (q := OracleQuery.mk q f) (f := g))
        _ = g <$> (liftM (liftM (OracleQuery.mk q f) : OracleQuery spec₃ _) :
            OracleQuery (spec₁ + spec₃) _) := by
              simpa [liftM, monadLift] using
                (OracleSpec.SubSpec.liftM_map (spec := spec₃) (superSpec := spec₁ + spec₃)
                  (q := (liftM (OracleQuery.mk q f) : OracleQuery spec₃ _)) (f := g))

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

instance lawfulSubSpec_right_add_right_add [spec₂ ⊂ₒ spec₃]
    [OracleSpec.LawfulSubSpec spec₂ spec₃] :
    OracleSpec.LawfulSubSpec (spec₁ + spec₂) (spec₁ + spec₃) where
  cont_bijective t := by
    match t with
    | .inl _ => exact Function.bijective_id
    | .inr t => exact OracleSpec.LawfulSubSpec.cont_bijective (spec := spec₂) (superSpec := spec₃) t

end right_add_right_add

section add_assoc

instance subSpec_add_assoc : spec₁ + (spec₂ + spec₃) ⊂ₒ spec₁ + spec₂ + spec₃ where
  monadLift
    | ⟨.inl t, f⟩ => ⟨.inl (.inl t), f⟩
    | ⟨.inr (.inl t), f⟩ => ⟨.inl (.inr t), f⟩
    | ⟨.inr (.inr t), f⟩ => ⟨.inr t, f⟩
  liftM_map
    | ⟨.inl t, f⟩ => by simp [liftM, monadLift]
    | ⟨.inr (.inl t), f⟩ => by simp [liftM, monadLift]
    | ⟨.inr (.inr t), f⟩ => by simp [liftM, monadLift]

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

instance lawfulSubSpec_add_assoc :
    OracleSpec.LawfulSubSpec (spec₁ + (spec₂ + spec₃)) (spec₁ + spec₂ + spec₃) where
  cont_bijective t := by
    rcases t with t | t | t <;> exact Function.bijective_id

end add_assoc

section sigma

variable {σ ι} (specs : σ → OracleSpec ι)

-- dtumad: we could expand this more to lifting a finite sum to the sigma type

instance subSpec_sigma {σ ι} (specs : σ → OracleSpec ι) (j : σ) :
    specs j ⊂ₒ OracleSpec.sigma specs where
  monadLift | .mk t f => .mk ⟨j, t⟩ f
  liftM_map | .mk t f => by simp [liftM, monadLift]

@[simp low] lemma liftM_sigma_def (j : σ) (q : OracleQuery (specs j) α) :
    (liftM q : OracleQuery (OracleSpec.sigma specs) _) = .mk ⟨j, q.input⟩ q.cont := rfl

@[simp] lemma liftM_sigma_query (j : σ) (t : (specs j).Domain) :
    (liftM (query t) : OracleQuery (OracleSpec.sigma specs) ((specs j).Range t)) =
      query (spec := OracleSpec.sigma specs) ⟨j, t⟩ := rfl

instance lawfulSubSpec_sigma (j : σ) :
    OracleSpec.LawfulSubSpec (specs j) (OracleSpec.sigma specs) where
  cont_bijective _ := Function.bijective_id

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

-- coerce a single oracle and then add extra oracles
example (oa : OracleComp spec₁ α) :
  OracleComp ((spec₁ + spec₂) + spec₃) α := oa
example (oa : OracleComp spec₂ α) :
  OracleComp ((spec₁ + spec₂) + spec₂) α := oa
example (oa : OracleComp spec₃ α) :
  OracleComp ((spec₁ + spec₂) + spec₃) α := oa
example (oa : OracleComp spec₁ α) :
  OracleComp (spec₁ + (spec₂ + spec₃)) α := oa
example (oa : OracleComp spec₂ α) :
  OracleComp (spec₁ + (spec₂ + spec₂)) α := oa
example (oa : OracleComp spec₃ α) :
  OracleComp (spec₁ + (spec₂ + spec₃)) α := oa

-- coerce a single oracle and then add extra oracles
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
