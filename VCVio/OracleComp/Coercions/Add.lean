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
either `OracleSpec.add` or `OracleSpec.sigma`. Each instance spells out the
`monadLift` action explicitly (rather than letting it default from
`onQuery` / `onResponse`) so that the lifted query reduces fully under
`isDefEq`. This is load-bearing for `rw` / `simp` lemmas like
`probEvent_liftComp` to find their pattern through the synthesized
`MonadLiftT` instance chain.
-/

open OracleSpec

open scoped OracleSpec.PrimitiveQuery

namespace OracleQuery

universe u v w

variable {ι₁} {ι₂} {ι₃} {ι₄}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄} {α β γ : Type u}

section instances

/-- We need `Inhabited` to prevent infinite type-class searching. -/
instance (priority := low) {τ : Type u} [Inhabited τ] {spec : OracleSpec.{u, v} τ} :
    OracleSpec.emptySpec.{u,v} ⊂ₒ spec where
  monadLift q := PEmpty.elim q.input
  onQuery t := t.elim
  onResponse t := t.elim
  liftM_eq_lift q := PEmpty.elim q.input

instance (priority := low) {τ : Type u} [Inhabited τ] {spec : OracleSpec.{u, v} τ} :
    OracleSpec.emptySpec ˡ⊂ₒ spec where
  onResponse_bijective t := PEmpty.elim t

section add_left

/-- Add additional oracles to the right side of the existing ones. -/
instance subSpec_add_left : spec₁ ⊂ₒ (spec₁ + spec₂) where
  monadLift q := ⟨.inl q.input, q.cont⟩
  onQuery := Sum.inl
  onResponse _ := id

@[simp] lemma liftM_add_left_def (q : OracleQuery spec₁ α) :
    (liftM q : OracleQuery (spec₁ + spec₂) α) = .mk (.inl q.input) q.cont := rfl

@[simp high] lemma liftM_add_left_query (t : spec₁.Domain) :
    (liftM (query t) : OracleQuery (spec₁ + spec₂) (spec₁.Range t)) = query (Sum.inl t) := rfl

instance lawfulSubSpec_add_left : spec₁ ˡ⊂ₒ (spec₁ + spec₂) where
  onResponse_bijective _ := Function.bijective_id

end add_left

section add_right

/-- Add additional oracles to the left side of the exiting ones. -/
instance subSpec_add_right : spec₂ ⊂ₒ (spec₁ + spec₂) where
  monadLift q := ⟨.inr q.input, q.cont⟩
  onQuery := Sum.inr
  onResponse _ := id

@[simp] lemma liftM_add_right_def (q : OracleQuery spec₂ α) :
    (liftM q : OracleQuery (spec₁ + spec₂) α) = .mk (.inr q.input) q.cont := rfl

@[simp high] lemma liftM_add_right_query (t : spec₂.Domain) :
    (liftM (query t) : OracleQuery (spec₁ + spec₂) (spec₂.Range t)) = query (Sum.inr t) := rfl

instance lawfulSubSpec_add_right : spec₂ ˡ⊂ₒ (spec₁ + spec₂) where
  onResponse_bijective _ := Function.bijective_id

instance disjointSubSpec_add_left_right :
    OracleSpec.DisjointSubSpec spec₁ spec₂ (spec₁ + spec₂) where
  disjoint_onQuery _ _ := by rintro ⟨⟩

instance disjointSubSpec_add_right_left :
    OracleSpec.DisjointSubSpec spec₂ spec₁ (spec₁ + spec₂) where
  disjoint_onQuery _ _ := by rintro ⟨⟩

end add_right

section left_add_left_add

/-- Congruence on the left summand: an inclusion `spec₁ ⊂ₒ spec₃` extends to
`spec₁ + spec₂ ⊂ₒ spec₃ + spec₂`.

Low priority so that searches whose source spec is a metavariable (notably the
`MonadLiftT (OracleComp spec) (OracleComp superSpec)` chain behind whole-computation
coercions) prefer the direct embeddings `subSpec_add_left` / `subSpec_add_right`. This keeps
such coercions a single `liftComp`, definitionally, instead of a stack of lifts through an
intermediate spec. -/
instance (priority := low) subSpec_left_add_left_add_of_subSpec [h : spec₁ ⊂ₒ spec₃] :
    spec₁ + spec₂ ⊂ₒ spec₃ + spec₂ where
  monadLift
    | ⟨.inl t, f⟩ => ⟨.inl (h.onQuery t), f ∘ h.onResponse t⟩
    | ⟨.inr t, f⟩ => ⟨.inr t, f⟩
  onQuery
    | .inl t => .inl (h.onQuery t)
    | .inr t => .inr t
  onResponse
    | .inl t => h.onResponse t
    | .inr _ => id
  liftM_eq_lift q := by rcases q with ⟨_ | _, _⟩ <;> rfl

@[simp] lemma liftM_left_add_left_add_def
    [h : spec₁ ⊂ₒ spec₃] (q : OracleQuery (spec₁ + spec₂) α) :
    (liftM q : OracleQuery (spec₃ + spec₂) α) = match q with
      | .mk (.inl q) f => liftM ((liftM (OracleQuery.mk q f) : OracleQuery spec₃ _))
      | .mk (.inr q) f => .mk (.inr q) f := by
  rcases q with ⟨t | t, f⟩
  · change _ = liftM (liftM (OracleQuery.mk t f) : OracleQuery spec₃ _)
    rw [show (liftM (OracleQuery.mk t f) : OracleQuery spec₃ _) =
      ⟨h.onQuery t, f ∘ h.onResponse t⟩ from h.liftM_eq_lift _]
    rfl
  · rfl

@[simp high] lemma liftM_left_add_left_add_query
    [h : spec₁ ⊂ₒ spec₃] (t : (spec₁ + spec₂).Domain) :
    (liftM (query t) : OracleQuery (spec₃ + spec₂) ((spec₁ + spec₂).Range t)) =
      match t with
        | .inl t => liftM (liftM (query t) : OracleQuery spec₃ _)
        | .inr t => query (Sum.inr t) := by
  rw [liftM_left_add_left_add_def]
  rcases t with t | t <;> rfl

instance lawfulSubSpec_left_add_left_add [spec₁ ⊂ₒ spec₃]
    [spec₁ ˡ⊂ₒ spec₃] :
    spec₁ + spec₂ ˡ⊂ₒ spec₃ + spec₂ where
  onResponse_bijective t := by
    match t with
    | .inl t =>
      exact OracleSpec.LawfulSubSpec.onResponse_bijective (spec := spec₁) (superSpec := spec₃) t
    | .inr _ => exact Function.bijective_id

end left_add_left_add

section right_add_right_add

/-- Congruence on the right summand: an inclusion `spec₂ ⊂ₒ spec₃` extends to
`spec₁ + spec₂ ⊂ₒ spec₁ + spec₃`.

Low priority for the same reason as `subSpec_left_add_left_add_of_subSpec`: the direct
embeddings must win metavariable-headed searches so that whole-computation coercions stay a
single `liftComp`. -/
instance (priority := low) subSpec_right_add_right_add_of_subSpec [h : spec₂ ⊂ₒ spec₃] :
    spec₁ + spec₂ ⊂ₒ spec₁ + spec₃ where
  monadLift
    | ⟨.inl t, f⟩ => ⟨.inl t, f⟩
    | ⟨.inr t, f⟩ => ⟨.inr (h.onQuery t), f ∘ h.onResponse t⟩
  onQuery
    | .inl t => .inl t
    | .inr t => .inr (h.onQuery t)
  onResponse
    | .inl _ => id
    | .inr t => h.onResponse t
  liftM_eq_lift q := by rcases q with ⟨_ | _, _⟩ <;> rfl

@[simp] lemma liftM_right_add_right_add_def
    [h : spec₂ ⊂ₒ spec₃] (q : OracleQuery (spec₁ + spec₂) α) :
    (liftM q : OracleQuery (spec₁ + spec₃) α) = match q with
      | .mk (.inl q) f => .mk (.inl q) f
      | .mk (.inr q) f => (liftM (liftM (OracleQuery.mk q f) : OracleQuery spec₃ _)) := by
  rcases q with ⟨t | t, f⟩
  · rfl
  · change _ = liftM (liftM (OracleQuery.mk t f) : OracleQuery spec₃ _)
    rw [show (liftM (OracleQuery.mk t f) : OracleQuery spec₃ _) =
      ⟨h.onQuery t, f ∘ h.onResponse t⟩ from h.liftM_eq_lift _]
    rfl

@[simp high] lemma liftM_right_add_right_add_query
    [h : spec₂ ⊂ₒ spec₃] (t : (spec₁ + spec₂).Domain) :
    (liftM (query t) : OracleQuery (spec₁ + spec₃) ((spec₁ + spec₂).Range t)) =
      match t with
        | .inl t => query (Sum.inl t)
        | .inr t => liftM (liftM (query t) : OracleQuery spec₃ _) := by
  rw [liftM_right_add_right_add_def]
  rcases t with t | t <;> rfl

instance lawfulSubSpec_right_add_right_add [spec₂ ⊂ₒ spec₃]
    [spec₂ ˡ⊂ₒ spec₃] :
    spec₁ + spec₂ ˡ⊂ₒ spec₁ + spec₃ where
  onResponse_bijective t := by
    match t with
    | .inl _ => exact Function.bijective_id
    | .inr t =>
      exact OracleSpec.LawfulSubSpec.onResponse_bijective (spec := spec₂) (superSpec := spec₃) t

end right_add_right_add

section add_assoc

instance subSpec_add_assoc : spec₁ + (spec₂ + spec₃) ⊂ₒ spec₁ + spec₂ + spec₃ where
  monadLift
    | ⟨.inl t, f⟩ => ⟨.inl (.inl t), f⟩
    | ⟨.inr (.inl t), f⟩ => ⟨.inl (.inr t), f⟩
    | ⟨.inr (.inr t), f⟩ => ⟨.inr t, f⟩
  onQuery
    | .inl t => .inl (.inl t)
    | .inr (.inl t) => .inl (.inr t)
    | .inr (.inr t) => .inr t
  onResponse
    | .inl _ => id
    | .inr (.inl _) => id
    | .inr (.inr _) => id
  liftM_eq_lift q := by rcases q with ⟨_ | _ | _, _⟩ <;> rfl

@[simp] lemma liftM_add_assoc_def (q : OracleQuery (spec₁ + (spec₂ + spec₃)) α) :
    (liftM q : OracleQuery (spec₁ + spec₂ + spec₃) α) =
    match q with
    | ⟨.inl t, f⟩ => ⟨.inl (.inl t), f⟩
    | ⟨.inr (.inl t), f⟩ => ⟨.inl (.inr t), f⟩
    | ⟨.inr (.inr t), f⟩ => ⟨.inr t, f⟩ := by
  rcases q with ⟨t | t | t, f⟩ <;> rfl

@[simp] lemma liftM_add_assoc_query (t : (spec₁ + (spec₂ + spec₃)).Domain) :
    (liftM (query t) : OracleQuery (spec₁ + spec₂ + spec₃) ((spec₁ + (spec₂ + spec₃)).Range t)) =
      match t with
        | .inl t => query (Sum.inl (Sum.inl t))
        | .inr (.inl t) => query (Sum.inl (Sum.inr t))
        | .inr (.inr t) => query (Sum.inr t) := by
  rcases t with t | t | t <;> rfl

instance lawfulSubSpec_add_assoc :
    spec₁ + (spec₂ + spec₃) ˡ⊂ₒ spec₁ + spec₂ + spec₃ where
  onResponse_bijective t := by
    rcases t with t | t | t <;> exact Function.bijective_id

end add_assoc

section sigma

variable {σ ι} (specs : σ → OracleSpec ι)

-- dtumad: we could expand this more to lifting a finite sum to the sigma type

instance subSpec_sigma {σ ι} (specs : σ → OracleSpec ι) (j : σ) :
    specs j ⊂ₒ OracleSpec.sigma specs where
  monadLift q := ⟨⟨j, q.input⟩, q.cont⟩
  onQuery t := ⟨j, t⟩
  onResponse _ := id

@[simp low] lemma liftM_sigma_def (j : σ) (q : OracleQuery (specs j) α) :
    (liftM q : OracleQuery (OracleSpec.sigma specs) _) = .mk ⟨j, q.input⟩ q.cont := rfl

@[simp] lemma liftM_sigma_query (j : σ) (t : (specs j).Domain) :
    (liftM (query t) : OracleQuery (OracleSpec.sigma specs) ((specs j).Range t)) =
      (OracleSpec.sigma specs).query ⟨j, t⟩ := rfl

instance lawfulSubSpec_sigma (j : σ) :
    specs j ˡ⊂ₒ OracleSpec.sigma specs where
  onResponse_bijective _ := Function.bijective_id

end sigma

end instances

@[simp low] -- dtumad: the `simp` tag could be dangerous even at low I think
lemma liftM_eq_liftM_liftM [spec₁ ⊂ₒ spec₂]
    [MonadLift (OracleQuery spec₂) (OracleQuery spec₃)] (q : OracleQuery spec₁ α) :
    (liftM q : OracleQuery spec₃ α) =
      (liftM (liftM q : OracleQuery spec₂ α) : OracleQuery spec₃ α) := rfl

end OracleQuery

section tests

-- This set of examples serves as sort of a "unit test" for the coercions above
variable (α : Type)
  {ι₁ ι₂ ι₃ ι₄ ι ι'}
  {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
  {spec₃ : OracleSpec ι₃} {spec₄ : OracleSpec ι₄}
  (coeSpec : OracleSpec ι) (coeSuperSpec : OracleSpec ι')
  [_hSub : coeSpec ⊂ₒ coeSuperSpec]

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

-- Whole-computation coercions into a sum spec are *definitionally* a single `liftComp`,
-- with no intermediate hop through another spec. In particular lifting out of `ProbComp`
-- (e.g. into a random-oracle spec `unifSpec + (T →ₒ U)`) is `liftComp` by `rfl`.
example (oa : OracleComp spec₁ α) :
    (oa : OracleComp (spec₁ + spec₂) α) = OracleComp.liftComp oa (spec₁ + spec₂) := rfl
example (oa : OracleComp spec₂ α) :
    (oa : OracleComp (spec₁ + spec₂) α) = OracleComp.liftComp oa (spec₁ + spec₂) := rfl
example (px : ProbComp α) :
    (px : OracleComp (unifSpec + spec₁) α) = OracleComp.liftComp px (unifSpec + spec₁) := rfl

end tests
