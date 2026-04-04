/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Order

/-!
# Structured Resource Profiles

This file defines a compositional resource profile for open computations.

A `ResourceProfile ω κ` separates two kinds of cost:

- `intrinsic : ω`, the concrete runtime cost of the code itself;
- `usage : κ →₀ ℕ`, a symbolic count of how often the code invokes each external capability.

This split is useful for reduction proofs. We can first analyze an open reduction body in terms of
its intrinsic overhead and interface usage, and only later instantiate those interface calls with
the cost profiles of the adversaries or subroutines that implement them.
-/

open scoped BigOperators

/-- Structured resource profile for open computations.

`intrinsic` is the concrete cost paid by the computation itself. `usage k` counts how many times
the computation invokes external capability `k`. -/
@[ext] structure ResourceProfile (ω : Type*) (κ : Type*) where
  intrinsic : ω
  usage : κ →₀ ℕ

namespace ResourceProfile

variable {ω κ κ' κ'' : Type*}

/-- Pure intrinsic cost with no external capability usage. -/
def ofIntrinsic (w : ω) : ResourceProfile ω κ where
  intrinsic := w
  usage := 0

/-- Pure external usage with zero intrinsic cost. -/
def ofUsage [Zero ω] (u : κ →₀ ℕ) : ResourceProfile ω κ where
  intrinsic := 0
  usage := u

/-- A single capability use counted `n` times, with zero intrinsic cost. -/
noncomputable def single [Zero ω] (k : κ) (n : ℕ := 1) : ResourceProfile ω κ :=
  ofUsage (Finsupp.single k n)

instance [Zero ω] : Zero (ResourceProfile ω κ) :=
  ⟨ofIntrinsic (κ := κ) 0⟩

noncomputable instance [Add ω] : Add (ResourceProfile ω κ) where
  add a b :=
    { intrinsic := a.intrinsic + b.intrinsic
      usage := a.usage + b.usage }

@[simp] lemma intrinsic_zero [Zero ω] :
    (0 : ResourceProfile ω κ).intrinsic = 0 := rfl

@[simp] lemma usage_zero [Zero ω] :
    (0 : ResourceProfile ω κ).usage = 0 := rfl

@[simp] lemma intrinsic_add [Add ω] (a b : ResourceProfile ω κ) :
    (a + b).intrinsic = a.intrinsic + b.intrinsic := rfl

@[simp] lemma usage_add [Add ω] (a b : ResourceProfile ω κ) :
    (a + b).usage = a.usage + b.usage := rfl

@[simp] lemma intrinsic_ofIntrinsic (w : ω) :
    (ofIntrinsic (κ := κ) w).intrinsic = w := rfl

@[simp] lemma usage_ofIntrinsic (w : ω) :
    (ofIntrinsic (κ := κ) w).usage = 0 := rfl

@[simp] lemma ofIntrinsic_zero [Zero ω] :
    ofIntrinsic (κ := κ) (0 : ω) = 0 := rfl

@[simp] lemma intrinsic_ofUsage [Zero ω] (u : κ →₀ ℕ) :
    (ofUsage (ω := ω) u).intrinsic = 0 := rfl

@[simp] lemma usage_ofUsage [Zero ω] (u : κ →₀ ℕ) :
    (ofUsage (ω := ω) u).usage = u := rfl

@[simp] lemma intrinsic_single [Zero ω] (k : κ) (n : ℕ := 1) :
    (single (ω := ω) k n).intrinsic = 0 := rfl

@[simp] lemma usage_single [Zero ω] (k : κ) (n : ℕ := 1) :
    (single (ω := ω) k n).usage = Finsupp.single k n := rfl

noncomputable instance [AddMonoid ω] : AddMonoid (ResourceProfile ω κ) where
  zero := 0
  add := (· + ·)
  nsmul n a :=
    { intrinsic := n • a.intrinsic
      usage := n • a.usage }
  zero_add a := by ext <;> simp
  add_zero a := by ext <;> simp
  add_assoc a b c := by ext <;> simp [add_assoc]
  nsmul_zero a := by ext <;> simp
  nsmul_succ n a := by ext <;> simp [succ_nsmul, add_comm]

@[simp] lemma intrinsic_nsmul [AddMonoid ω] (n : ℕ) (a : ResourceProfile ω κ) :
    (n • a).intrinsic = n • a.intrinsic := rfl

@[simp] lemma usage_nsmul [AddMonoid ω] (n : ℕ) (a : ResourceProfile ω κ) :
    (n • a).usage = n • a.usage := rfl

noncomputable instance [AddCommMonoid ω] : AddCommMonoid (ResourceProfile ω κ) where
  add_comm a b := by ext <;> simp [add_comm]

def toProd (c : ResourceProfile ω κ) : ω × (κ →₀ ℕ) :=
  (c.intrinsic, c.usage)

instance [LE ω] : LE (ResourceProfile ω κ) where
  le a b := a.toProd ≤ b.toProd

@[simp] lemma toProd_mk (intrinsic : ω) (usage : κ →₀ ℕ) :
    toProd ⟨intrinsic, usage⟩ = (intrinsic, usage) := rfl

@[simp] lemma le_def [LE ω] {a b : ResourceProfile ω κ} :
    a ≤ b ↔ a.intrinsic ≤ b.intrinsic ∧ a.usage ≤ b.usage := Iff.rfl

instance [Preorder ω] : Preorder (ResourceProfile ω κ) where
  le := (· ≤ ·)
  le_refl a := ⟨le_rfl, le_rfl⟩
  le_trans a b c hab hbc := ⟨le_trans hab.1 hbc.1, le_trans hab.2 hbc.2⟩

instance [PartialOrder ω] : PartialOrder (ResourceProfile ω κ) where
  le := (· ≤ ·)
  le_refl a := ⟨le_rfl, le_rfl⟩
  le_trans a b c hab hbc := ⟨le_trans hab.1 hbc.1, le_trans hab.2 hbc.2⟩
  le_antisymm a b hab hba := by
    have hprod : a.toProd = b.toProd := le_antisymm hab hba
    cases a
    cases b
    cases hprod
    rfl

instance [AddCommMonoid ω] [PartialOrder ω] [IsOrderedAddMonoid ω] :
    IsOrderedAddMonoid (ResourceProfile ω κ) where
  add_le_add_left _ _ hab _ := ⟨add_le_add_left hab.1 _, add_le_add_left hab.2 _⟩

/-- Evaluate a structured resource profile against concrete per-capability costs. -/
def eval [AddCommMonoid ω] (c : ResourceProfile ω κ) (w : κ → ω) : ω :=
  c.intrinsic + c.usage.sum (fun k n ↦ n • w k)

/-- Instantiate the symbolic capability usage in `c` with open implementations `impl`. -/
noncomputable def instantiate [AddCommMonoid ω]
    (c : ResourceProfile ω κ) (impl : κ → ResourceProfile ω κ') :
    ResourceProfile ω κ' :=
  ofIntrinsic (κ := κ') c.intrinsic + c.usage.sum (fun k n ↦ n • impl k)

def intrinsicAddMonoidHom [AddMonoid ω] : ResourceProfile ω κ →+ ω where
  toFun := intrinsic
  map_zero' := rfl
  map_add' _ _ := rfl

def usageAddMonoidHom [AddMonoid ω] : ResourceProfile ω κ →+ (κ →₀ ℕ) where
  toFun := usage
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def evalAddMonoidHom [AddCommMonoid ω] (weights : κ → ω) :
    ResourceProfile ω κ →+ ω where
  toFun := fun c ↦ c.eval weights
  map_zero' := by simp [eval]
  map_add' a b := by
    simp [eval, Finsupp.sum_add_index', add_assoc, add_left_comm, add_comm, add_nsmul]

@[simp] lemma intrinsic_sum [AddCommMonoid ω] {ι : Type*} (s : Finset ι)
    (f : ι → ResourceProfile ω κ) :
    (∑ a ∈ s, f a).intrinsic = ∑ a ∈ s, (f a).intrinsic := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [ha, ih]

@[simp] lemma usage_sum [AddCommMonoid ω] {ι : Type*} (s : Finset ι)
    (f : ι → ResourceProfile ω κ) :
    (∑ a ∈ s, f a).usage = ∑ a ∈ s, (f a).usage := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [ha, ih]

@[simp] lemma intrinsic_instantiate [AddCommMonoid ω]
    (c : ResourceProfile ω κ) (impl : κ → ResourceProfile ω κ') :
    (c.instantiate impl).intrinsic =
      c.intrinsic + c.usage.sum (fun k n ↦ n • (impl k).intrinsic) := by
  simp [instantiate, Finsupp.sum]

@[simp] lemma usage_instantiate [AddCommMonoid ω]
    (c : ResourceProfile ω κ) (impl : κ → ResourceProfile ω κ') :
    (c.instantiate impl).usage = c.usage.sum (fun k n ↦ n • (impl k).usage) := by
  simp [instantiate, Finsupp.sum]

@[simp] lemma eval_ofIntrinsic [AddCommMonoid ω] (w : ω) (weights : κ → ω) :
    (ofIntrinsic (κ := κ) w).eval weights = w := by
  simp [eval, ofIntrinsic]

@[simp] lemma eval_ofUsage [AddCommMonoid ω] (u : κ →₀ ℕ) (weights : κ → ω) :
    (ofUsage (ω := ω) u).eval weights = u.sum (fun k n ↦ n • weights k) := by
  rw [eval, ofUsage]
  simp

@[simp] lemma eval_single [AddCommMonoid ω] (k : κ) (n : ℕ) (weights : κ → ω) :
    (single (ω := ω) k n).eval weights = n • weights k := by
  rw [single, eval, ofUsage]
  rw [Finsupp.sum_single_index]
  · simp
  · simp

@[simp] lemma eval_zero [AddCommMonoid ω] (weights : κ → ω) :
    (0 : ResourceProfile ω κ).eval weights = 0 := by
  simp [eval]

@[simp] lemma eval_add [AddCommMonoid ω] (a b : ResourceProfile ω κ) (weights : κ → ω) :
    (a + b).eval weights = a.eval weights + b.eval weights := by
  exact (evalAddMonoidHom (ω := ω) (κ := κ) weights).map_add a b

@[simp] lemma eval_nsmul [AddCommMonoid ω] (n : ℕ) (a : ResourceProfile ω κ) (weights : κ → ω) :
    (n • a).eval weights = n • a.eval weights := by
  exact map_nsmul (evalAddMonoidHom (ω := ω) (κ := κ) weights) n a

@[simp] lemma eval_sum [AddCommMonoid ω] {ι : Type*} (s : Finset ι)
    (f : ι → ResourceProfile ω κ) (weights : κ → ω) :
    (∑ a ∈ s, f a).eval weights = ∑ a ∈ s, (f a).eval weights := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [ha, ih, eval_add]

@[simp] lemma instantiate_ofIntrinsic [AddCommMonoid ω]
    (w : ω) (impl : κ → ResourceProfile ω κ') :
    (ofIntrinsic (κ := κ) w).instantiate impl = ofIntrinsic (κ := κ') w := by
  simp [instantiate, ofIntrinsic]

@[simp] lemma instantiate_ofUsage [AddCommMonoid ω]
    (u : κ →₀ ℕ) (impl : κ → ResourceProfile ω κ') :
    (ofUsage (ω := ω) u).instantiate impl = u.sum (fun k n ↦ n • impl k) := by
  rw [instantiate, ofUsage, ofIntrinsic_zero]
  simp

@[simp] lemma instantiate_single [AddCommMonoid ω]
    (k : κ) (n : ℕ) (impl : κ → ResourceProfile ω κ') :
    (single (ω := ω) k n).instantiate impl = n • impl k := by
  rw [single, instantiate_ofUsage]
  rw [Finsupp.sum_single_index]
  · simp

noncomputable def instantiateAddMonoidHom [AddCommMonoid ω]
    (impl : κ → ResourceProfile ω κ') :
    ResourceProfile ω κ →+ ResourceProfile ω κ' where
  toFun := fun c ↦ c.instantiate impl
  map_zero' := by simp [instantiate]
  map_add' a b := by
    ext <;> simp [instantiate, Finsupp.sum_add_index', add_assoc, add_left_comm, add_comm,
      add_nsmul]

@[simp] lemma instantiate_add [AddCommMonoid ω]
    (a b : ResourceProfile ω κ) (impl : κ → ResourceProfile ω κ') :
    (a + b).instantiate impl = a.instantiate impl + b.instantiate impl := by
  exact (instantiateAddMonoidHom (ω := ω) impl).map_add a b

@[simp] lemma instantiate_nsmul [AddCommMonoid ω]
    (n : ℕ) (a : ResourceProfile ω κ) (impl : κ → ResourceProfile ω κ') :
    (n • a).instantiate impl = n • a.instantiate impl := by
  exact map_nsmul (instantiateAddMonoidHom (ω := ω) impl) n a

/-- Instantiating symbolic capabilities is associative.

Substituting `impl₁` into a profile `c`, and then substituting `impl₂` into the resulting
profile, is the same as substituting the composite implementation
`fun k ↦ (impl₁ k).instantiate impl₂` into `c` directly. -/
@[simp] lemma instantiate_assoc [AddCommMonoid ω]
    (c : ResourceProfile ω κ)
    (impl₁ : κ → ResourceProfile ω κ')
    (impl₂ : κ' → ResourceProfile ω κ'') :
    (c.instantiate impl₁).instantiate impl₂ =
      c.instantiate (fun k ↦ (impl₁ k).instantiate impl₂) := by
  have hu :
      ∀ u : κ →₀ ℕ,
        ((ofUsage (ω := ω) u).instantiate impl₁).instantiate impl₂ =
          (ofUsage (ω := ω) u).instantiate (fun k ↦ (impl₁ k).instantiate impl₂) := by
    intro u
    induction u using Finsupp.induction with
    | zero =>
        simp [instantiate]
    | @single_add a n u ha hn ih =>
        have ihu :
            (u.sum fun k n ↦ n • impl₁ k).instantiate impl₂ =
              u.sum fun k n ↦ n • (impl₁ k).instantiate impl₂ := by
          simpa [instantiate_ofUsage] using ih
        rw [instantiate_ofUsage, instantiate_ofUsage]
        rw [Finsupp.sum_add_index' (h_zero := fun _ ↦ by simp)
          (h_add := fun _ _ _ ↦ by simp [add_nsmul])]
        rw [Finsupp.sum_add_index' (h_zero := fun _ ↦ by simp)
          (h_add := fun _ _ _ ↦ by simp [add_nsmul])]
        rw [instantiate_add, Finsupp.sum_single_index, instantiate_nsmul, Finsupp.sum_single_index]
        · exact congrArg (fun t ↦ n • (impl₁ a).instantiate impl₂ + t) ihu
        · simp
        · simp
  have hc : c = ofIntrinsic (κ := κ) c.intrinsic + ofUsage (ω := ω) c.usage := by
    ext <;> simp [ofUsage]
  rw [hc, instantiate_add, instantiate_ofIntrinsic, instantiate_add, instantiate_ofIntrinsic,
    instantiate_add, instantiate_ofIntrinsic]
  exact congrArg (fun t ↦ ofIntrinsic (κ := κ'') c.intrinsic + t) (hu c.usage)

/-- Evaluating a purely intrinsic profile after instantiation leaves the intrinsic cost
unchanged. -/
@[simp] lemma eval_instantiate_ofIntrinsic [AddCommMonoid ω]
    (w : ω) (impl : κ → ResourceProfile ω κ') (weights : κ' → ω) :
    ((ofIntrinsic (κ := κ) w).instantiate impl).eval weights =
      (ofIntrinsic (κ := κ) w).eval (fun k => (impl k).eval weights) := by
  simp

/-- Evaluating a purely symbolic usage profile after instantiation amounts to evaluating each
capability implementation and summing the resulting scalar costs. -/
@[simp] lemma eval_instantiate_ofUsage [AddCommMonoid ω]
    (u : κ →₀ ℕ) (impl : κ → ResourceProfile ω κ') (weights : κ' → ω) :
    ((ofUsage (ω := ω) u).instantiate impl).eval weights =
      (ofUsage (ω := ω) u).eval (fun k => (impl k).eval weights) := by
  rw [instantiate_ofUsage, Finsupp.sum, eval_sum, eval_ofUsage, Finsupp.sum]
  simp [eval_nsmul]

/-- Evaluating a resource profile after instantiating its symbolic capabilities is the same as
evaluating the outer profile against the scalar costs induced by the implementations. -/
@[simp] lemma eval_instantiate [AddCommMonoid ω]
    (c : ResourceProfile ω κ)
    (impl : κ → ResourceProfile ω κ')
    (weights : κ' → ω) :
    (c.instantiate impl).eval weights =
      c.eval (fun k => (impl k).eval weights) := by
  have hc : c = ofIntrinsic (κ := κ) c.intrinsic + ofUsage (ω := ω) c.usage := by
    ext <;> simp [ofUsage]
  rw [hc, instantiate_add, eval_add, eval_instantiate_ofIntrinsic, eval_instantiate_ofUsage,
    eval_add]

end ResourceProfile
