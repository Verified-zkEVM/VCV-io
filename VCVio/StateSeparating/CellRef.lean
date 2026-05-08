/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ToMathlib.Data.Heap
import VCVio.EvalDist.Defs.Instances
import VCVio.OracleComp.ProbComp
import VCVio.OracleComp.SimSemantics.QueryImpl.Constructions

/-!
# State-separating cell references

`Heap Ident` stores typed cells at stable identifiers. `CellRef Ident` packages
one identifier as a typed reference, so heap programs can say explicitly which
cell they read or write.

The main purpose of this file is frame reasoning. A program that writes only a
known footprint preserves every cell outside that footprint, and the same idea
lifts from deterministic state programs to support-based effectful programs and
to oracle handlers interpreted by `simulateQ`.

The file is organized around four small layers:

* typed references and state operations;
* support-based preservation and write footprints;
* deterministic specializations for `StateT (Heap Ident) Id`;
* handler-level footprints for `QueryImpl`.
-/

universe u v uι u₀

namespace VCVio.StateSeparating

variable {Ident : Type u} [CellSpec.{u, max u v} Ident]

/-! ## Cell references -/

/-- A capability naming one typed cell in a `Heap Ident`. The value type of
the reference is dependent: `r.Value = CellSpec.type r.id`. -/
structure CellRef (Ident : Type u) [CellSpec.{u, max u v} Ident] where
  /-- The underlying heap cell identifier. -/
  id : Ident

namespace CellRef

/-- The value type stored at a cell reference. -/
abbrev Value (r : CellRef Ident) : Type (max u v) := CellSpec.type r.id

/-- Read a referenced cell from a heap. -/
@[reducible]
def get (r : CellRef Ident) (h : Heap Ident) : r.Value := h.get r.id

/-- Write a referenced cell in a heap. -/
def set [DecidableEq Ident] (r : CellRef Ident) (h : Heap Ident) (x : r.Value) : Heap Ident :=
  h.update r.id x

@[simp]
theorem get_set_self [DecidableEq Ident] (r : CellRef Ident) (h : Heap Ident) (x : r.Value) :
    r.get (r.set h x) = x :=
  Heap.get_update_self h r.id x

@[simp]
theorem get_set_of_ne [DecidableEq Ident] (r s : CellRef Ident) (h : Heap Ident) (x : r.Value)
    (hne : s.id ≠ r.id) :
    s.get (r.set h x) = s.get h :=
  Heap.get_update_of_ne hne x

/-! ## Deterministic state operations -/

/-- Deterministically read a referenced cell. -/
def read (r : CellRef Ident) : StateT (Heap Ident) Id r.Value :=
  StateT.mk fun h => (r.get h, h)

/-- Deterministically write a referenced cell. -/
def write [DecidableEq Ident] (r : CellRef Ident) (x : r.Value) :
    StateT (Heap Ident) Id PUnit :=
  StateT.mk fun h => (PUnit.unit, r.set h x)

@[simp]
theorem read_run (r : CellRef Ident) (h : Heap Ident) :
    r.read.run h = (r.get h, h) :=
  rfl

@[simp]
theorem write_run [DecidableEq Ident] (r : CellRef Ident) (h : Heap Ident) (x : r.Value) :
    (r.write x).run h = (PUnit.unit, r.set h x) :=
  rfl

/-! ## Effectful state operations -/

/-- Effectfully read a referenced cell. This is the monadic version of
`CellRef.read`: it works in any ambient monad, not just `Id`. -/
def readM (r : CellRef Ident) {m : Type (max u v) → Type*} [Monad m] :
    StateT (Heap Ident) m r.Value :=
  StateT.mk fun h => pure (r.get h, h)

/-- Effectfully write a referenced cell. This is the monadic version of
`CellRef.write`: it updates only the selected heap cell and performs no other
ambient effects. -/
def writeM [DecidableEq Ident] (r : CellRef Ident) (x : r.Value)
    {m : Type (max u v) → Type*} [Monad m] :
    StateT (Heap Ident) m PUnit :=
  StateT.mk fun h => pure (PUnit.unit, r.set h x)

@[simp]
theorem readM_run (r : CellRef Ident) {m : Type (max u v) → Type*} [Monad m]
    (h : Heap Ident) :
    (r.readM : StateT (Heap Ident) m r.Value).run h = pure (r.get h, h) :=
  rfl

@[simp]
theorem writeM_run [DecidableEq Ident] (r : CellRef Ident) (x : r.Value)
    {m : Type (max u v) → Type*} [Monad m] (h : Heap Ident) :
    (r.writeM x : StateT (Heap Ident) m PUnit).run h =
      pure (PUnit.unit, r.set h x) :=
  rfl

/-! ## Support-based frame predicates -/

/-- An effectful heap program preserves a cell reference when every
support-reachable final heap has the same value at that reference as the
initial heap. This is the right generalization of `Preserves` beyond `Id`:
for probabilistic/oracle computations there may be many possible final states. -/
def SupportPreserves {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    {α : Type (max u v)} (c : StateT (Heap Ident) m α) (r : CellRef Ident) : Prop :=
  ∀ h z, z ∈ support (c.run h) → r.get z.2 = r.get h

/-- An effectful heap program writes only a set of identifiers when every cell
outside the set is support-preserved. -/
def SupportWritesOnly {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    {α : Type (max u v)} (c : StateT (Heap Ident) m α) (writes : Set Ident) : Prop :=
  ∀ r : CellRef Ident, r.id ∉ writes → SupportPreserves c r

theorem supportWritesOnly_mono {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    {α : Type (max u v)} {c : StateT (Heap Ident) m α} {writes₁ writes₂ : Set Ident}
    (hc : SupportWritesOnly c writes₁) (hsubset : writes₁ ⊆ writes₂) :
    SupportWritesOnly c writes₂ := by
  intro r hr
  exact hc r (fun hmem => hr (hsubset hmem))

theorem supportPreserves_pure {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    {α : Type (max u v)} (x : α) (r : CellRef Ident) :
    SupportPreserves (pure x : StateT (Heap Ident) m α) r := by
  intro h z hz
  have hz_eq : z = (x, h) := by
    simpa using (mem_support_pure_iff z (x, h)).1 hz
  simp [hz_eq]

theorem supportWritesOnly_pure_empty {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    {α : Type (max u v)} (x : α) :
    SupportWritesOnly (pure x : StateT (Heap Ident) m α) (∅ : Set Ident) := by
  intro r hr
  exact supportPreserves_pure x r

theorem supportPreserves_readM {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    (r s : CellRef Ident) :
    SupportPreserves (r.readM : StateT (Heap Ident) m r.Value) s := by
  intro h z hz
  have hz_eq : z = (r.get h, h) := by
    simpa using (mem_support_pure_iff z (r.get h, h)).1 hz
  simp [hz_eq]

theorem readM_supportWritesOnly_empty {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    (r : CellRef Ident) :
    SupportWritesOnly (r.readM : StateT (Heap Ident) m r.Value) (∅ : Set Ident) := by
  intro s hs
  exact supportPreserves_readM r s

theorem supportPreserves_bind {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    {α β : Type (max u v)} {c : StateT (Heap Ident) m α}
    {k : α → StateT (Heap Ident) m β} {r : CellRef Ident}
    (hc : SupportPreserves c r) (hk : ∀ a, SupportPreserves (k a) r) :
    SupportPreserves (c >>= k) r := by
  intro h z hz
  have hz' :
      z ∈ support ((c.run h) >>= fun us => (k us.1).run us.2) := by
    simpa [StateT.run_bind] using hz
  rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hzcont⟩
  exact (hk us.1 us.2 z hzcont).trans (hc h us hus)

theorem writeM_supportWritesOnly_single [DecidableEq Ident]
    {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    (r : CellRef Ident) (x : r.Value) :
    SupportWritesOnly
      (r.writeM x : StateT (Heap Ident) m PUnit) ({r.id} : Set Ident) := by
  intro s hs h z hz
  have hz_eq : z = (PUnit.unit, r.set h x) := by
    simpa using (mem_support_pure_iff z (PUnit.unit, r.set h x)).1 hz
  simpa [hz_eq] using get_set_of_ne r s h x (by
    intro heq
    exact hs (by
      change s.id = r.id
      exact heq))

theorem supportWritesOnly_bind {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    {α β : Type (max u v)} {c : StateT (Heap Ident) m α}
    {k : α → StateT (Heap Ident) m β} {writes₁ writes₂ : Set Ident}
    (hc : SupportWritesOnly c writes₁) (hk : ∀ a, SupportWritesOnly (k a) writes₂) :
    SupportWritesOnly (c >>= k) (writes₁ ∪ writes₂) := by
  intro r hr
  exact supportPreserves_bind (hc r (fun hmem => hr (Or.inl hmem)))
    (fun a => hk a r (fun hmem => hr (Or.inr hmem)))

/-- Dependent effectful bind form: the continuation's write set may depend on
the first result. -/
theorem supportWritesOnly_bind_dep {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    {α β : Type (max u v)} {c : StateT (Heap Ident) m α}
    {k : α → StateT (Heap Ident) m β} {writes₁ : Set Ident}
    {writes₂ : α → Set Ident}
    (hc : SupportWritesOnly c writes₁) (hk : ∀ a, SupportWritesOnly (k a) (writes₂ a)) :
    SupportWritesOnly (c >>= k) (writes₁ ∪ {i | ∃ a, i ∈ writes₂ a}) := by
  intro r hr
  exact supportPreserves_bind (hc r (fun hmem => hr (Or.inl hmem)))
    (fun a => hk a r (fun hmem => hr (Or.inr ⟨a, hmem⟩)))

/-- A support-based write footprint packages a program with the set of cells it
may write and the proof that every other cell is preserved. -/
structure SupportWriteFootprint {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    {α : Type (max u v)} (c : StateT (Heap Ident) m α) where
  /-- Cells that the effectful program may write. -/
  writes : Set Ident
  /-- Soundness: every cell outside `writes` is support-framed through. -/
  sound : SupportWritesOnly c writes

namespace SupportWriteFootprint

variable {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
variable {α β : Type (max u v)}

theorem preserves {c : StateT (Heap Ident) m α} (footprint : SupportWriteFootprint c)
    (r : CellRef Ident) (hr : r.id ∉ footprint.writes) :
    SupportPreserves c r :=
  footprint.sound r hr

def pure (x : α) : SupportWriteFootprint (pure x : StateT (Heap Ident) m α) where
  writes := ∅
  sound := supportWritesOnly_pure_empty x

def readM (r : CellRef Ident) :
    SupportWriteFootprint (r.readM : StateT (Heap Ident) m r.Value) where
  writes := ∅
  sound := readM_supportWritesOnly_empty r

def writeM [DecidableEq Ident] (r : CellRef Ident) (x : r.Value) :
    SupportWriteFootprint (r.writeM x : StateT (Heap Ident) m PUnit) where
  writes := {r.id}
  sound := writeM_supportWritesOnly_single r x

def bind {c : StateT (Heap Ident) m α} {k : α → StateT (Heap Ident) m β}
    (footprint : SupportWriteFootprint c) (kont : ∀ a, SupportWriteFootprint (k a)) :
    SupportWriteFootprint (c >>= k) where
  writes := footprint.writes ∪ {i | ∃ a, i ∈ (kont a).writes}
  sound := supportWritesOnly_bind_dep footprint.sound (fun a => (kont a).sound)

end SupportWriteFootprint

/-! ## Probability corollaries for cell frames -/

namespace SupportPreserves

variable {m : Type (max u v) → Type*} [Monad m] [HasEvalSPMF m]
variable {α : Type (max u v)} {c : StateT (Heap Ident) m α} {r : CellRef Ident}

/-- A support-level frame implies that the cell-change event has probability
zero. This is the probability-facing corollary most proofs want after a
generic frame theorem has done the support-level work. -/
theorem prob_changed_eq_zero (hc : SupportPreserves c r) (h : Heap Ident) :
    Pr[ fun z => r.get z.2 ≠ r.get h | c.run h] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro z hz hchange
  exact hchange (hc h z hz)

/-- If a cell is support-preserved, then the probability of reading the
initial value at the end is exactly one minus the failure probability. -/
theorem prob_unchanged_eq_sub_probFailure (hc : SupportPreserves c r) (h : Heap Ident) :
    Pr[ fun z => r.get z.2 = r.get h | c.run h] = 1 - Pr[⊥ | c.run h] := by
  calc
    Pr[ fun z => r.get z.2 = r.get h | c.run h]
        = Pr[ fun _ => True | c.run h] := by
          refine probEvent_ext ?_
          intro z hz
          exact ⟨fun _ => True.intro, fun _ => hc h z hz⟩
    _ = 1 - Pr[⊥ | c.run h] := probEvent_True_eq_sub (c.run h)

/-- Failure-free specialization of `prob_unchanged_eq_sub_probFailure`. -/
theorem prob_unchanged_eq_one_of_probFailure_eq_zero (hc : SupportPreserves c r)
    (h : Heap Ident) (hnf : Pr[⊥ | c.run h] = 0) :
    Pr[ fun z => r.get z.2 = r.get h | c.run h] = 1 := by
  simp [prob_unchanged_eq_sub_probFailure hc h, hnf]

/-- If the ambient monad has total probability semantics, support preservation
gives probability-one preservation directly. -/
theorem prob_unchanged_eq_one {m : Type (max u v) → Type*} [Monad m] [HasEvalPMF m]
    {α : Type (max u v)} {c : StateT (Heap Ident) m α} {r : CellRef Ident}
    (hc : SupportPreserves c r) (h : Heap Ident) :
    Pr[ fun z => r.get z.2 = r.get h | c.run h] = 1 :=
  prob_unchanged_eq_one_of_probFailure_eq_zero hc h (HasEvalPMF.probFailure_eq_zero (c.run h))

/-- If the initial cell value is not `x`, then a support-preserved cell has
final value `x` with probability zero. -/
theorem prob_final_eq_eq_zero_of_ne (hc : SupportPreserves c r) (h : Heap Ident)
    {x : r.Value} (hne : x ≠ r.get h) :
    Pr[ fun z => r.get z.2 = x | c.run h] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro z hz hzval
  exact hne (hzval.symm.trans (hc h z hz))

end SupportPreserves

namespace SupportWritesOnly

variable {m : Type (max u v) → Type*} [Monad m] [HasEvalSPMF m]
variable {α : Type (max u v)} {c : StateT (Heap Ident) m α} {writes : Set Ident}

theorem prob_changed_eq_zero (hc : SupportWritesOnly c writes)
    (r : CellRef Ident) (hr : r.id ∉ writes) (h : Heap Ident) :
    Pr[ fun z => r.get z.2 ≠ r.get h | c.run h] = 0 :=
  SupportPreserves.prob_changed_eq_zero (hc r hr) h

theorem prob_unchanged_eq_sub_probFailure (hc : SupportWritesOnly c writes)
    (r : CellRef Ident) (hr : r.id ∉ writes) (h : Heap Ident) :
    Pr[ fun z => r.get z.2 = r.get h | c.run h] = 1 - Pr[⊥ | c.run h] :=
  SupportPreserves.prob_unchanged_eq_sub_probFailure (hc r hr) h

theorem prob_final_eq_eq_zero_of_ne (hc : SupportWritesOnly c writes)
    (r : CellRef Ident) (hr : r.id ∉ writes) (h : Heap Ident)
    {x : r.Value} (hne : x ≠ r.get h) :
    Pr[ fun z => r.get z.2 = x | c.run h] = 0 :=
  SupportPreserves.prob_final_eq_eq_zero_of_ne (hc r hr) h hne

end SupportWritesOnly

/-! ## Preservation except an event -/

/-- A computation preserves a cell except on an event when every
support-reachable outcome outside that event has the initial cell value. The
event may depend on the initial heap. -/
def SupportPreservesExcept {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    {α : Type (max u v)} (c : StateT (Heap Ident) m α) (r : CellRef Ident)
    (event : Heap Ident → α × Heap Ident → Prop) : Prop :=
  ∀ h z, z ∈ support (c.run h) → ¬ event h z → r.get z.2 = r.get h

namespace SupportPreservesExcept

section support

variable {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
variable {α : Type (max u v)} {c : StateT (Heap Ident) m α} {r : CellRef Ident}
variable {event : Heap Ident → α × Heap Ident → Prop}

theorem of_supportPreserves (hc : SupportPreserves c r) :
    SupportPreservesExcept c r event := by
  intro h z hz hevent
  exact hc h z hz

theorem mono_event (hc : SupportPreservesExcept c r event)
    {event' : Heap Ident → α × Heap Ident → Prop}
    (hsubset : ∀ h z, event h z → event' h z) :
    SupportPreservesExcept c r event' := by
  intro h z hz hnot
  exact hc h z hz (fun hevent => hnot (hsubset h z hevent))

theorem supportPreserves_of_false_event
    (hc : SupportPreservesExcept c r (fun _ _ => False)) :
    SupportPreserves c r := by
  intro h z hz
  exact hc h z hz (by simp)

end support

section probability

variable {m : Type (max u v) → Type*} [Monad m] [HasEvalSPMF m]
variable {α : Type (max u v)} {c : StateT (Heap Ident) m α} {r : CellRef Ident}
variable {event : Heap Ident → α × Heap Ident → Prop}

/-- If a cell can change only when `event` occurs, then the change probability
is bounded by the event probability. -/
theorem prob_changed_le_prob_event (hc : SupportPreservesExcept c r event)
    (h : Heap Ident) :
    Pr[ fun z => r.get z.2 ≠ r.get h | c.run h] ≤
      Pr[ fun z => event h z | c.run h] := by
  exact probEvent_mono (fun z hz hchange => by
    by_contra hevent
    exact hchange (hc h z hz hevent))

theorem prob_changed_eq_zero_of_prob_event_eq_zero
    (hc : SupportPreservesExcept c r event) (h : Heap Ident)
    (hevent : Pr[ fun z => event h z | c.run h] = 0) :
    Pr[ fun z => r.get z.2 ≠ r.get h | c.run h] = 0 := by
  exact le_antisymm ((prob_changed_le_prob_event hc h).trans (le_of_eq hevent)) (zero_le _)

theorem prob_changed_le_of_prob_event_le
    (hc : SupportPreservesExcept c r event) (h : Heap Ident) {ε : ENNReal}
    (hevent : Pr[ fun z => event h z | c.run h] ≤ ε) :
    Pr[ fun z => r.get z.2 ≠ r.get h | c.run h] ≤ ε :=
  (prob_changed_le_prob_event hc h).trans hevent

end probability

end SupportPreservesExcept

/-! ## Relational and measured cell effects -/

/-- A support-level relation between the initial and final value of one cell.
This is the general qualitative layer underneath preservation (`rel := Eq`) and
monotonicity/growth assertions. -/
def SupportCellRel {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    {α : Type (max u v)} (c : StateT (Heap Ident) m α) (r : CellRef Ident)
    (rel : r.Value → r.Value → Prop) : Prop :=
  ∀ h z, z ∈ support (c.run h) → rel (r.get h) (r.get z.2)

namespace SupportCellRel

section support

variable {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
variable {α β : Type (max u v)} {c : StateT (Heap Ident) m α}
variable {k : α → StateT (Heap Ident) m β} {r : CellRef Ident}
variable {rel : r.Value → r.Value → Prop}

theorem of_supportPreserves (hc : SupportPreserves c r) :
    SupportCellRel c r Eq := by
  intro h z hz
  exact (hc h z hz).symm

theorem supportPreserves_of_eq (hc : SupportCellRel c r Eq) :
    SupportPreserves c r := by
  intro h z hz
  exact (hc h z hz).symm

theorem bind (hc : SupportCellRel c r rel)
    (hk : ∀ a, SupportCellRel (k a) r rel)
    (htrans : ∀ x y z, rel x y → rel y z → rel x z) :
    SupportCellRel (c >>= k) r rel := by
  intro h z hz
  have hz' :
      z ∈ support ((c.run h) >>= fun us => (k us.1).run us.2) := by
    simpa [StateT.run_bind] using hz
  rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hzcont⟩
  exact htrans (r.get h) (r.get us.2) (r.get z.2)
    (hc h us hus) (hk us.1 us.2 z hzcont)

end support

section probability

variable {m : Type (max u v) → Type*} [Monad m] [HasEvalSPMF m]
variable {α : Type (max u v)} {c : StateT (Heap Ident) m α} {r : CellRef Ident}
variable {rel : r.Value → r.Value → Prop}

/-- A support-level cell relation makes violations of the relation a
probability-zero event. -/
theorem prob_violate_eq_zero (hc : SupportCellRel c r rel) (h : Heap Ident) :
    Pr[ fun z => ¬ rel (r.get h) (r.get z.2) | c.run h] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro z hz hviol
  exact hviol (hc h z hz)

end probability

end SupportCellRel

/-- A measured cell bound says a numeric measure of a cell can increase by at
most `δ` on every support-reachable execution path. Binds compose by adding
their deltas. -/
def SupportMeasureBound {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
    {α : Type (max u v)} (c : StateT (Heap Ident) m α) (r : CellRef Ident)
    (measure : r.Value → Nat) (δ : Nat) : Prop :=
  ∀ h z, z ∈ support (c.run h) → measure (r.get z.2) ≤ measure (r.get h) + δ

namespace SupportMeasureBound

section support

variable {m : Type (max u v) → Type*} [Monad m] [HasEvalSet m]
variable {α β : Type (max u v)} {c : StateT (Heap Ident) m α}
variable {k : α → StateT (Heap Ident) m β} {r : CellRef Ident}
variable {measure : r.Value → Nat}

theorem of_supportPreserves (hc : SupportPreserves c r) :
    SupportMeasureBound c r measure 0 := by
  intro h z hz
  simp [hc h z hz]

theorem mono_delta {δ₁ δ₂ : Nat} (hc : SupportMeasureBound c r measure δ₁)
    (hle : δ₁ ≤ δ₂) :
    SupportMeasureBound c r measure δ₂ := by
  intro h z hz
  exact (hc h z hz).trans (Nat.add_le_add_left hle (measure (r.get h)))

theorem bind {δ₁ δ₂ : Nat} (hc : SupportMeasureBound c r measure δ₁)
    (hk : ∀ a, SupportMeasureBound (k a) r measure δ₂) :
    SupportMeasureBound (c >>= k) r measure (δ₁ + δ₂) := by
  intro h z hz
  have hz' :
      z ∈ support ((c.run h) >>= fun us => (k us.1).run us.2) := by
    simpa [StateT.run_bind] using hz
  rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hzcont⟩
  exact (hk us.1 us.2 z hzcont).trans (by
    simpa [Nat.add_assoc] using
      Nat.add_le_add_right (hc h us hus) δ₂)

end support

section probability

variable {m : Type (max u v) → Type*} [Monad m] [HasEvalSPMF m]
variable {α : Type (max u v)} {c : StateT (Heap Ident) m α} {r : CellRef Ident}
variable {measure : r.Value → Nat} {δ : Nat}

/-- A measured support bound gives probability zero to exceeding the bound. -/
theorem prob_exceeds_eq_zero (hc : SupportMeasureBound c r measure δ)
    (h : Heap Ident) :
    Pr[ fun z => measure (r.get h) + δ < measure (r.get z.2) | c.run h] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro z hz hgt
  exact Nat.not_lt_of_ge (hc h z hz) hgt

end probability

end SupportMeasureBound

/-! ## Deterministic specialization -/

/-- A deterministic heap program preserves a cell reference when the final
heap has the same value at that reference as the initial heap.

This exact `Id`-specific predicate is equivalent to `SupportPreserves`, whose
support contains exactly the single deterministic output. The exact form keeps
deterministic examples pleasant to use, while the combinator proofs below are
derived from the generic support-based API. -/
def Preserves {α : Type (max u v)} (c : StateT (Heap Ident) Id α) (r : CellRef Ident) : Prop :=
  ∀ h, r.get (c.run h).2 = r.get h

/-- A deterministic heap program writes only a set of identifiers when every
cell outside the set is preserved. -/
def WritesOnly {α : Type (max u v)} (c : StateT (Heap Ident) Id α) (writes : Set Ident) : Prop :=
  ∀ r : CellRef Ident, r.id ∉ writes → Preserves c r

theorem supportPreserves_of_preserves {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {r : CellRef Ident} (hc : Preserves c r) :
    SupportPreserves c r := by
  intro h z hz
  have hz_eq : z = (c.run h).run := by
    simpa [Id.support_eq_singleton] using hz
  simpa [hz_eq] using hc h

theorem preserves_of_supportPreserves {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {r : CellRef Ident} (hc : SupportPreserves c r) :
    Preserves c r := by
  intro h
  exact hc h (c.run h).run (by simp [Id.support_eq_singleton])

/-- For the `Id` monad, support-based cell preservation is exactly the same as
the direct final-state equality predicate. -/
theorem supportPreserves_iff_preserves {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {r : CellRef Ident} :
    SupportPreserves c r ↔ Preserves c r :=
  ⟨preserves_of_supportPreserves, supportPreserves_of_preserves⟩

theorem supportWritesOnly_of_writesOnly {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {writes : Set Ident} (hc : WritesOnly c writes) :
    SupportWritesOnly c writes := by
  intro r hr
  exact supportPreserves_of_preserves (hc r hr)

theorem writesOnly_of_supportWritesOnly {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {writes : Set Ident} (hc : SupportWritesOnly c writes) :
    WritesOnly c writes := by
  intro r hr
  exact preserves_of_supportPreserves (hc r hr)

theorem supportWritesOnly_iff_writesOnly {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {writes : Set Ident} :
    SupportWritesOnly c writes ↔ WritesOnly c writes :=
  ⟨writesOnly_of_supportWritesOnly, supportWritesOnly_of_writesOnly⟩

theorem writesOnly_mono {α : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {writes₁ writes₂ : Set Ident} (hc : WritesOnly c writes₁)
    (hsubset : writes₁ ⊆ writes₂) :
    WritesOnly c writes₂ :=
  writesOnly_of_supportWritesOnly
    (supportWritesOnly_mono (supportWritesOnly_of_writesOnly hc) hsubset)

theorem preserves_pure {α : Type (max u v)} (x : α) (r : CellRef Ident) :
    Preserves (pure x : StateT (Heap Ident) Id α) r :=
  preserves_of_supportPreserves (supportPreserves_pure x r)

theorem preserves_read (r s : CellRef Ident) :
    Preserves (r.read) s := by
  refine preserves_of_supportPreserves ?_
  intro h z hz
  have hz_eq : z = (r.get h, h) := by
    simpa [read, Id.support_eq_singleton] using hz
  simp [hz_eq]

theorem read_writesOnly_empty (r : CellRef Ident) :
    WritesOnly (r.read) (∅ : Set Ident) := by
  intro s hs
  exact preserves_read r s

theorem preserves_bind {α β : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {k : α → StateT (Heap Ident) Id β} {r : CellRef Ident}
    (hc : Preserves c r) (hk : ∀ a, Preserves (k a) r) :
    Preserves (c >>= k) r :=
  preserves_of_supportPreserves
    (supportPreserves_bind (supportPreserves_of_preserves hc)
      (fun a => supportPreserves_of_preserves (hk a)))

theorem write_writesOnly_single [DecidableEq Ident] (r : CellRef Ident) (x : r.Value) :
    WritesOnly (r.write x) ({r.id} : Set Ident) := by
  refine writesOnly_of_supportWritesOnly ?_
  intro s hs h z hz
  have hz_eq : z = (PUnit.unit, r.set h x) := by
    simpa [write, Id.support_eq_singleton] using hz
  simpa [hz_eq] using get_set_of_ne r s h x (by
    intro heq
    exact hs (by
      change s.id = r.id
      exact heq))

theorem writesOnly_bind {α β : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {k : α → StateT (Heap Ident) Id β} {writes₁ writes₂ : Set Ident}
    (hc : WritesOnly c writes₁) (hk : ∀ a, WritesOnly (k a) writes₂) :
    WritesOnly (c >>= k) (writes₁ ∪ writes₂) :=
  writesOnly_of_supportWritesOnly
    (supportWritesOnly_bind (supportWritesOnly_of_writesOnly hc)
      (fun a => supportWritesOnly_of_writesOnly (hk a)))

/-- Dependent bind form: the continuation's write set may depend on the
first result. The resulting write set is the union of the first write set and
all possible continuation write sets. -/
theorem writesOnly_bind_dep {α β : Type (max u v)} {c : StateT (Heap Ident) Id α}
    {k : α → StateT (Heap Ident) Id β} {writes₁ : Set Ident}
    {writes₂ : α → Set Ident}
    (hc : WritesOnly c writes₁) (hk : ∀ a, WritesOnly (k a) (writes₂ a)) :
    WritesOnly (c >>= k) (writes₁ ∪ {i | ∃ a, i ∈ writes₂ a}) :=
  writesOnly_of_supportWritesOnly
    (supportWritesOnly_bind_dep (supportWritesOnly_of_writesOnly hc)
      (fun a => supportWritesOnly_of_writesOnly (hk a)))

/-! ## Read agreement and result-dependence footprints -/

/-- Two heaps agree on a set of cell identifiers when every reference whose
identifier is in the set reads the same value from both heaps. -/
def SameOn (cells : Set Ident) (h₁ h₂ : Heap Ident) : Prop :=
  ∀ r : CellRef Ident, r.id ∈ cells → r.get h₁ = r.get h₂

theorem sameOn_refl (cells : Set Ident) (h : Heap Ident) :
    SameOn cells h h := by
  intro r hr
  rfl

theorem sameOn_mono {cells₁ cells₂ : Set Ident} {h₁ h₂ : Heap Ident}
    (hsubset : cells₁ ⊆ cells₂) (hsame : SameOn cells₂ h₁ h₂) :
    SameOn cells₁ h₁ h₂ := by
  intro r hr
  exact hsame r (hsubset hr)

theorem sameOn_singleton_read {r : CellRef Ident} {h₁ h₂ : Heap Ident}
    (hsame : SameOn ({r.id} : Set Ident) h₁ h₂) :
    r.get h₁ = r.get h₂ :=
  hsame r rfl

/-- A deterministic heap program's result depends only on a set of cells when
heaps agreeing on those cells produce equal return values. This intentionally
tracks only the returned value, not the final heap. -/
def ResultDependsOnly {α : Type (max u v)} (c : StateT (Heap Ident) Id α)
    (reads : Set Ident) : Prop :=
  ∀ h₁ h₂, SameOn reads h₁ h₂ → (c.run h₁).1 = (c.run h₂).1

theorem resultDependsOnly_pure {α : Type (max u v)} (x : α) :
    ResultDependsOnly (pure x : StateT (Heap Ident) Id α) (∅ : Set Ident) := by
  intro h₁ h₂ hsame
  rfl

theorem resultDependsOnly_read (r : CellRef Ident) :
    ResultDependsOnly r.read ({r.id} : Set Ident) := by
  intro h₁ h₂ hsame
  exact sameOn_singleton_read hsame

theorem resultDependsOnly_write [DecidableEq Ident] (r : CellRef Ident) (x : r.Value) :
    ResultDependsOnly (r.write x) (∅ : Set Ident) := by
  intro h₁ h₂ hsame
  rfl

/-! ## Compositional write footprints -/

/-- A compositional write footprint packages a deterministic heap program with
the set of cells it may write and the proof that all other cells are
preserved. -/
structure WriteFootprint {α : Type (max u v)} (c : StateT (Heap Ident) Id α) where
  /-- Cells that the program may write. -/
  writes : Set Ident
  /-- Soundness: every cell outside `writes` is framed through. -/
  sound : WritesOnly c writes

namespace WriteFootprint

variable {α β : Type (max u v)}

theorem preserves {c : StateT (Heap Ident) Id α} (footprint : WriteFootprint c)
    (r : CellRef Ident) (hr : r.id ∉ footprint.writes) :
    Preserves c r :=
  footprint.sound r hr

def pure (x : α) : WriteFootprint (pure x : StateT (Heap Ident) Id α) where
  writes := ∅
  sound := by
    intro r hr
    exact preserves_pure x r

def read (r : CellRef Ident) : WriteFootprint r.read where
  writes := ∅
  sound := read_writesOnly_empty r

def write [DecidableEq Ident] (r : CellRef Ident) (x : r.Value) :
    WriteFootprint (r.write x) where
  writes := {r.id}
  sound := write_writesOnly_single r x

def bind {c : StateT (Heap Ident) Id α} {k : α → StateT (Heap Ident) Id β}
    (footprint : WriteFootprint c) (kont : ∀ a, WriteFootprint (k a)) :
    WriteFootprint (c >>= k) where
  writes := footprint.writes ∪ {i | ∃ a, i ∈ (kont a).writes}
  sound := writesOnly_bind_dep footprint.sound (fun a => (kont a).sound)

end WriteFootprint

end CellRef

/-! ## Query-implementation cell frames -/

noncomputable section

open OracleComp OracleSpec

namespace QueryImpl

variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]
variable {m : Type (max u₀ v) → Type*} [Monad m] [HasEvalSet m]

/-- A `QueryImpl` preserves a heap cell when each single query step leaves
that cell unchanged on every support-reachable post-state. This is the
support-level analogue of `CellRef.Preserves` for probabilistic handlers. -/
def PreservesCell (impl : QueryImpl spec (StateT (Heap Ident₀) m))
    (r : CellRef Ident₀) : Prop :=
  ∀ t h z, z ∈ support ((impl t).run h) → r.get z.2 = r.get h

/-- A `QueryImpl` writes only the cells named by a per-query footprint when
each query step support-preserves every cell outside its footprint. -/
def WritesOnlyCells (impl : QueryImpl spec (StateT (Heap Ident₀) m))
    (writes : spec.Domain → Set Ident₀) : Prop :=
  ∀ t, CellRef.SupportWritesOnly (impl t) (writes t)

theorem writesOnlyCells_mono {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    {writes₁ writes₂ : spec.Domain → Set Ident₀} (himpl : WritesOnlyCells impl writes₁)
    (hsubset : ∀ t, writes₁ t ⊆ writes₂ t) :
    WritesOnlyCells impl writes₂ := by
  intro t
  exact CellRef.supportWritesOnly_mono (himpl t) (hsubset t)

theorem preservesCell_of_writesOnlyCells
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    {writes : spec.Domain → Set Ident₀} {r : CellRef Ident₀}
    (himpl : WritesOnlyCells impl writes) (hr : ∀ t, r.id ∉ writes t) :
    PreservesCell impl r := by
  intro t h z hz
  exact himpl t r (hr t) h z hz

/-- A compositional cell-write footprint for a whole query implementation: every
domain element gets a set of cells it may write, plus a support-level proof
that no other cells change. -/
structure CellWriteFootprint (impl : QueryImpl spec (StateT (Heap Ident₀) m)) where
  /-- Per-query cells that may be written by the handler branch. -/
  writes : spec.Domain → Set Ident₀
  /-- Soundness of the footprint. -/
  sound : WritesOnlyCells impl writes

namespace CellWriteFootprint

theorem preservesCell {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    (footprint : CellWriteFootprint impl) (r : CellRef Ident₀)
    (hr : ∀ t, r.id ∉ footprint.writes t) :
    PreservesCell impl r :=
  preservesCell_of_writesOnlyCells footprint.sound hr

end CellWriteFootprint

end QueryImpl

namespace OracleComp

variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}
variable {α : Type (max u₀ v)}
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]
variable {m : Type (max u₀ v) → Type*} [Monad m] [LawfulMonad m] [HasEvalSet m]

/-- If every handler query preserves a cell, then interpreting any
`OracleComp` through that handler preserves the cell. -/
theorem simulateQ_run_cellPreserved
    (impl : QueryImpl spec (StateT (Heap Ident₀) m))
    (r : CellRef Ident₀) (himpl : QueryImpl.PreservesCell impl r)
    (A : OracleComp spec α) (h : Heap Ident₀) :
    ∀ z ∈ support ((simulateQ impl A).run h), r.get z.2 = r.get h := by
  revert h
  induction A using OracleComp.inductionOn with
  | pure a =>
      intro h z hz
      have hz_eq : z = (a, h) := by
        simpa using (mem_support_pure_iff z (a, h)).1 hz
      simp [hz_eq]
  | query_bind t oa ih =>
      intro h z hz
      have hz' :
          z ∈ support
            (((simulateQ impl
                  (OracleSpec.query t : OracleComp spec (spec.Range t))).run h) >>=
              fun us => (simulateQ impl (oa us.1)).run us.2) := by
        simpa [simulateQ_bind, OracleComp.liftM_def] using hz
      rcases (mem_support_bind_iff _ _ _).1 hz' with ⟨us, hus, hzcont⟩
      have hq_run :
          (simulateQ impl (OracleSpec.query t : OracleComp spec (spec.Range t))).run h =
            (impl t).run h := by
        have hq :
            simulateQ impl (OracleSpec.query t : OracleComp spec (spec.Range t)) =
              impl t := by
          simp [OracleSpec.query_def, simulateQ_query]
        simp [hq]
      have hus' : us ∈ support ((impl t).run h) := by
        simpa [hq_run] using hus
      exact (ih us.1 us.2 z hzcont).trans (himpl t h us hus')

end OracleComp

namespace QueryImpl

section probability

variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]
variable {m : Type (max u₀ v) → Type*} [Monad m] [HasEvalSPMF m]

theorem PreservesCell.prob_changed_eq_zero
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)} {r : CellRef Ident₀}
    (himpl : PreservesCell impl r) (t : spec.Domain) (h : Heap Ident₀) :
    Pr[ fun z => r.get z.2 ≠ r.get h | (impl t).run h] = 0 :=
  CellRef.SupportPreserves.prob_changed_eq_zero (himpl t) h

theorem PreservesCell.prob_unchanged_eq_sub_probFailure
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)} {r : CellRef Ident₀}
    (himpl : PreservesCell impl r) (t : spec.Domain) (h : Heap Ident₀) :
    Pr[ fun z => r.get z.2 = r.get h | (impl t).run h] =
      1 - Pr[⊥ | (impl t).run h] :=
  CellRef.SupportPreserves.prob_unchanged_eq_sub_probFailure (himpl t) h

theorem CellWriteFootprint.prob_changed_eq_zero
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    (footprint : CellWriteFootprint impl) (r : CellRef Ident₀)
    (hr : ∀ t, r.id ∉ footprint.writes t)
    (t : spec.Domain) (h : Heap Ident₀) :
    Pr[ fun z => r.get z.2 ≠ r.get h | (impl t).run h] = 0 :=
  (footprint.preservesCell r hr).prob_changed_eq_zero t h

theorem CellWriteFootprint.prob_unchanged_eq_sub_probFailure
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    (footprint : CellWriteFootprint impl) (r : CellRef Ident₀)
    (hr : ∀ t, r.id ∉ footprint.writes t)
    (t : spec.Domain) (h : Heap Ident₀) :
    Pr[ fun z => r.get z.2 = r.get h | (impl t).run h] =
      1 - Pr[⊥ | (impl t).run h] :=
  (footprint.preservesCell r hr).prob_unchanged_eq_sub_probFailure t h

end probability

end QueryImpl

namespace OracleComp

section probability

variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}
variable {α : Type (max u₀ v)}
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]
variable {m : Type (max u₀ v) → Type*} [Monad m] [LawfulMonad m] [HasEvalSPMF m]

theorem simulateQ_run_cellChange_prob_eq_zero
    (impl : QueryImpl spec (StateT (Heap Ident₀) m))
    (r : CellRef Ident₀) (himpl : QueryImpl.PreservesCell impl r)
    (A : OracleComp spec α) (h : Heap Ident₀) :
    Pr[ fun z => r.get z.2 ≠ r.get h | (simulateQ impl A).run h] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro z hz hchange
  exact hchange (simulateQ_run_cellPreserved impl r himpl A h z hz)

theorem simulateQ_run_cellUnchanged_prob_eq_sub_probFailure
    (impl : QueryImpl spec (StateT (Heap Ident₀) m))
    (r : CellRef Ident₀) (himpl : QueryImpl.PreservesCell impl r)
    (A : OracleComp spec α) (h : Heap Ident₀) :
    Pr[ fun z => r.get z.2 = r.get h | (simulateQ impl A).run h] =
      1 - Pr[⊥ | (simulateQ impl A).run h] := by
  have hpres : CellRef.SupportPreserves (simulateQ impl A) r := by
    intro h' z hz
    exact simulateQ_run_cellPreserved impl r himpl A h' z hz
  exact CellRef.SupportPreserves.prob_unchanged_eq_sub_probFailure hpres h

theorem simulateQ_run_cellUnchanged_prob_eq_one_of_probFailure_eq_zero
    (impl : QueryImpl spec (StateT (Heap Ident₀) m))
    (r : CellRef Ident₀) (himpl : QueryImpl.PreservesCell impl r)
    (A : OracleComp spec α) (h : Heap Ident₀)
    (hnf : Pr[⊥ | (simulateQ impl A).run h] = 0) :
    Pr[ fun z => r.get z.2 = r.get h | (simulateQ impl A).run h] = 1 := by
  simp [simulateQ_run_cellUnchanged_prob_eq_sub_probFailure impl r himpl A h, hnf]

end probability

section probability_total

variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}
variable {α : Type (max u₀ v)}
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]
variable {m : Type (max u₀ v) → Type*} [Monad m] [LawfulMonad m] [HasEvalPMF m]

theorem simulateQ_run_cellUnchanged_prob_eq_one
    (impl : QueryImpl spec (StateT (Heap Ident₀) m))
    (r : CellRef Ident₀) (himpl : QueryImpl.PreservesCell impl r)
    (A : OracleComp spec α) (h : Heap Ident₀) :
    Pr[ fun z => r.get z.2 = r.get h | (simulateQ impl A).run h] = 1 :=
  simulateQ_run_cellUnchanged_prob_eq_one_of_probFailure_eq_zero impl r himpl A h
    (HasEvalPMF.probFailure_eq_zero ((simulateQ impl A).run h))

end probability_total

end OracleComp

namespace QueryImpl

variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}
variable {α : Type (max u₀ v)}
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]
variable {m : Type (max u₀ v) → Type*} [Monad m] [LawfulMonad m] [HasEvalSet m]

/-- A query-implementation cell-write footprint lifts through interpretation: if a
cell is outside every per-query footprint, the interpreted computation
preserves that cell. -/
theorem CellWriteFootprint.simulateQ_run_cellPreserved
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    (footprint : CellWriteFootprint impl) (r : CellRef Ident₀)
    (hr : ∀ t, r.id ∉ footprint.writes t)
    (A : OracleComp spec α) (h : Heap Ident₀) :
    ∀ z ∈ support ((simulateQ impl A).run h), r.get z.2 = r.get h :=
  OracleComp.simulateQ_run_cellPreserved impl r (footprint.preservesCell r hr) A h

section probability

variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}
variable {α : Type (max u₀ v)}
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]
variable {m : Type (max u₀ v) → Type*} [Monad m] [LawfulMonad m] [HasEvalSPMF m]

theorem CellWriteFootprint.simulateQ_run_cellChange_prob_eq_zero
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    (footprint : CellWriteFootprint impl) (r : CellRef Ident₀)
    (hr : ∀ t, r.id ∉ footprint.writes t)
    (A : OracleComp spec α) (h : Heap Ident₀) :
    Pr[ fun z => r.get z.2 ≠ r.get h | (simulateQ impl A).run h] = 0 :=
  OracleComp.simulateQ_run_cellChange_prob_eq_zero impl r
    (footprint.preservesCell r hr) A h

theorem CellWriteFootprint.simulateQ_run_cellUnchanged_prob_eq_sub_probFailure
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    (footprint : CellWriteFootprint impl) (r : CellRef Ident₀)
    (hr : ∀ t, r.id ∉ footprint.writes t)
    (A : OracleComp spec α) (h : Heap Ident₀) :
    Pr[ fun z => r.get z.2 = r.get h | (simulateQ impl A).run h] =
      1 - Pr[⊥ | (simulateQ impl A).run h] :=
  OracleComp.simulateQ_run_cellUnchanged_prob_eq_sub_probFailure impl r
    (footprint.preservesCell r hr) A h

theorem CellWriteFootprint.simulateQ_run_cellUnchanged_prob_eq_one_of_probFailure_eq_zero
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    (footprint : CellWriteFootprint impl) (r : CellRef Ident₀)
    (hr : ∀ t, r.id ∉ footprint.writes t)
    (A : OracleComp spec α) (h : Heap Ident₀)
    (hnf : Pr[⊥ | (simulateQ impl A).run h] = 0) :
    Pr[ fun z => r.get z.2 = r.get h | (simulateQ impl A).run h] = 1 :=
  OracleComp.simulateQ_run_cellUnchanged_prob_eq_one_of_probFailure_eq_zero impl r
    (footprint.preservesCell r hr) A h hnf

end probability

section probability_total

variable {ι : Type uι} {spec : OracleSpec.{uι, max u₀ v} ι}
variable {α : Type (max u₀ v)}
variable {Ident₀ : Type u₀} [CellSpec.{u₀, max u₀ v} Ident₀]
variable {m : Type (max u₀ v) → Type*} [Monad m] [LawfulMonad m] [HasEvalPMF m]

theorem CellWriteFootprint.simulateQ_run_cellUnchanged_prob_eq_one
    {impl : QueryImpl spec (StateT (Heap Ident₀) m)}
    (footprint : CellWriteFootprint impl) (r : CellRef Ident₀)
    (hr : ∀ t, r.id ∉ footprint.writes t)
    (A : OracleComp spec α) (h : Heap Ident₀) :
    Pr[ fun z => r.get z.2 = r.get h | (simulateQ impl A).run h] = 1 :=
  OracleComp.simulateQ_run_cellUnchanged_prob_eq_one impl r
    (footprint.preservesCell r hr) A h

end probability_total

end QueryImpl

end

/-! ## Examples -/

namespace CellRefExample

/-- Three toy cells: a log counter, a cache counter, and an immutable flag. -/
inductive DemoCell where
  | log
  | cache
  | flag
  deriving DecidableEq

instance : CellSpec DemoCell where
  type
    | .log => Nat
    | .cache => Nat
    | .flag => Bool
  default
    | .log => 0
    | .cache => 0
    | .flag => false

@[reducible] def logRef : CellRef DemoCell := ⟨.log⟩
@[reducible] def cacheRef : CellRef DemoCell := ⟨.cache⟩
@[reducible] def flagRef : CellRef DemoCell := ⟨.flag⟩

/-! ### Query-handler write footprints -/

/-- A tiny external oracle interface for the support-based footprint demo. -/
inductive DemoQuery where
  | touchLog
  | touchCache
  | readFlag
  deriving DecidableEq

/-- Every demo query returns unit; the interesting part is the heap effect. -/
def demoSpec : OracleSpec.{0, 0} DemoQuery := fun _ => PUnit

/-- A toy probabilistic handler with heap effects. Two branches write cells,
and one branch reads the flag without modifying it. -/
def demoImpl : QueryImpl demoSpec (StateT (Heap DemoCell) ProbComp)
  | .touchLog => logRef.writeM 1
  | .touchCache => cacheRef.writeM 1
  | .readFlag => do
      let _ ← (flagRef.readM : StateT (Heap DemoCell) ProbComp Bool)
      pure PUnit.unit

/-- Per-query write footprint for `demoImpl`. -/
def demoWrites : DemoQuery → Set DemoCell
  | .touchLog => {DemoCell.log}
  | .touchCache => {DemoCell.cache}
  | .readFlag => ∅

/-- The handler writes only the cells declared by `demoWrites`. -/
theorem demoImpl_writesOnly :
    QueryImpl.WritesOnlyCells demoImpl demoWrites := by
  intro t
  cases t with
  | touchLog =>
      simpa [demoImpl, demoWrites, logRef] using
        (CellRef.writeM_supportWritesOnly_single logRef 1
          : CellRef.SupportWritesOnly
              (logRef.writeM 1 : StateT (Heap DemoCell) ProbComp PUnit) {DemoCell.log})
  | touchCache =>
      simpa [demoImpl, demoWrites, cacheRef] using
        (CellRef.writeM_supportWritesOnly_single cacheRef 1
          : CellRef.SupportWritesOnly
              (cacheRef.writeM 1 : StateT (Heap DemoCell) ProbComp PUnit) {DemoCell.cache})
  | readFlag =>
      have hbind :
          CellRef.SupportWritesOnly
            ((flagRef.readM : StateT (Heap DemoCell) ProbComp Bool) >>= fun _ =>
              pure PUnit.unit) (∅ ∪ ∅ : Set DemoCell) :=
        CellRef.supportWritesOnly_bind
          (CellRef.readM_supportWritesOnly_empty
            (m := ProbComp) flagRef)
          (fun _ => CellRef.supportWritesOnly_pure_empty
            (m := ProbComp) PUnit.unit)
      simpa [demoImpl, demoWrites] using hbind

/-- Pack the handler-level footprint once, so later proofs need not unfold
every query branch. -/
def demoFootprint : QueryImpl.CellWriteFootprint demoImpl where
  writes := demoWrites
  sound := demoImpl_writesOnly

/-- The flag is outside every branch footprint, so each handler step preserves
it. -/
theorem demoImpl_preserves_flag :
    QueryImpl.PreservesCell demoImpl flagRef :=
  demoFootprint.preservesCell flagRef (by
    intro t
    change DemoCell.flag ∉ demoWrites t
    cases t <;> simp [demoWrites])

/-- A tiny client computation that calls several branches of the demo handler. -/
def demoClient : OracleComp demoSpec PUnit := do
  let _ ← liftM (demoSpec.query DemoQuery.touchCache)
  let _ ← liftM (demoSpec.query DemoQuery.touchLog)
  liftM (demoSpec.query DemoQuery.readFlag)

/-- The handler footprint automatically lifts through `simulateQ`: the whole
interpreted computation preserves the flag, not just a single query branch. -/
theorem demoClient_preserves_flag (h : Heap DemoCell) :
    ∀ z ∈ support ((simulateQ demoImpl demoClient).run h),
      flagRef.get z.2 = flagRef.get h :=
  demoFootprint.simulateQ_run_cellPreserved flagRef (by
    intro t
    change DemoCell.flag ∉ demoWrites t
    cases t <;> simp [demoWrites]) demoClient h

/-- The previous theorem as a reusable support-preservation predicate. -/
theorem demoClient_supportPreserves_flag :
    CellRef.SupportPreserves (simulateQ demoImpl demoClient) flagRef := by
  intro h z hz
  exact demoClient_preserves_flag h z hz

/-- From the empty heap, the framed flag is never `true`. -/
theorem demoClient_prob_flag_true_eq_zero :
    Pr[ fun z => flagRef.get z.2 = true |
      (simulateQ demoImpl demoClient).run (Heap.empty : Heap DemoCell)] = 0 :=
  CellRef.SupportPreserves.prob_final_eq_eq_zero_of_ne
    demoClient_supportPreserves_flag (Heap.empty : Heap DemoCell) (by decide)

/-- Probability-one preservation for the framed flag. -/
theorem demoClient_prob_flag_unchanged_eq_one (h : Heap DemoCell) :
    Pr[ fun z => flagRef.get z.2 = flagRef.get h |
      (simulateQ demoImpl demoClient).run h] = 1 :=
  CellRef.SupportPreserves.prob_unchanged_eq_one demoClient_supportPreserves_flag h

/-- Increment the cache counter and append one log entry. The program never
writes `flagRef`. -/
def cacheAndLogStep : StateT (Heap DemoCell) Id PUnit := do
  let cache ← cacheRef.read
  let _ ← cacheRef.write (cache + 1)
  let log ← logRef.read
  logRef.write (log + 1)

/-- The step writes only `.cache` and `.log`. -/
theorem cacheAndLogStep_writesOnly :
    CellRef.WritesOnly cacheAndLogStep ({DemoCell.cache, DemoCell.log} : Set DemoCell) := by
  classical
  intro r hr h
  rcases r with ⟨id⟩
  cases id with
  | log =>
      exact False.elim (hr
        (show DemoCell.log = DemoCell.cache ∨ DemoCell.log = DemoCell.log from Or.inr rfl))
  | cache =>
      exact False.elim (hr
        (show DemoCell.cache = DemoCell.cache ∨ DemoCell.cache = DemoCell.log from
          Or.inl rfl))
  | flag =>
      change
        (((h.update DemoCell.cache (h.get DemoCell.cache + 1)).update
            DemoCell.log
            (((h.update DemoCell.cache (h.get DemoCell.cache + 1)).get
              DemoCell.log) + 1)).get DemoCell.flag =
          h.get DemoCell.flag)
      simp

/-- A compositional footprint for `cacheAndLogStep`. Reads contribute no writes,
writes contribute singleton footprints, and binds union the footprints. -/
def cacheAndLogFootprint :
    CellRef.WriteFootprint
      (cacheRef.read >>= fun cache =>
        cacheRef.write (cache + 1) >>= fun _ =>
          logRef.read >>= fun log =>
            logRef.write (log + 1)) where
  writes := {DemoCell.cache, DemoCell.log}
  sound := by
    intro r hr
    apply CellRef.preserves_bind
    · exact CellRef.preserves_read cacheRef r
    · intro cache
      apply CellRef.preserves_bind
      · exact (CellRef.write_writesOnly_single cacheRef (cache + 1)) r (by
          intro hmem
          exact hr (Or.inl hmem))
      · intro _
        apply CellRef.preserves_bind
        · exact CellRef.preserves_read logRef r
        · intro log
          exact (CellRef.write_writesOnly_single logRef (log + 1)) r (by
            intro hmem
            exact hr (Or.inr hmem))

/-- The compositional footprint gives flag preservation without unfolding each
state update in the final proof. -/
theorem cacheAndLogStep_preserves_flag_via_footprint :
    CellRef.Preserves cacheAndLogStep flagRef := by
  unfold cacheAndLogStep
  exact cacheAndLogFootprint.preserves flagRef (by
    intro h
    rcases h with h | h
    · cases h
    · cases h)

/-- A smaller example that uses the generic frame combinators directly: two
writes outside the flag cell preserve the flag. -/
def writeCacheThenLog : StateT (Heap DemoCell) Id PUnit := do
  let _ ← cacheRef.write 1
  logRef.write 1

theorem writeCacheThenLog_preserves_flag :
    CellRef.Preserves writeCacheThenLog flagRef := by
  unfold writeCacheThenLog
  apply CellRef.preserves_bind
  · exact (CellRef.write_writesOnly_single cacheRef 1) flagRef (by
      intro h
      cases h)
  · intro _
    exact (CellRef.write_writesOnly_single logRef 1) flagRef (by
      intro h
      cases h)

/-- A compositional footprint for the two-write program. The write set is
computed by `WriteFootprint.bind`: first `{cache}`, then `{log}`. -/
def writeCacheThenLogFootprint :
    CellRef.WriteFootprint (cacheRef.write 1 >>= fun _ => logRef.write 1) :=
  (CellRef.WriteFootprint.write cacheRef 1).bind fun _ =>
    CellRef.WriteFootprint.write logRef 1

/-- Once the footprint says the write set is `{cache, log}`, flag preservation
is a one-line frame application plus a membership proof. -/
theorem writeCacheThenLog_preserves_flag_via_footprint :
    CellRef.Preserves writeCacheThenLog flagRef := by
  unfold writeCacheThenLog
  exact writeCacheThenLogFootprint.preserves flagRef (by
    intro h
    rcases h with h | ⟨_, h⟩
    · cases h
    · cases h)

/-- Reads have a separate result-dependence footprint: reading `cacheRef`
depends only on the cache cell. -/
example {h₁ h₂ : Heap DemoCell}
    (hsame : CellRef.SameOn ({DemoCell.cache} : Set DemoCell) h₁ h₂) :
    (cacheRef.read.run h₁).1 = (cacheRef.read.run h₂).1 :=
  CellRef.resultDependsOnly_read cacheRef h₁ h₂ hsame

/-- As a corollary, `flagRef` is preserved by `cacheAndLogStep`. -/
theorem cacheAndLogStep_preserves_flag :
    CellRef.Preserves cacheAndLogStep flagRef := by
  exact cacheAndLogStep_writesOnly flagRef (by
    intro h
    cases h with
    | inl hflag => cases hflag
    | inr hflag => cases hflag)

example (h : Heap DemoCell) :
    flagRef.get (cacheAndLogStep.run h).2 = flagRef.get h :=
  cacheAndLogStep_preserves_flag h

example :
    flagRef.get (cacheAndLogStep.run (Heap.empty : Heap DemoCell)).2 = false := by
  rw [cacheAndLogStep_preserves_flag]
  rfl

end CellRefExample

end VCVio.StateSeparating
