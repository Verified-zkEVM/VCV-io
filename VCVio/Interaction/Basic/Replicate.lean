/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Append
import ToMathlib.PFunctor.Free.Replicate

/-!
# `Spec.replicate` and transcript operations

Non-dependent `n`-fold append of the same spec, with `Transcript.replicateJoin` / `replicateSplit`,
replicated decorations/refinements, and `Strategy.iterate`. This is the uniform special case of
`Spec.stateChain` (see `VCVio.Interaction.Basic.StateChain`).
-/

universe u v w

namespace Interaction
namespace Spec

/-- `n`-fold dependent append of `spec` with trivial continuation (`fun _ => replicate …`). -/
abbrev replicate (spec : Spec) : (n : Nat) → Spec :=
  PFunctor.FreeM.replicate PUnit.unit spec

@[simp, grind =] theorem replicate_zero (spec : Spec) : spec.replicate 0 = .done := rfl

theorem replicate_succ (spec : Spec) (n : Nat) :
    spec.replicate (n + 1) = spec.append (fun _ => spec.replicate n) := rfl

/-- Prepend one transcript to a length-`n` replicated tail. -/
abbrev Transcript.replicateCons (spec : Spec) (n : Nat) :
    Transcript spec → Transcript (spec.replicate n) →
    Transcript (spec.replicate (n + 1)) :=
  PFunctor.FreeM.Path.append spec (fun _ => spec.replicate n)

/-- Split the head round from a length-`(n+1)` replicated transcript. -/
abbrev Transcript.replicateUncons (spec : Spec) (n : Nat) :
    Transcript (spec.replicate (n + 1)) →
    Transcript spec × Transcript (spec.replicate n) :=
  fun tr =>
    let ⟨hd, tl⟩ := PFunctor.FreeM.Path.split spec (fun _ => spec.replicate n) tr
    (hd, tl)

/-- Combine `n` transcripts of `spec` into one of `spec.replicate n`. -/
def Transcript.replicateJoin (spec : Spec) :
    (n : Nat) → (Fin n → Transcript spec) → Transcript (spec.replicate n)
  | 0, _ => ⟨⟩
  | n + 1, trs =>
      PFunctor.FreeM.Path.append spec (fun _ => spec.replicate n)
        (trs 0) (Transcript.replicateJoin spec n (fun i => trs i.succ))

/-- Split `spec.replicate n` into `n` per-round transcripts. -/
def Transcript.replicateSplit (spec : Spec) :
    (n : Nat) → Transcript (spec.replicate n) → (Fin n → Transcript spec)
  | 0, _ => fun i => i.elim0
  | n + 1, tr => fun i =>
      let ⟨hd, tl⟩ := PFunctor.FreeM.Path.split spec (fun _ => spec.replicate n) tr
      match i with
        | ⟨0, _⟩ => hd
        | ⟨i + 1, h⟩ => Transcript.replicateSplit spec n tl ⟨i, Nat.lt_of_succ_lt_succ h⟩

@[simp, grind =]
theorem Transcript.replicateSplit_replicateJoin (spec : Spec) :
    (n : Nat) → (trs : Fin n → Transcript spec) → (i : Fin n) →
    Transcript.replicateSplit spec n (Transcript.replicateJoin spec n trs) i = trs i
  | 0, _, i => i.elim0
  | n + 1, trs, ⟨0, _⟩ => by
      simp [replicateSplit, replicateJoin, PFunctor.FreeM.Path.split_append]
  | n + 1, trs, ⟨i + 1, h⟩ => by
      simp only [replicateSplit, replicateJoin, PFunctor.FreeM.Path.split_append]
      exact replicateSplit_replicateJoin spec n (fun i => trs i.succ) ⟨i, Nat.lt_of_succ_lt_succ h⟩

theorem Transcript.replicateSplit_join_zero (spec : Spec) (n : Nat)
    (hd : Transcript spec) (tl : Transcript (spec.replicate n)) :
    Transcript.replicateSplit spec (n + 1)
        (PFunctor.FreeM.Path.append spec (fun _ => spec.replicate n) hd tl) ⟨0, n.succ_pos⟩ =
      hd := by
  simp [replicateSplit, PFunctor.FreeM.Path.split_append]

theorem Transcript.replicateSplit_join_succ (spec : Spec) (n : Nat)
    (hd : Transcript spec) (tl : Transcript (spec.replicate n)) (i : Fin n) :
    Transcript.replicateSplit spec (n + 1)
        (PFunctor.FreeM.Path.append spec (fun _ => spec.replicate n) hd tl) i.succ =
      Transcript.replicateSplit spec n tl i := by
  simp [replicateSplit, PFunctor.FreeM.Path.split_append, Fin.succ]

@[simp, grind =]
theorem Transcript.replicateJoin_replicateSplit (spec : Spec) (n : Nat)
    (tr : Transcript (spec.replicate n)) :
    Transcript.replicateJoin spec n (Transcript.replicateSplit spec n tr) = tr := by
  induction n with
  | zero =>
    cases tr
    rfl
  | succ n ih =>
    let hd := (PFunctor.FreeM.Path.split spec (fun _ => spec.replicate n) tr).1
    let tl := (PFunctor.FreeM.Path.split spec (fun _ => spec.replicate n) tr).2
    have htr :
        tr = PFunctor.FreeM.Path.append spec (fun _ => spec.replicate n) hd tl :=
      (PFunctor.FreeM.Path.append_split spec (fun _ => spec.replicate n) tr).symm
    rw [htr, replicateJoin]
    congr 1
    · simpa using replicateSplit_join_zero spec n hd tl
    · have hfns :
          (fun i => Transcript.replicateSplit spec (n + 1)
              (PFunctor.FreeM.Path.append spec (fun _ => spec.replicate n) hd tl) i.succ) =
            Transcript.replicateSplit spec n tl := by
        funext i
        exact replicateSplit_join_succ spec n hd tl i
      rw [hfns, ih]

variable {S : Type u → Type v}

/-- Replicate a decoration `n` times along `Spec.replicate`. -/
abbrev Decoration.replicate {S : Type u → Type v}
    {spec : Spec} (d : Decoration S spec) : (n : Nat) →
    Decoration S (spec.replicate n) :=
  PFunctor.FreeM.Displayed.Decoration.replicate (P := Spec.basePFunctor)
    (α := PUnit.{u+1}) (a := PUnit.unit) d

/-- Replicate a dependent decoration `n` times along replicated base
decorations. -/
abbrev Decoration.Over.replicate {L : Type u → Type v} {F : ∀ X, L X → Type w}
    {spec : Spec} {d : Decoration L spec}
    (r : Decoration.Over F spec d) : (n : Nat) →
    Decoration.Over F (spec.replicate n) (d.replicate n) :=
  PFunctor.FreeM.Displayed.Decoration.Over.replicate (P := Spec.basePFunctor)
    (α := PUnit.{u+1}) (a := PUnit.unit) r

/-- `Decoration.map` commutes with `Decoration.replicate`. -/
theorem Decoration.map_replicate {S : Type u → Type v} {T : Type u → Type w}
    (f : ∀ X, S X → T X) {spec : Spec} (d : Decoration S spec) (n : Nat) :
    Decoration.map f (spec.replicate n) (d.replicate n) =
      (Decoration.map f spec d).replicate n :=
  PFunctor.FreeM.Displayed.Decoration.map_replicate
    (P := Spec.basePFunctor) (α := PUnit.{u+1}) f PUnit.unit d n

/-- `Decoration.Over.map` commutes with `Over.replicate`. -/
theorem Decoration.Over.map_replicate {L : Type u → Type v} {F G : ∀ X, L X → Type w}
    (η : ∀ X l, F X l → G X l) {spec : Spec} {d : Decoration L spec}
    (r : Decoration.Over F spec d) (n : Nat) :
    Decoration.Over.map η (PFunctor.FreeM.replicate PUnit.unit spec n) (Decoration.replicate d n)
        (Decoration.Over.replicate r n) =
      Decoration.Over.replicate (Decoration.Over.map η spec d r) n :=
  PFunctor.FreeM.Displayed.Decoration.Over.map_replicate
    (P := Spec.basePFunctor) (α := PUnit.{u+1}) η PUnit.unit r n

variable {m : Type u → Type u}

/-- Iterate a strategy `n` times on `spec.replicate n`, threading a value of type `α`. -/
def Strategy.iterate {m : Type u → Type u} [Monad m]
    {spec : Spec} {α : Type u} :
    (n : Nat) →
    (step : Fin n → α → m (Strategy.Plain m spec (fun _ => α))) →
    α →
    m (Strategy.Plain m (spec.replicate n) (fun _ => α))
  | 0, _, a => pure a
  | n + 1, step, a => do
    let strat ← step 0 a
    Strategy.compFlat spec (fun _ => spec.replicate n) strat
      (fun _ mid => iterate n (fun i => step i.succ) mid)

end Spec
end Interaction
