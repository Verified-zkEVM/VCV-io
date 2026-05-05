/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Decoration
import VCVio.Interaction.Basic.Strategy

/-!
# Dependent append of interaction specs

Given two interactions where the second may depend on the outcome of the first,
`Spec.append` fuses them into a single interaction. The file provides the full
algebra around this operation:

- **Transcript operations**: `Transcript.append` / `split` construct and decompose
  combined transcripts, while `Transcript.liftAppend` lifts a two-argument type family
  to a single-argument family on the combined transcript with definitional computation.
- **Strategy composition**: `Strategy.comp` (factored output via `liftAppend`) and
  `Strategy.compFlat` (flat output via `Transcript.append`).
- **Decoration / refinement append** and their naturality lemmas.
-/

universe u v w w₂

namespace Interaction
namespace Spec

/-! ## Structural combinators -/

/-- Sequential composition of interactions: run `s₁` first, then continue with
`s₂ tr₁` where `tr₁` records what happened in `s₁`. -/
def append : (s₁ : Spec) → (Transcript s₁ → Spec) → Spec
  | .done, s₂ => s₂ ⟨⟩
  | .node X rest, s₂ => .node X (fun x => (rest x).append (fun p => s₂ ⟨x, p⟩))

/-- Lift a two-argument type family `F tr₁ tr₂` (indexed by per-phase transcripts)
to a single-argument family on the combined transcript of `s₁.append s₂`.

Crucially, `liftAppend s₁ s₂ F (Transcript.append s₁ s₂ tr₁ tr₂)` reduces
**definitionally** to `F tr₁ tr₂`, which makes this the right combinator for
stage-dependent composition. Without this property, every composition combinator
would need explicit casts between the two-argument and single-argument views.

This combinator propagates up through the entire stack:
- `Transcript.stateChainFamily` uses it at each stage of a state chain
- `Chain.outputFamily` uses it at each round of a continuation chain
- `Strategy.comp` / `Strategy.compWithRoles` use it for the output type
- All security composition theorems factor through it -/
def Transcript.liftAppend :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    ((tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    Transcript (s₁.append s₂) → Type u
  | .done, _, F, tr => F ⟨⟩ tr
  | .node _ rest, s₂, F, ⟨x, tail⟩ =>
      Transcript.liftAppend (rest x) (fun p => s₂ ⟨x, p⟩)
        (fun tr₁ tr₂ => F ⟨x, tr₁⟩ tr₂) tail

/-- `liftAppend` respects pointwise equality of the family `F`. -/
theorem Transcript.liftAppend_congr :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F G : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (∀ tr₁ tr₂, F tr₁ tr₂ = G tr₁ tr₂) →
    (tr : Transcript (s₁.append s₂)) →
    Transcript.liftAppend s₁ s₂ F tr = Transcript.liftAppend s₁ s₂ G tr
  | .done, _, _, _, h, tr => h ⟨⟩ tr
  | .node _ rest, s₂, _, _, h, ⟨x, tail⟩ =>
      liftAppend_congr (rest x) (fun p => s₂ ⟨x, p⟩) _ _
        (fun tr₁ tr₂ => h ⟨x, tr₁⟩ tr₂) tail

/-- A constant family is unaffected by `liftAppend`. -/
@[simp]
theorem Transcript.liftAppend_const (α : Type u) :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr : Transcript (s₁.append s₂)) →
    Transcript.liftAppend s₁ s₂ (fun _ _ => α) tr = α
  | .done, _, _ => rfl
  | .node _ rest, s₂, ⟨x, tail⟩ =>
      liftAppend_const α (rest x) (fun p => s₂ ⟨x, p⟩) tail

/-- Combine a first-phase transcript and a second-phase transcript into a transcript
of the composed interaction `s₁.append s₂`. -/
def Transcript.append :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Transcript (s₁.append s₂)
  | .done, _, _, tr₂ => tr₂
  | .node _ rest, s₂, ⟨x, tail₁⟩, tr₂ =>
      ⟨x, Transcript.append (rest x) (fun p => s₂ ⟨x, p⟩) tail₁ tr₂⟩

/-- `liftAppend` on an appended transcript reduces to the original two-argument
family. -/
@[simp]
theorem Transcript.liftAppend_append :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (tr₁ : Transcript s₁) → (tr₂ : Transcript (s₂ tr₁)) →
    Transcript.liftAppend s₁ s₂ F (Transcript.append s₁ s₂ tr₁ tr₂) = F tr₁ tr₂
  | .done, _, _, _, _ => rfl
  | .node _ rest, s₂, F, ⟨x, tail₁⟩, tr₂ => by
      simpa [Transcript.liftAppend, Transcript.append] using
        Transcript.liftAppend_append (rest x) (fun p => s₂ ⟨x, p⟩)
          (fun tr₁ tr₂ => F ⟨x, tr₁⟩ tr₂) tail₁ tr₂

/-- Decompose a transcript of `s₁.append s₂` into the first-phase prefix and the
second-phase continuation. Inverse of `Transcript.append`. -/
def Transcript.split :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    Transcript (s₁.append s₂) → (tr₁ : Transcript s₁) × Transcript (s₂ tr₁)
  | .done, _, tr => ⟨⟨⟩, tr⟩
  | .node _ rest, s₂, ⟨x, tail⟩ =>
      let ⟨tr₁, tr₂⟩ := Transcript.split (rest x) (fun p => s₂ ⟨x, p⟩) tail
      ⟨⟨x, tr₁⟩, tr₂⟩

/-- Splitting after appending recovers the original components. -/
@[simp, grind =]
theorem Transcript.split_append :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr₁ : Transcript s₁) → (tr₂ : Transcript (s₂ tr₁)) →
    Transcript.split s₁ s₂ (Transcript.append s₁ s₂ tr₁ tr₂) = ⟨tr₁, tr₂⟩
  | .done, _, _, _ => rfl
  | .node _ rest, s₂, ⟨x, tail₁⟩, tr₂ => by
      simp only [Transcript.append, split]; rw [split_append]

/-- Appending the components produced by `split` recovers the original transcript. -/
@[simp]
theorem Transcript.append_split :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (tr : Transcript (s₁.append s₂)) →
    let ⟨tr₁, tr₂⟩ := Transcript.split s₁ s₂ tr
    Transcript.append s₁ s₂ tr₁ tr₂ = tr
  | .done, _, _ => rfl
  | .node _ rest, s₂, ⟨x, tail⟩ => by
      simp only [split, Transcript.append]; rw [append_split]

/-- `liftAppend` can be reconstructed from the transcript pieces returned by
`Transcript.split`. -/
theorem Transcript.liftAppend_split :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (tr : Transcript (s₁.append s₂)) →
    let ⟨tr₁, tr₂⟩ := Transcript.split s₁ s₂ tr
    Transcript.liftAppend s₁ s₂ F tr = F tr₁ tr₂
  | .done, _, _, _ => rfl
  | .node _ rest, s₂, F, ⟨x, tail⟩ => by
      simpa [Transcript.split, Transcript.liftAppend] using
        Transcript.liftAppend_split (rest x) (fun p => s₂ ⟨x, p⟩)
          (fun tr₁ tr₂ => F ⟨x, tr₁⟩ tr₂) tail

/-- Reinterpret a `liftAppend` value against the transcript pair recovered by `split`.
Defined by structural recursion mirroring `liftAppend`/`split`, so no explicit `cast`
appears in the definition. -/
def Transcript.unliftAppend :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (tr : Transcript (s₁.append s₂)) →
    Transcript.liftAppend s₁ s₂ F tr →
    let ⟨tr₁, tr₂⟩ := Transcript.split s₁ s₂ tr
    F tr₁ tr₂
  | .done, _, _, _, x => x
  | .node _ rest, s₂, F, ⟨xm, tail⟩, val =>
      unliftAppend (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => F ⟨xm, tr₁⟩ tr₂) tail val

/-- Transport a value of `F tr₁ tr₂` to `liftAppend s₁ s₂ F (append s₁ s₂ tr₁ tr₂)`.
Defined by structural recursion mirroring `liftAppend`/`append`, so no explicit `cast`
appears. This is the identity function in disguise — at each constructor step,
`liftAppend s₁ s₂ F (append s₁ s₂ tr₁ tr₂)` reduces to `F tr₁ tr₂`. -/
def Transcript.packAppend :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (tr₁ : Transcript s₁) → (tr₂ : Transcript (s₂ tr₁)) →
    F tr₁ tr₂ → liftAppend s₁ s₂ F (append s₁ s₂ tr₁ tr₂)
  | .done, _, _, ⟨⟩, _, x => x
  | .node _ rest, s₂, F, ⟨xm, tail₁⟩, tr₂, x =>
      packAppend (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => F ⟨xm, tr₁⟩ tr₂) tail₁ tr₂ x

/-- Transport a `liftAppend` value back to the pair-indexed family.
Inverse of `packAppend`. -/
def Transcript.unpackAppend :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (tr₁ : Transcript s₁) → (tr₂ : Transcript (s₂ tr₁)) →
    liftAppend s₁ s₂ F (append s₁ s₂ tr₁ tr₂) → F tr₁ tr₂
  | .done, _, _, ⟨⟩, _, x => x
  | .node _ rest, s₂, F, ⟨xm, tail₁⟩, tr₂, x =>
      unpackAppend (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => F ⟨xm, tr₁⟩ tr₂) tail₁ tr₂ x

@[simp]
theorem Transcript.unpackAppend_packAppend :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (tr₁ : Transcript s₁) → (tr₂ : Transcript (s₂ tr₁)) →
    (x : F tr₁ tr₂) →
    unpackAppend s₁ s₂ F tr₁ tr₂ (packAppend s₁ s₂ F tr₁ tr₂ x) = x
  | .done, _, _, ⟨⟩, _, _ => rfl
  | .node _ rest, s₂, F, ⟨xm, tail₁⟩, tr₂, x =>
      unpackAppend_packAppend (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => F ⟨xm, tr₁⟩ tr₂) tail₁ tr₂ x

@[simp]
theorem Transcript.packAppend_unpackAppend :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (tr₁ : Transcript s₁) → (tr₂ : Transcript (s₂ tr₁)) →
    (x : liftAppend s₁ s₂ F (append s₁ s₂ tr₁ tr₂)) →
    packAppend s₁ s₂ F tr₁ tr₂ (unpackAppend s₁ s₂ F tr₁ tr₂ x) = x
  | .done, _, _, ⟨⟩, _, _ => rfl
  | .node _ rest, s₂, F, ⟨xm, tail₁⟩, tr₂, x =>
      packAppend_unpackAppend (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => F ⟨xm, tr₁⟩ tr₂) tail₁ tr₂ x

/-- Collapse a `liftAppend` family indexed by `append tr₁ tr₂` back to the
fused transcript index. Defined by structural recursion, so no explicit `cast`
appears. -/
def Transcript.collapseAppend :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : Transcript (s₁.append s₂) → Type u) →
    (tr : Transcript (s₁.append s₂)) →
    Transcript.liftAppend s₁ s₂
      (fun tr₁ tr₂ => F (Transcript.append s₁ s₂ tr₁ tr₂)) tr →
      F tr
  | .done, _, _, _, x => x
  | .node _ rest, s₂, F, ⟨xm, tail⟩, x =>
      collapseAppend (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tail => F ⟨xm, tail⟩) tail x

@[simp]
theorem Transcript.collapseAppend_append :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : Transcript (s₁.append s₂) → Type u) →
    (tr₁ : Transcript s₁) → (tr₂ : Transcript (s₂ tr₁)) →
    (x : Transcript.liftAppend s₁ s₂
      (fun tr₁ tr₂ => F (Transcript.append s₁ s₂ tr₁ tr₂))
      (Transcript.append s₁ s₂ tr₁ tr₂)) →
    collapseAppend s₁ s₂ F (Transcript.append s₁ s₂ tr₁ tr₂) x =
      cast (Transcript.liftAppend_append s₁ s₂
        (fun tr₁ tr₂ => F (Transcript.append s₁ s₂ tr₁ tr₂))
        tr₁ tr₂) x
  | .done, _, _, ⟨⟩, _, _ => rfl
  | .node _ rest, s₂, F, ⟨xm, tail₁⟩, tr₂, x => by
      simpa [Transcript.collapseAppend, Transcript.append] using
        collapseAppend_append (rest xm) (fun p => s₂ ⟨xm, p⟩)
          (fun tail => F ⟨xm, tail⟩) tail₁ tr₂ x

/-- Lift a family indexed by a split append transcript into a family indexed by
the fused append transcript. -/
abbrev Transcript.liftAppendFamily
    (s₁ : Spec) (s₂ : Transcript s₁ → Spec)
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) :
    Transcript (s₁.append s₂) → Type u :=
  fun tr =>
    let split := Transcript.split s₁ s₂ tr
    F split.1 split.2

@[simp]
theorem Transcript.liftAppendFamily_append
    (s₁ : Spec) (s₂ : Transcript s₁ → Spec)
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u)
    (tr₁ : Transcript s₁) (tr₂ : Transcript (s₂ tr₁)) :
    Transcript.liftAppendFamily s₁ s₂ F (Transcript.append s₁ s₂ tr₁ tr₂) = F tr₁ tr₂ := by
  simpa [Transcript.liftAppendFamily] using
    congrArg (fun p => F p.1 p.2) (Transcript.split_append s₁ s₂ tr₁ tr₂)

/-- Split a fused `liftAppend` value whose payload is a product into the product of
the separately lifted payloads. -/
def Transcript.liftAppendProd :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (A B : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (tr : Transcript (s₁.append s₂)) →
    liftAppend s₁ s₂ (fun tr₁ tr₂ => A tr₁ tr₂ × B tr₁ tr₂) tr →
      liftAppend s₁ s₂ A tr × liftAppend s₁ s₂ B tr
  | .done, _, _, _, _, x => x
  | .node _ rest, s₂, A, B, ⟨xm, tail⟩, x =>
      liftAppendProd (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => A ⟨xm, tr₁⟩ tr₂)
        (fun tr₁ tr₂ => B ⟨xm, tr₁⟩ tr₂) tail x

/-- Inverse of `liftAppendProd`, fusing separately lifted payloads into a lifted
product payload. -/
def Transcript.liftAppendProdMk :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (A B : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (tr : Transcript (s₁.append s₂)) →
    liftAppend s₁ s₂ A tr × liftAppend s₁ s₂ B tr →
      liftAppend s₁ s₂ (fun tr₁ tr₂ => A tr₁ tr₂ × B tr₁ tr₂) tr
  | .done, _, _, _, _, x => x
  | .node _ rest, s₂, A, B, ⟨xm, tail⟩, x =>
      liftAppendProdMk (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => A ⟨xm, tr₁⟩ tr₂)
        (fun tr₁ tr₂ => B ⟨xm, tr₁⟩ tr₂) tail x

@[simp]
theorem Transcript.liftAppendProdMk_liftAppendProd :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (A B : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (tr : Transcript (s₁.append s₂)) →
    (x : liftAppend s₁ s₂ (fun tr₁ tr₂ => A tr₁ tr₂ × B tr₁ tr₂) tr) →
    liftAppendProdMk s₁ s₂ A B tr (liftAppendProd s₁ s₂ A B tr x) = x
  | .done, _, _, _, _, _ => rfl
  | .node _ rest, s₂, A, B, ⟨xm, tail⟩, x =>
      liftAppendProdMk_liftAppendProd (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => A ⟨xm, tr₁⟩ tr₂)
        (fun tr₁ tr₂ => B ⟨xm, tr₁⟩ tr₂) tail x

@[simp]
theorem Transcript.liftAppendProd_liftAppendProdMk :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (A B : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (tr : Transcript (s₁.append s₂)) →
    (x : liftAppend s₁ s₂ A tr × liftAppend s₁ s₂ B tr) →
    liftAppendProd s₁ s₂ A B tr (liftAppendProdMk s₁ s₂ A B tr x) = x
  | .done, _, _, _, _, _ => rfl
  | .node _ rest, s₂, A, B, ⟨xm, tail⟩, x =>
      liftAppendProd_liftAppendProdMk (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => A ⟨xm, tr₁⟩ tr₂)
        (fun tr₁ tr₂ => B ⟨xm, tr₁⟩ tr₂) tail x

@[simp]
theorem Transcript.liftAppendProd_packAppend :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (A B : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (tr₁ : Transcript s₁) → (tr₂ : Transcript (s₂ tr₁)) →
    (x : A tr₁ tr₂ × B tr₁ tr₂) →
    liftAppendProd s₁ s₂ A B (append s₁ s₂ tr₁ tr₂)
      (packAppend s₁ s₂ (fun tr₁ tr₂ => A tr₁ tr₂ × B tr₁ tr₂) tr₁ tr₂ x) =
        (packAppend s₁ s₂ A tr₁ tr₂ x.1, packAppend s₁ s₂ B tr₁ tr₂ x.2)
  | .done, _, _, _, ⟨⟩, _, _ => rfl
  | .node _ rest, s₂, A, B, ⟨xm, tail₁⟩, tr₂, x =>
      liftAppendProd_packAppend (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => A ⟨xm, tr₁⟩ tr₂)
        (fun tr₁ tr₂ => B ⟨xm, tr₁⟩ tr₂) tail₁ tr₂ x

/-- When `tr = append tr₁ tr₂`, the round-trip (`packAppend` then `unliftAppend`)
recovers the original pair-indexed relation value. -/
theorem Transcript.rel_unliftAppend_append :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F G : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (R : ∀ (tr₁ : Transcript s₁) (tr₂ : Transcript (s₂ tr₁)),
      F tr₁ tr₂ → G tr₁ tr₂ → Prop) →
    (tr₁ : Transcript s₁) → (tr₂ : Transcript (s₂ tr₁)) →
    (x : F tr₁ tr₂) → (y : G tr₁ tr₂) →
    let tr := Transcript.append s₁ s₂ tr₁ tr₂
    R (Transcript.split s₁ s₂ tr).1 (Transcript.split s₁ s₂ tr).2
      (Transcript.unliftAppend s₁ s₂ F tr
        (Transcript.packAppend s₁ s₂ F tr₁ tr₂ x))
      (Transcript.unliftAppend s₁ s₂ G tr
        (Transcript.packAppend s₁ s₂ G tr₁ tr₂ y))
    = R tr₁ tr₂ x y
  | .done, _, _, _, _, ⟨⟩, _, _, _ => rfl
  | .node _ rest, s₂, F, G, R, ⟨xm, tail₁⟩, tr₂, x, y => by
      change _ = R ⟨xm, tail₁⟩ tr₂ x y
      simpa [Transcript.append, Transcript.split, Transcript.unliftAppend,
          Transcript.liftAppend, Transcript.packAppend] using
        rel_unliftAppend_append (rest xm) (fun p => s₂ ⟨xm, p⟩)
          (fun tr₁ tr₂ => F ⟨xm, tr₁⟩ tr₂) (fun tr₁ tr₂ => G ⟨xm, tr₁⟩ tr₂)
          (fun tr₁ tr₂ => R ⟨xm, tr₁⟩ tr₂) tail₁ tr₂ x y

/-- Lift a binary relation on pair-indexed type families to the fused transcript
of `s₁.append s₂`. Reduces definitionally when the transcript is
`Transcript.append s₁ s₂ tr₁ tr₂`, making it the right combinator for stating
composition theorems without visible casts. -/
def Transcript.liftAppendRel :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (G : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (R : ∀ (tr₁ : Transcript s₁) (tr₂ : Transcript (s₂ tr₁)),
      F tr₁ tr₂ → G tr₁ tr₂ → Prop) →
    (tr : Transcript (s₁.append s₂)) →
    Transcript.liftAppend s₁ s₂ F tr →
    Transcript.liftAppend s₁ s₂ G tr → Prop
  | .done, _, _, _, R, tr, x, y => R ⟨⟩ tr x y
  | .node _ rest, s₂, F, G, R, ⟨xm, tail⟩, x, y =>
      liftAppendRel (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => F ⟨xm, tr₁⟩ tr₂) (fun tr₁ tr₂ => G ⟨xm, tr₁⟩ tr₂)
        (fun tr₁ tr₂ => R ⟨xm, tr₁⟩ tr₂) tail x y

/-- `liftAppendRel` is equivalent to applying `R` at the transcript pair
recovered by `split`, via `unliftAppend`. -/
theorem Transcript.liftAppendRel_iff :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (G : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (R : ∀ (tr₁ : Transcript s₁) (tr₂ : Transcript (s₂ tr₁)),
      F tr₁ tr₂ → G tr₁ tr₂ → Prop) →
    (tr : Transcript (s₁.append s₂)) →
    (x : Transcript.liftAppend s₁ s₂ F tr) →
    (y : Transcript.liftAppend s₁ s₂ G tr) →
    Transcript.liftAppendRel s₁ s₂ F G R tr x y ↔
      R (Transcript.split s₁ s₂ tr).1 (Transcript.split s₁ s₂ tr).2
        (Transcript.unliftAppend s₁ s₂ F tr x)
        (Transcript.unliftAppend s₁ s₂ G tr y)
  | .done, _, _, _, _, _, _, _ => Iff.rfl
  | .node _ rest, s₂, F, G, R, ⟨xm, tail⟩, x, y =>
      liftAppendRel_iff (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => F ⟨xm, tr₁⟩ tr₂) (fun tr₁ tr₂ => G ⟨xm, tr₁⟩ tr₂)
        (fun tr₁ tr₂ => R ⟨xm, tr₁⟩ tr₂) tail x y

/-- Lift a unary predicate on a pair-indexed type family to the fused transcript
of `s₁.append s₂`. Reduces definitionally when the transcript is
`Transcript.append s₁ s₂ tr₁ tr₂`. -/
def Transcript.liftAppendPred :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (P : ∀ (tr₁ : Transcript s₁) (tr₂ : Transcript (s₂ tr₁)),
      F tr₁ tr₂ → Prop) →
    (tr : Transcript (s₁.append s₂)) →
    Transcript.liftAppend s₁ s₂ F tr → Prop
  | .done, _, _, P, tr, x => P ⟨⟩ tr x
  | .node _ rest, s₂, F, P, ⟨xm, tail⟩, x =>
      liftAppendPred (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => F ⟨xm, tr₁⟩ tr₂)
        (fun tr₁ tr₂ => P ⟨xm, tr₁⟩ tr₂) tail x

/-- `liftAppendPred` is equivalent to applying `P` at the transcript pair
recovered by `split`, via `unliftAppend`. -/
theorem Transcript.liftAppendPred_iff :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u) →
    (P : ∀ (tr₁ : Transcript s₁) (tr₂ : Transcript (s₂ tr₁)),
      F tr₁ tr₂ → Prop) →
    (tr : Transcript (s₁.append s₂)) →
    (x : Transcript.liftAppend s₁ s₂ F tr) →
    Transcript.liftAppendPred s₁ s₂ F P tr x ↔
      P (Transcript.split s₁ s₂ tr).1 (Transcript.split s₁ s₂ tr).2
        (Transcript.unliftAppend s₁ s₂ F tr x)
  | .done, _, _, _, _, _ => Iff.rfl
  | .node _ rest, s₂, F, P, ⟨xm, tail⟩, x =>
      liftAppendPred_iff (rest xm) (fun p => s₂ ⟨xm, p⟩)
        (fun tr₁ tr₂ => F ⟨xm, tr₁⟩ tr₂)
        (fun tr₁ tr₂ => P ⟨xm, tr₁⟩ tr₂) tail x

theorem append_done (s₂ : Transcript Spec.done → Spec) :
    Spec.done.append s₂ = s₂ ⟨⟩ := rfl

theorem append_node (X : Type u) (rest : X → Spec) (s₂ : Transcript (.node X rest) → Spec) :
    (Spec.node X rest).append s₂ =
      .node X (fun x => (rest x).append (fun p => s₂ ⟨x, p⟩)) := rfl

variable {m : Type u → Type u}

/-- Monadic composition of strategies along `Spec.append`.

The output type is given as a two-argument family
`F : Transcript s₁ → Transcript (s₂ tr₁) → Type u`, lifted to the combined spec
via `Transcript.liftAppend`. The continuation receives the first-phase strategy's
output and produces a second-phase strategy whose output family is `F tr₁`.

This is the preferred composition form: `liftAppend` ensures the output type
reduces definitionally when combined with `Transcript.append`, which is essential
for dependent chain composition (see `Strategy.stateChainComp`). -/
def Strategy.comp {m : Type u → Type u} [Monad m] :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    {Mid : Transcript s₁ → Type u} →
    {F : (tr₁ : Transcript s₁) → Transcript (s₂ tr₁) → Type u} →
    Strategy m s₁ Mid →
    ((tr₁ : Transcript s₁) → Mid tr₁ → m (Strategy m (s₂ tr₁) (F tr₁))) →
    m (Strategy m (s₁.append s₂) (Transcript.liftAppend s₁ s₂ F))
  | .done, _, _, _, mid, f => f ⟨⟩ mid
  | .node _ rest, s₂, _, _, ⟨x, cont⟩, f => pure ⟨x, do
      let next ← cont
      comp (rest x) (fun p => s₂ ⟨x, p⟩) next
        (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩

/-- Monadic composition of strategies along `Spec.append` with a single output family
`Output` on the combined transcript. The continuation indexes into `Output` via
`Transcript.append`.

Use this when the output type is naturally expressed over the combined transcript
rather than as a two-argument family (e.g., constant output types, or when working
with `Strategy.iterate`). See also `Strategy.comp`. -/
def Strategy.compFlat {m : Type u → Type u} [Monad m] :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    {Mid : Transcript s₁ → Type u} →
    {Output : Transcript (s₁.append s₂) → Type u} →
    Strategy m s₁ Mid →
    ((tr₁ : Transcript s₁) → Mid tr₁ →
      m (Strategy m (s₂ tr₁) (fun tr₂ => Output (Transcript.append s₁ s₂ tr₁ tr₂)))) →
    m (Strategy m (s₁.append s₂) Output)
  | .done, _, _, _, mid, f => f ⟨⟩ mid
  | .node _ rest, s₂, _, _, ⟨x, cont⟩, f => pure ⟨x, do
      let next ← cont
      compFlat (rest x) (fun p => s₂ ⟨x, p⟩) next (fun tr₁ mid => f ⟨x, tr₁⟩ mid)⟩

/-- Extract the first-phase strategy from a strategy on a composed interaction.
At each first-phase transcript `tr₁`, the remainder is the second-phase strategy
with output indexed by `Transcript.append`. -/
def Strategy.splitPrefix {m : Type u → Type u} [Functor m] :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    {Output : Transcript (s₁.append s₂) → Type u} →
    Strategy m (s₁.append s₂) Output →
    Strategy m s₁ (fun tr₁ =>
      Strategy m (s₂ tr₁) (fun tr₂ => Output (Transcript.append s₁ s₂ tr₁ tr₂)))
  | .done, _, _, p => p
  | .node _ rest, s₂, _, ⟨x, cont⟩ =>
      ⟨x, (splitPrefix (rest x) (fun p => s₂ ⟨x, p⟩) ·) <$> cont⟩

/-- Concatenate per-node labels along `Spec.append`. -/
def Decoration.append {S : Type u → Type v}
    {s₁ : Spec} {s₂ : Transcript s₁ → Spec}
    (d₁ : Decoration S s₁)
    (d₂ : (tr₁ : Transcript s₁) → Decoration S (s₂ tr₁)) :
    Decoration S (s₁.append s₂) :=
  match s₁, d₁ with
  | .done, _ => d₂ ⟨⟩
  | .node _ _, ⟨s, dRest⟩ =>
      ⟨s, fun x => Decoration.append (dRest x)
        (fun p => d₂ ⟨x, p⟩)⟩

/-- Concatenate dependent decoration layers along `Spec.append`, over appended
base decorations. -/
def Decoration.Over.append {L : Type u → Type v} {F : ∀ X, L X → Type w}
    {s₁ : Spec} {s₂ : Transcript s₁ → Spec}
    {d₁ : Decoration L s₁}
    {d₂ : (tr₁ : Transcript s₁) → Decoration L (s₂ tr₁)}
    (r₁ : Decoration.Over F s₁ d₁)
    (r₂ : (tr₁ : Transcript s₁) → Decoration.Over F (s₂ tr₁) (d₂ tr₁)) :
    Decoration.Over F (s₁.append s₂) (d₁.append d₂) :=
  match s₁, d₁, r₁ with
  | .done, _, _ => r₂ ⟨⟩
  | .node _ _, ⟨_, _⟩, ⟨fData, rRest⟩ =>
      ⟨fData, fun x => Over.append (rRest x) (fun p => r₂ ⟨x, p⟩)⟩

/-- `Decoration.Over.map` commutes with `Over.append`. -/
theorem Decoration.Over.map_append {L : Type u → Type v} {F G : ∀ X, L X → Type w}
    (η : ∀ X l, F X l → G X l) :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (d₁ : Decoration L s₁) →
    (d₂ : (tr₁ : Transcript s₁) → Decoration L (s₂ tr₁)) →
    (r₁ : Decoration.Over F s₁ d₁) →
    (r₂ : (tr₁ : Transcript s₁) → Decoration.Over F (s₂ tr₁) (d₂ tr₁)) →
    Decoration.Over.map η (s₁.append s₂) (d₁.append d₂) (Over.append r₁ r₂) =
      Over.append (Over.map η s₁ d₁ r₁)
        (fun tr₁ => Over.map η (s₂ tr₁) (d₂ tr₁) (r₂ tr₁))
  | .done, _, _, _, r₁, r₂ => rfl
  | .node X rest, s₂, ⟨l, dRest⟩, d₂, ⟨fData, rRest⟩, r₂ => by
      simp only [Spec.append, Decoration.append, Decoration.Over.append, Decoration.Over.map]
      congr 1; funext x
      exact map_append η (rest x) (fun p => s₂ ⟨x, p⟩) (dRest x) (fun p => d₂ ⟨x, p⟩)
        (rRest x) (fun p => r₂ ⟨x, p⟩)

/-- `Decoration.map` commutes with `Decoration.append`. -/
theorem Decoration.map_append {S : Type u → Type v} {T : Type u → Type w}
    (f : ∀ X, S X → T X) :
    (s₁ : Spec) → (s₂ : Transcript s₁ → Spec) →
    (d₁ : Decoration S s₁) →
    (d₂ : (tr₁ : Transcript s₁) → Decoration S (s₂ tr₁)) →
    Decoration.map f (s₁.append s₂) (d₁.append d₂) =
      (Decoration.map f s₁ d₁).append (fun tr₁ => Decoration.map f (s₂ tr₁) (d₂ tr₁))
  | .done, _, _, _ => rfl
  | .node X rest, s₂, ⟨s, dRest⟩, d₂ => by
      simp only [Spec.append, Decoration.append, Decoration.map]
      congr 1; funext x
      exact map_append f (rest x) (fun p => s₂ ⟨x, p⟩) (dRest x) (fun p => d₂ ⟨x, p⟩)

end Spec
end Interaction
