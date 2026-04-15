/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.Interaction.Basic.Spec

/-!
# Node-local contexts and schemas

This file isolates the node-local metadata layer of the `Interaction`
framework.

`Spec.Node.Context` is the semantic notion:
for each move space `X`, it gives the type of node-local information available
at a node whose next move lives in `X`.

`Spec.Node.Schema` is the structured, telescope-style front-end for building
such contexts in stages. This follows the use of **contexts** and
**telescopes** in dependent type theory, where later entries may depend on
earlier ones, and it also echoes the **schema / instance** split common in
database theory.

References informing this terminology:
* de Bruijn (1991), telescopes in dependent type theory;
* Castellan–Clairambault–Dybjer (2020), contexts and types in context via
  categories with families;
* Spivak (2012), schemas as structured descriptions whose instances carry data.

The rest of the interaction core consumes realized node contexts, not schemas:
* `Spec.Decoration Γ spec` decorates a protocol tree by concrete values in
  context `Γ`;
* `Spec.SyntaxOver` and `Spec.InteractionOver` define syntax and execution over
  those realized contexts.
* `Spec.ShapeOver` is the functorial refinement of `Spec.SyntaxOver`, used
  when node objects support generic continuation reindexing.
* `Spec.Node.ContextHom` records structure-preserving maps between realized
  contexts, so forgetting or repackaging metadata can be expressed explicitly.
* `Spec.Node.Schema.SchemaMap` is the corresponding notion at the schema level: a
  semantic map between realized contexts presented with their schema sources
  and targets.
* `Spec.Node.Schema.Prefix` records syntactic schema-prefix inclusions, which
  induce canonical forgetful maps on realized contexts.

Worked example:
if we previously thought of node metadata in two stages,
first a tag `Tag X` and then dependent data `Data X tag`,
the corresponding schema is
`(Spec.Node.Schema.singleton Tag).extend Data`.
Its realized context is `Spec.Node.Context.extend Tag Data`,
so a single decoration by that context packages the old staged view into one
semantic object.
-/

universe u v w w₂ w₃

namespace Interaction
namespace Spec
namespace Node

/--
`Context` is the realized family of node-local information.

If `Γ : Node.Context`, then for every move space `X`, the type `Γ X` describes
what metadata is available at a node whose next move lies in `X`.

This is the semantic object consumed by the rest of the interaction core.
Contexts may be written directly, or assembled in stages via `Node.Schema`.
-/
abbrev Context := Type u → Type v

/--
`ContextHom Γ Δ` is a nodewise map from context `Γ` to context `Δ`.

At each move space `X`, it turns a `Γ X`-value into a `Δ X`-value. This is the
right notion of morphism for realized node contexts, and it is what
`Spec.Decoration.map` consumes.
-/
abbrev ContextHom (Γ : Type u → Type v) (Δ : Type u → Type w) := ∀ X, Γ X → Δ X

/-- Identity morphism on a realized node context. -/
def ContextHom.id (Γ : Context) : ContextHom Γ Γ := fun _ x => x

/-- Composition of realized node-context morphisms. -/
def ContextHom.comp {Γ : Type u → Type v} {Δ : Type u → Type w} {Λ : Type u → Type w₂}
    (g : ContextHom Δ Λ) (f : ContextHom Γ Δ) : ContextHom Γ Λ :=
  fun X => g X ∘ f X

/--
The empty node context, carrying no information at any node.

This is the neutral context used by the plain `Shape` / `Interaction`
specializations.
-/
def Context.empty : Context := fun _ => PUnit

/--
Extend a realized node context by one dependent field.

If `Γ` is the current context and `A X γ` is a new field whose type may depend
on the existing context value `γ : Γ X`, then `Γ.extend A` is the enlarged
context containing both pieces of data.

The new field is allowed to live in a different universe from the existing
context. This keeps `Context.extend` flexible even though `Schema` itself uses
one fixed universe parameter for its staged fields.
-/
def Context.extend (Γ : Type u → Type v) (A : ∀ X, Γ X → Type w) : Type u → Type (max v w) :=
  fun X => Σ γ : Γ X, A X γ

/--
Forget the most recently added field of an extended node context.

This is the canonical projection from `Context.extend Γ A` back to its base
context `Γ`.
-/
def Context.extendFst (Γ : Type u → Type v) (A : ∀ X, Γ X → Type w) :
    ContextHom (Context.extend Γ A) Γ :=
  fun _ => Sigma.fst

/--
Map one extended node context to another by:
* mapping the base context with `f`, and
* mapping the new dependent field with `g`.
-/
def Context.extendMap
    {Γ : Type u → Type v} {Δ : Type u → Type w}
    {A : ∀ X, Γ X → Type w₂} {B : ∀ X, Δ X → Type w₃}
    (f : ContextHom Γ Δ)
    (g : ∀ X γ, A X γ → B X (f X γ)) :
    ContextHom (Context.extend Γ A) (Context.extend Δ B) :=
  fun X ⟨γ, a⟩ => ⟨f X γ, g X γ a⟩

/--
`Schema Γ` is a telescope whose realized node context is `Γ`.

Schemas are the structured front-end for building node-local contexts:
* `nil` is the empty telescope;
* `singleton A` is a one-field schema with no prior dependencies;
* `snoc S A` appends a new field whose type may depend on the earlier realized
  context carried by `S`.

The semantic object used elsewhere in the interaction core is still the
realized context `Γ`; a schema is simply a readable way to assemble such
contexts stage by stage, while keeping the dependency structure visible.

For example, a two-stage schema consisting of:
* a first field `Tag X`, and then
* a second field `Data X tag` depending on that tag

is written as `(Schema.singleton Tag).extend Data`,
and realizes to the context `Context.extend Tag Data`.
-/
inductive Schema : Context → Type (max (u + 1) (v + 1)) where
  /-- The empty schema. -/
  | nil : Schema Context.empty
  /-- A one-field schema whose realized context is exactly `A`. -/
  | singleton (A : Type u → Type v) : Schema A
/-- Extend an existing schema by one further dependent field. -/
  | snoc {Γ : Context} (S : Schema Γ) (A : ∀ X, Γ X → Type v) :
      Schema (Context.extend Γ A)

/--
Extend a node schema by one further dependent field.

This is the functional wrapper around the `snoc` constructor, useful when a
schema is being built incrementally.
-/
abbrev Schema.extend {Γ : Context} (S : Schema Γ) (A : ∀ X, Γ X → Type v) :
    Schema (Context.extend Γ A) :=
  .snoc S A

/--
Interpret a node schema as its realized node context.

This uses the active name `toContext` rather than a noun like `context`
because a schema is a descriptive telescope, while a context is the semantic
family it determines.
-/
abbrev Schema.toContext {Γ : Context} (_ : Schema Γ) : Context := Γ

namespace Schema

/--
`SchemaMap S T` is a semantic morphism from schema `S` to schema `T`.

Unlike `Schema.Prefix`, this is not a syntactic extension relation. It is
simply a map between the realized node contexts of `S` and `T`, presented with
the schema source and target so that later constructions can speak directly in
schema-level terms.

So:
* `Schema.Prefix` expresses a particular syntactic way one schema sits inside
  another;
* `SchemaMap` expresses an arbitrary semantic transformation between their
  realized contexts.
-/
abbrev SchemaMap {Γ Δ : Context} (S : Schema Γ) (T : Schema Δ) :=
  ContextHom S.toContext T.toContext

/-- Identity schema morphism. -/
def SchemaMap.id {Γ : Context} (S : Schema Γ) : SchemaMap S S :=
  ContextHom.id _

/--
Treat a realized context morphism as a schema morphism between any schemas
presenting those contexts.
-/
abbrev SchemaMap.ofContextHom
    {Γ Δ : Context} {S : Schema Γ} {T : Schema Δ}
    (f : ContextHom Γ Δ) : SchemaMap S T := f

/-- Composition of schema morphisms. -/
def SchemaMap.comp {Γ Δ Λ : Context}
    {S : Schema Γ} {T : Schema Δ} {U : Schema Λ}
    (g : SchemaMap T U) (f : SchemaMap S T) : SchemaMap S U :=
  ContextHom.comp g f

/--
Forget that a schema morphism was presented at the schema level and view it as
the underlying realized context morphism.
-/
abbrev SchemaMap.toContextHom {Γ Δ : Context} {S : Schema Γ} {T : Schema Δ}
    (f : SchemaMap S T) : ContextHom S.toContext T.toContext := f

/--
Extend a schema morphism by one further dependent field.

If `f : SchemaMap S T` maps the base contexts and `g` maps the newly added
field over each base value, then `SchemaMap.extend f g` is the induced schema
morphism between the corresponding one-step schema extensions.
-/
def SchemaMap.extend
    {Γ Δ : Context}
    {S : Schema Γ} {T : Schema Δ}
    {A : ∀ X, Γ X → Type v} {B : ∀ X, Δ X → Type v}
    (f : SchemaMap S T)
    (g : ∀ X γ, A X γ → B X (f X γ)) :
    SchemaMap (S.extend A) (T.extend B) :=
  Context.extendMap f g

@[simp]
theorem SchemaMap.extend_id
    {Γ : Context} {S : Schema Γ} {A : ∀ X, Γ X → Type v} :
    SchemaMap.extend (SchemaMap.id S) (fun _ _ x => x) = SchemaMap.id (S.extend A) := by
  funext X x
  cases x
  rfl

theorem SchemaMap.extend_comp
    {Γ Δ Λ : Context}
    {S : Schema Γ} {T : Schema Δ} {U : Schema Λ}
    {A : ∀ X, Γ X → Type v}
    {B : ∀ X, Δ X → Type v}
    {C : ∀ X, Λ X → Type v}
    (g : SchemaMap T U) (f : SchemaMap S T)
    (fOver : ∀ X γ, A X γ → B X (f X γ))
    (gOver : ∀ X δ, B X δ → C X (g X δ)) :
    SchemaMap.comp (SchemaMap.extend g gOver) (SchemaMap.extend f fOver) =
      SchemaMap.extend (SchemaMap.comp g f)
        (fun X γ => gOver X (f X γ) ∘ fOver X γ) := by
  funext X x
  cases x
  rfl

/--
Forget the most recently added field of a schema extension.
-/
abbrev SchemaMap.fst
    {Γ : Context} {S : Schema Γ}
    (A : ∀ X, Γ X → Type v) :
    SchemaMap (S.extend A) S :=
  Context.extendFst _ A

/--
`Prefix S T` means that `S` is a syntactic prefix of the schema `T`.

Each `snoc` step adds one new field on the right, so a prefix determines a
canonical forgetful map from the realized context of `T` back to the realized
context of `S`.

This is intentionally a syntactic notion, not merely a semantic one: two
schemas may realize equivalent node contexts without one being a prefix of the
other.
-/
inductive Prefix :
    {Γ Δ : Context.{u, v}} →
    Schema Γ → Schema Δ → Type (max (u + 1) (v + 1)) where
  /-- Every schema is a prefix of itself. -/
  | refl {Γ : Context.{u, v}} (S : Schema Γ) : Schema.Prefix S S
  /-- If `S` is a prefix of `T`, then it is also a prefix of any one-field
  extension of `T`. -/
  | snoc {Γ Δ : Context.{u, v}} {S : Schema Γ} {T : Schema Δ}
      (p : Schema.Prefix S T) (A : ∀ X, Δ X → Type v) :
      Schema.Prefix S (T.extend A)

/--
The realized context morphism induced by a schema prefix.

This forgets exactly the fields appended after the prefix `S`.
-/
def Prefix.toContextHom :
    {Γ Δ : Context.{u, v}} → {S : Schema Γ} → {T : Schema Δ} →
    Schema.Prefix S T → ContextHom T.toContext S.toContext
  | _, _, _, _, .refl _ => ContextHom.id _
  | _, _, _, _, .snoc p A =>
      ContextHom.comp (Prefix.toContextHom p) (Context.extendFst _ A)

/--
View a schema prefix as the corresponding schema morphism that forgets the
fields added after the prefix.
-/
abbrev Prefix.toSchemaMap
    {Γ Δ : Context.{u, v}} {S : Schema Γ} {T : Schema Δ}
    (p : Schema.Prefix S T) : SchemaMap T S :=
  p.toContextHom

end Schema

end Node
end Spec
end Interaction
