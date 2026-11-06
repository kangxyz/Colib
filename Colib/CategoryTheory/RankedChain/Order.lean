/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Order.Hom.Set
public import Colib.CategoryTheory.SemisimplexResolution.Basic

/-!
# The actual face poset of strictly ranked chains

Strict growth of the original object ranks makes every chain's vertices
distinct. Hence an injective face is unique when it exists, while its strict
functor equality retains all original parallel-arrow data. Mutual exact faces
coincide literally, yielding an actual partial order. The original last-vertex
functor factors through the original semisimplex category; dimension is proved
to be a direct rank there, including its equality-transport alternative.

Implementation provenance:
`Quillen/CategoryTheory/RankedChain/Order.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u

namespace CategoryTheory.RankedChainOrder
variable (C : Type u) [SmallCategory C] (rank : C → ℕ)

/-- A nonempty finite chain with strictly increasing original object ranks. -/
structure Obj : Type u where
  /-- The number of arrows in the chain; there are `dim + 1` vertices. -/
  dim : ℕ
  /-- The chain in `C` whose vertex ranks are required to increase strictly. -/
  chain : ComposableArrows C dim
  strict : StrictMono (fun i ↦ rank (chain.obj i))

/-- A literal injective face of one strict chain in another. -/
structure Face (A B : Obj C rank) : Type u where
  /-- The order embedding selecting the vertices of `A` inside `B`. -/
  index : Fin (A.dim + 1) ↪o Fin (B.dim + 1)
  face : index.monotone.functor ⋙ B.chain = A.chain

@[ext] theorem Face.ext {A B : Obj C rank} {f g : Face C rank A B}
    (h : f.index = g.index) : f = g := by
  cases f; cases g; cases h; rfl

/-- Strict ranks identify each original vertex occurrence uniquely. -/
instance faceSubsingleton (A B : Obj C rank) : Subsingleton (Face C rank A B) where
  allEq f g := by
    apply Face.ext C rank
    apply DFunLike.ext
    intro i
    apply B.strict.injective
    exact congrArg rank ((congrArg (fun T : ComposableArrows C A.dim ↦ T.obj i) f.face).trans
      (congrArg (fun T : ComposableArrows C A.dim ↦ T.obj i) g.face).symm)

/-- The literal identity face. -/
def Face.id (A : Obj C rank) : Face C rank A A :=
  ⟨(OrderIso.refl _).toOrderEmbedding, rfl⟩

/-- Actual strict-face composition. -/
def Face.comp {A B E : Obj C rank} (f : Face C rank A B) (g : Face C rank B E) :
    Face C rank A E :=
  ⟨f.index.trans g.index, by
    change f.index.monotone.functor ⋙ (g.index.monotone.functor ⋙ E.chain) = A.chain
    rw [g.face, f.face]⟩

/-- An injective face cannot increase the source dimension. -/
theorem Face.dim_le {A B : Obj C rank} (f : Face C rank A B) : A.dim ≤ B.dim := by
  have h := Fintype.card_le_of_injective f.index f.index.injective
  simpa only [Fintype.card_fin, Nat.add_le_add_iff_right] using h

/-- An order embedding of a finite ordinal into itself is exactly identity. -/
theorem self_embedding_eq_refl {n : ℕ} (f : Fin n ↪o Fin n) :
    f = (OrderIso.refl _).toOrderEmbedding := by
  let e := OrderIso.ofSurjective f (Finite.surjective_of_injective f.injective)
  have he : e = OrderIso.refl _ := Subsingleton.elim _ _
  exact congrArg OrderIso.toOrderEmbedding he

/-- Mutual literal faces are the same actual chain, not merely isomorphic. -/
theorem face_antisymm {A B : Obj C rank} (f : Face C rank A B) (g : Face C rank B A) : A = B := by
  have hd := Nat.le_antisymm (f.dim_le C rank) (g.dim_le C rank)
  cases A with
  | mk n a ha =>
    cases B with
    | mk m b hb =>
      dsimp at hd
      subst m
      have hf := f.face
      have he := self_embedding_eq_refl f.index
      rw [he] at hf
      change b = a at hf
      subst b
      rfl

/-- The original face relation is a genuine partial order. -/
instance : PartialOrder (Obj C rank) where
  le A B := Nonempty (Face C rank A B)
  le_refl A := ⟨Face.id C rank A⟩
  le_trans A B E f g := ⟨Face.comp C rank f.some g.some⟩
  le_antisymm A B f g := face_antisymm C rank f.some g.some

/-- The face encoded by an actual order arrow; uniqueness removes all choice
from its resulting original index map and strict face equation. -/
def faceOfHom {A B : Obj C rank} (f : A ⟶ B) : Face C rank A B :=
  (leOfHom f).some

/-- Every genuine strict face determines an arrow of the actual face poset. -/
def homOfFace {A B : Obj C rank} (f : Face C rank A B) : A ⟶ B :=
  homOfLE ⟨f⟩

@[simp] theorem faceOfHom_homOfFace {A B : Obj C rank} (f : Face C rank A B) :
    faceOfHom C rank (homOfFace C rank f) = f := Subsingleton.elim _ _

end CategoryTheory.RankedChainOrder

namespace CategoryTheory.RankedChainOrder
variable (C : Type u) [SmallCategory C] (rank : C → ℕ)

/-- Every original arrow either strictly raises rank or is an actual equality
transport. This rules out both nonidentity endomorphisms and rank-zero cycles. -/
def IsDirectRank : Prop :=
  ∀ {X Y : C} (f : X ⟶ Y), rank X < rank Y ∨ ∃ e : X = Y, f = eqToHom e

/-- Forget only the proved strict-rank property, retaining the actual chain
and its exact original injective face. -/
def forget : Obj C rank ⥤ SemisimplexResolution.Obj C where
  obj A := ⟨A.dim, A.chain⟩
  map f := ⟨(faceOfHom C rank f).index, (faceOfHom C rank f).face⟩
  map_id A := by
    have h : faceOfHom C rank (𝟙 A) = Face.id C rank A := Subsingleton.elim _ _
    simp only [h]
    rfl
  map_comp f g := by
    have h : faceOfHom C rank (f ≫ g) = Face.comp C rank
        (faceOfHom C rank f) (faceOfHom C rank g) := Subsingleton.elim _ _
    simp only [h]
    rfl

/-- The last-vertex functor preserves the original terminal object and
original face-composite maps, with no replacement of the target category. -/
def lastVertex : Obj C rank ⥤ C := forget C rank ⋙ SemisimplexResolution.lastVertex C

/-- Dimension is a genuine direct rank on the original semisimplex category. -/
theorem semisimplex_directRank :
    IsDirectRank (SemisimplexResolution.Obj C) SemisimplexResolution.Obj.dim := by
  intro A B f
  have hdim : A.dim ≤ B.dim := by
    have h := Fintype.card_le_of_injective f.index f.index.injective
    simpa only [Fintype.card_fin, Nat.add_le_add_iff_right] using h
  rcases lt_or_eq_of_le hdim with hlt | heq
  · exact Or.inl hlt
  · have hAB : A = B := by
      cases A with
      | mk n a =>
        cases B with
        | mk m b =>
          dsimp at heq
          subst m
          have hface := f.face
          rw [self_embedding_eq_refl f.index] at hface
          change b = a at hface
          subst b
          rfl
    subst B
    exact Or.inr ⟨rfl, SemisimplexResolution.Hom.ext C (self_embedding_eq_refl f.index)⟩

end CategoryTheory.RankedChainOrder
