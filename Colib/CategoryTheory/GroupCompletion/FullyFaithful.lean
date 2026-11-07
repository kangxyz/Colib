/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.Functoriality

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/FullyFaithful.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Fully faithful descent through Grayson's quotient

An equivariant fully faithful functor with invertible lineators remains fully
faithful on the actual localization categories. This is used for the
identity-extension model of the zero fiber.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u₁ v₁ u₂ v₂
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
open CategoryTheory.Functor.LaxLeftLinear
namespace CategoryTheory.GroupCompletion.ActionLocalization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u₁} [Category.{v₁} D] [MonoidalLeftAction C D]
  {E : Type u₂} [Category.{v₂} E] [MonoidalLeftAction C E]
  (F : D ⥤ E) [F.LaxLeftLinear C] [∀ (s : C) (X : D), IsIso (μₗ F s X)]

lemma HomRep.rel_of_map_rel [F.Faithful] {X Y : D} (f g : HomRep (C := C) X Y)
    (h : Rel (mapRep F f) (mapRep F g)) : Rel f g := by
  obtain ⟨e, he⟩ := h
  change f.denom ≅ g.denom at e
  refine ⟨e, F.map_injective ?_⟩
  change e.hom ⊵ₗ F.obj X ≫ μₗ F g.denom X ≫ F.map g.map =
    μₗ F f.denom X ≫ F.map f.map at he
  rw [μₗ_naturality_left_assoc, ← F.map_comp] at he
  exact (cancel_epi (μₗ F f.denom X)).1 he

instance mapFunctor_faithful [F.Faithful] : (mapFunctor (C := C) F).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨f, rfl⟩ := mkHom_surjective X.obj Y.obj f
    obtain ⟨g, rfl⟩ := mkHom_surjective X.obj Y.obj g
    exact (mkHom_eq_iff f g).2 (HomRep.rel_of_map_rel F f g
      ((mkHom_eq_iff _ _).1 h))

instance mapFunctor_full [F.Full] : (mapFunctor (C := C) F).Full where
  map_surjective {X Y} h := by
    obtain ⟨r, rfl⟩ := mkHom_surjective (F.obj X.obj) (F.obj Y.obj) h
    refine ⟨mkHom ⟨r.denom, F.preimage (inv (μₗ F r.denom X.obj) ≫ r.map)⟩, ?_⟩
    rw [mapFunctor_mkHom]
    congr 1
    apply congrArg (HomRep.mk r.denom)
    simp

end CategoryTheory.GroupCompletion.ActionLocalization
