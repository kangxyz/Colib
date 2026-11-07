/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.MonoidalFunctor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/MonoidalFunctorNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Coherence of the actual monoidal completion functor -/
@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction
universe u v w z u' v'
namespace CategoryTheory.GroupCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type w} [Category.{z} D] [MonoidalCategory D]
  {E : Type u'} [Category.{v'} E] [MonoidalCategory E]

/-- Original arrows are mapped by the original pair functor. -/
lemma monoidalMap_ofHom (F : C ⥤ D) [F.Monoidal] {X Y : C × C} (f : X ⟶ Y) :
    (monoidalMap F).map (ActionLocalization.ofHom (C := C) f) =
      ActionLocalization.ofHom (C := D) ((F.prod F).map f) :=
  ActionLocalization.mapAlong_ofHom F (F.prod F) (monoidalPairLinear F) f

/-- Translation is preserved with its actual tensor comparison, rather than strictly. -/
lemma monoidalMap_translation (F : C ⥤ D) [F.Monoidal] (s : C) (X : C × C) :
    (monoidalMap F).map (ActionLocalization.translation s X) =
      ActionLocalization.translation (F.obj s) (F.obj X.1, F.obj X.2) ≫
        ActionLocalization.ofHom (C := D)
          (X := (F.obj s ⊗ F.obj X.1, F.obj s ⊗ F.obj X.2))
          (Y := (F.obj (s ⊗ X.1), F.obj (s ⊗ X.2)))
          (Functor.LaxMonoidal.μ F s X.1, Functor.LaxMonoidal.μ F s X.2) := by
  change ActionLocalization.mkHom (C := D)
    (X := (F.obj X.1, F.obj X.2))
    (Y := (F.obj (s ⊗ X.1), F.obj (s ⊗ X.2))) ⟨F.obj s,
    (Functor.LaxMonoidal.μ F s X.1 ≫ F.map (𝟙 _),
      Functor.LaxMonoidal.μ F s X.2 ≫ F.map (𝟙 _))⟩ = _
  simpa only [Functor.map_id, Category.comp_id] using
    ActionLocalization.mkHom_factorization (C := D)
      (ActionLocalization.HomRep.mk (C := D)
        (X := (F.obj X.1, F.obj X.2))
        (Y := (F.obj (s ⊗ X.1), F.obj (s ⊗ X.2))) (F.obj s)
        (Functor.LaxMonoidal.μ F s X.1, Functor.LaxMonoidal.μ F s X.2))

/-- The representative square supplied by an actual monoidal natural transformation. -/
lemma monoidalMap_naturality_component {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    (η : F ⟶ G) [η.IsMonoidal] (s A A' : C) (f : s ⊗ A ⟶ A') :
    η.app s ▷ F.obj A ≫ G.obj s ◁ η.app A ≫
        Functor.LaxMonoidal.μ G s A ≫ G.map f =
      Functor.LaxMonoidal.μ F s A ≫ F.map f ≫ η.app A' := by
  rw [← tensorHom_def_assoc, ← NatTrans.IsMonoidal.tensor_assoc]
  rw [η.naturality]

/-- A monoidal natural isomorphism gives an isomorphism of the original completion maps. -/
def monoidalMapIso {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    (e : F ≅ G) [e.hom.IsMonoidal] : monoidalMap F ≅ monoidalMap G :=
  NatIso.ofComponents (fun X ↦
    (ActionLocalization.ofFunctor (C := D) (D := D × D)).mapIso
      ((e.app X.obj.1).prod (e.app X.obj.2))) (by
    intro X Y h
    induction h using Quotient.inductionOn with
    | _ h =>
      change ActionLocalization.mkHom _ ≫ ActionLocalization.ofHom _ =
        ActionLocalization.ofHom _ ≫ ActionLocalization.mkHom _
      rw [ActionLocalization.mkHom_comp_ofHom, ActionLocalization.ofHom_comp_mkHom]
      apply Quotient.sound
      refine ⟨e.app h.denom, ?_⟩
      apply Prod.ext
      · change (e.hom.app h.denom ▷ F.obj X.obj.1) ≫
          (G.obj h.denom ◁ e.hom.app X.obj.1 ≫
            (Functor.LaxMonoidal.μ G h.denom X.obj.1 ≫ G.map h.map.1)) =
          (Functor.LaxMonoidal.μ F h.denom X.obj.1 ≫ F.map h.map.1) ≫ e.hom.app Y.obj.1
        simpa only [Category.assoc] using
          monoidalMap_naturality_component e.hom h.denom X.obj.1 Y.obj.1 h.map.1
      · change (e.hom.app h.denom ▷ F.obj X.obj.2) ≫
          (G.obj h.denom ◁ e.hom.app X.obj.2 ≫
            (Functor.LaxMonoidal.μ G h.denom X.obj.2 ≫ G.map h.map.2)) =
          (Functor.LaxMonoidal.μ F h.denom X.obj.2 ≫ F.map h.map.2) ≫ e.hom.app Y.obj.2
        simpa only [Category.assoc] using
          monoidalMap_naturality_component e.hom h.denom X.obj.2 Y.obj.2 h.map.2)

/-- Identity acts identically on the original completion category. -/
lemma monoidalMap_id : monoidalMap (𝟭 C) = 𝟭 (Localization C C) := by
  refine CategoryTheory.Functor.ext (F := _) (G := _) (fun _ ↦ rfl) ?_
  intro X Y h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  induction h using Quotient.inductionOn with
  | _ h =>
    change ActionLocalization.mkHom (C := C) (X := X.obj) (Y := Y.obj)
      ⟨h.denom, (𝟙 _ ≫ h.map.1, 𝟙 _ ≫ h.map.2)⟩ = _
    simp only [Category.id_comp]
    rfl

/-- Composition uses the actual composite tensorator on each representative. -/
lemma monoidalMap_comp (F : C ⥤ D) [F.Monoidal] (G : D ⥤ E) [G.Monoidal] :
    monoidalMap F ⋙ monoidalMap G = monoidalMap (F ⋙ G) := by
  refine CategoryTheory.Functor.ext (F := _) (G := _) (fun _ ↦ rfl) ?_
  intro X Y h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  induction h using Quotient.inductionOn with
  | _ h =>
    change ActionLocalization.mkHom (C := E)
      (X := (G.obj (F.obj X.obj.1), G.obj (F.obj X.obj.2)))
      (Y := (G.obj (F.obj Y.obj.1), G.obj (F.obj Y.obj.2)))
      ⟨G.obj (F.obj h.denom),
      (Functor.LaxMonoidal.μ G _ _ ≫ G.map (Functor.LaxMonoidal.μ F _ _ ≫ F.map h.map.1),
       Functor.LaxMonoidal.μ G _ _ ≫ G.map (Functor.LaxMonoidal.μ F _ _ ≫ F.map h.map.2))⟩ = _
    simp only [Functor.map_comp]
    change ActionLocalization.mkHom _ = ActionLocalization.mkHom _
    congr 1
    apply congrArg (ActionLocalization.HomRep.mk _)
    apply Prod.ext <;> exact (Category.assoc _ _ _).symm

end CategoryTheory.GroupCompletion
