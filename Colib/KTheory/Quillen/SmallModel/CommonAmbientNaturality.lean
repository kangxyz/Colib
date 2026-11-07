/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.SmallModel.Exact
public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.KTheory.Quillen.Map.NaturalIso
public import Colib.KTheory.Quillen.Map.CommonAmbient
public import Colib.CategoryTheory.QConstruction.ZeroEndomorphisms

/-!
Implementation provenance: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd,
`Quillen/CategoryTheory/SmallModel/CommonAmbientNaturality.lean`.

# Naturality of the original small-model comparison in a common universe

The small-model equivalence has its genuine unit square with every exact
functor. Passing that square to Q and applying the original zero normalizations
gives a based homotopy: the zero Q-vertex has only its identity endomorphism.
This proves naturality of the existing mixed-universe comparison map, without
redefining it by transport.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
universe u v

namespace CategoryTheory

/-- A natural isomorphism between functors preserving the chosen vertices
induces equality of the based homotopy maps when the target vertex has only
one endomorphism. The homotopy is the actual realized nerve cylinder. -/
theorem piMap_classifying_eq_of_iso_of_subsingleton
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    {F G : C ⥤ D} (e : F ≅ G) (c : C) (d : D) [Subsingleton (d ⟶ d)]
    (hF : F.obj c = d) (hG : G.obj c = d)
    (hbF : classifyingSpaceMap F (classifyingSpacePoint c) = classifyingSpacePoint d)
    (hbG : classifyingSpaceMap G (classifyingSpacePoint c) = classifyingSpacePoint d)
    (n : ℕ) :
    HomotopyGroup.piMap n (classifyingSpaceMap F).hom hbF =
      HomotopyGroup.piMap n (classifyingSpaceMap G).hom hbG := by
  have he : e.hom.app c = eqToHom (hF.trans hG.symm) := by
    have : Subsingleton (F.obj c ⟶ G.obj c) := by rw [hF, hG]; infer_instance
    exact Subsingleton.elim _ _
  let H := classifyingSpaceNaturalTransformationBasedHomotopy
    e.hom c (hF.trans hG.symm) he
  exact HomotopyGroup.piMap_eq_of_based_homotopy n hbF hbG H.toHomotopy
    (fun t ↦ (H.prop t (classifyingSpacePoint c) (Set.mem_singleton _)).trans hbF)

end CategoryTheory

namespace CategoryTheory.ExactCategory.ExactFunctor

variable {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  [EssentiallySmall.{max u v} C] [EssentiallySmall.{max u v} D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The actual unit of the target small-model equivalence identifies the
two exact functors in the comparison square. -/
def smallModelToOriginalNaturalityIso (F : ExactFunctor EC ED) :
    (F.smallModel.comp ED.smallModelToOriginal).toFunctor ≅
      (EC.smallModelToOriginal.comp F).toFunctor :=
  Functor.isoWhiskerLeft ((equivSmallModel.{max u v} C).inverse ⋙ F.toFunctor)
    (equivSmallModel.{max u v} D).unitIso.symm

/-- The actual normalized Q-functors form the small-model naturality square. -/
def smallModelNormalizedQSquareIso (F : ExactFunctor EC ED) :
    F.smallModel.normalizedQ ⋙ ED.smallModelToOriginal.commonAmbientNormalizedQ ≅
      EC.smallModelToOriginal.commonAmbientNormalizedQ ⋙ F.normalizedQ :=
  (Functor.isoWhiskerRight
    (rebaseFunctorIso F.smallModel.mapQ _ _ _).symm
    ED.smallModelToOriginal.commonAmbientNormalizedQ ≪≫
    Functor.isoWhiskerLeft F.smallModel.mapQ
      (rebaseFunctorIso ED.smallModelToOriginal.mapQ _ _ _).symm) ≪≫
    (eqToIso (F.smallModel.mapQ_comp ED.smallModelToOriginal)).symm ≪≫
    mapQIso (smallModelToOriginalNaturalityIso F) ≪≫
    eqToIso (EC.smallModelToOriginal.mapQ_comp F) ≪≫
    (Functor.isoWhiskerRight
      (rebaseFunctorIso EC.smallModelToOriginal.mapQ _ _ _) F.mapQ ≪≫
      Functor.isoWhiskerLeft EC.smallModelToOriginal.commonAmbientNormalizedQ
        (rebaseFunctorIso F.mapQ _ _ _))

/-- Naturality of the original public small-model-to-original comparison.
All realizations stay in the same object universe, despite the different
hom universes of the small model and the original categories. -/
theorem smallModelToOriginal_commonAmbientKMap_naturality
    (F : ExactFunctor EC ED) (n : ℕ) :
    (ED.smallModelToOriginal.commonAmbientKMap n).comp (F.smallKMap n) =
      (F.KMap n).comp (EC.smallModelToOriginal.commonAmbientKMap n) := by
  let A := F.smallModel.normalizedQ
  let B := ED.smallModelToOriginal.commonAmbientNormalizedQ
  let C' := EC.smallModelToOriginal.commonAmbientNormalizedQ
  let D' := F.normalizedQ
  have hA : A.obj EC.smallModel.qZero = ED.smallModel.qZero :=
    rebaseFunctor_obj_base _ _ _ _
  have hB : B.obj ED.smallModel.qZero = ED.qZero :=
    rebaseFunctor_obj_base _ _ _ _
  have hC : C'.obj EC.smallModel.qZero = EC.qZero :=
    rebaseFunctor_obj_base _ _ _ _
  have hD : D'.obj EC.qZero = ED.qZero := rebaseFunctor_obj_base _ _ _ _
  have hAB : (A ⋙ B).obj EC.smallModel.qZero = ED.qZero :=
    (congrArg B.obj hA).trans hB
  have hCD : (C' ⋙ D').obj EC.smallModel.qZero = ED.qZero :=
    (congrArg D'.obj hC).trans hD
  have hbAB : classifyingSpaceMap (A ⋙ B) EC.smallModel.kBasepoint = ED.kBasepoint := by
    rw [classifyingSpaceMap_comp, TopCat.comp_app]
    exact (congrArg (classifyingSpaceMap B) F.smallModel.normalizedQ_map_point).trans
      ED.smallModelToOriginal.commonAmbientNormalizedQ_map_point
  have hbCD : classifyingSpaceMap (C' ⋙ D') EC.smallModel.kBasepoint = ED.kBasepoint := by
    rw [classifyingSpaceMap_comp, TopCat.comp_app]
    exact (congrArg (classifyingSpaceMap D')
      EC.smallModelToOriginal.commonAmbientNormalizedQ_map_point).trans F.normalizedQ_map_point
  have h := piMap_classifying_eq_of_iso_of_subsingleton
    (smallModelNormalizedQSquareIso F) EC.smallModel.qZero ED.qZero
    hAB hCD hbAB hbCD n
  apply MonoidHom.ext
  intro x
  have hx := DFunLike.congr_fun h x
  change HomotopyGroup.map (classifyingSpaceMap (A ⋙ B)).hom hbAB x =
    HomotopyGroup.map (classifyingSpaceMap (C' ⋙ D')).hom hbCD x at hx
  simp only [classifyingSpaceMap_comp, TopCat.hom_comp] at hx
  rw [HomotopyGroup.map_comp _ F.smallModel.normalizedQ_map_point _
      ED.smallModelToOriginal.commonAmbientNormalizedQ_map_point,
    HomotopyGroup.map_comp _ EC.smallModelToOriginal.commonAmbientNormalizedQ_map_point _
      F.normalizedQ_map_point] at hx
  exact hx

end CategoryTheory.ExactCategory.ExactFunctor

namespace CategoryTheory
end CategoryTheory
