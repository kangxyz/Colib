/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.QuillenComparison.ComparisonHom
public import Colib.CategoryTheory.Waldhausen.QuillenComparison.ExactNaturality
public import Colib.KTheory.Quillen.Map.ZeroNormalization
public import Colib.KTheory.Waldhausen.Functoriality

/-! # Exact-functor naturality of the original based Q/S homomorphism

Adapted from `Quillen/Waldhausen/QuillenComparison/BasedNaturality.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original functors,
canonical zero isomorphisms and based homotopies.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject Simplicial
universe v u v₁ v₂ u₁ u₂

namespace CategoryTheory.Waldhausen.QuillenComparison

private theorem piMap_of_commuting_square
    {X Y X' Y' : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace X'] [TopologicalSpace Y'] {x : X} {y : Y} {x' : X'} {y' : Y'}
    (n : ℕ) (f : ContinuousMap X Y) (hf : f x = y)
    (g : ContinuousMap X' Y') (hg : g x' = y')
    (a : ContinuousMap X X') (ha : a x = x')
    (b : ContinuousMap Y Y') (hb : b y = y') (h : g.comp a = b.comp f) :
    (HomotopyGroup.piMap n g hg).comp (HomotopyGroup.piMap n a ha) =
      (HomotopyGroup.piMap n b hb).comp (HomotopyGroup.piMap n f hf) := by
  ext z
  refine Quotient.inductionOn z (fun p ↦ ?_)
  apply congrArg Quotient.mk'
  ext t
  exact DFunLike.congr_fun h (p t)

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {EC : ExactCategory.ExactStructure C} {ED : ExactCategory.ExactStructure D}
  (F : ExactCategory.ExactFunctor EC ED)

/-- Strict zero preservation retains the actual constant zero simplex in every degree. -/
theorem sSetMap_zeroSimplex_of_zeroEq
    (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : SimplexCategoryᵒᵖ) :
    (sSetMap F.waldhausenExact).app n
      (zeroSimplex EC.inflation (MorphismProperty.isomorphisms C) (0 : C) (isZero_zero C) n) =
    zeroSimplex ED.inflation (MorphismProperty.isomorphisms D) (0 : D) (isZero_zero D) n := by
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ h) ?_
  intro i j f
  simp [sSetMap, zeroSimplex]

/-- The original subdivided S-map preserves the actual chosen zero vertex. -/
theorem subdivisionExactMap_basepoint_of_zeroEq (h : F.toFunctor.obj (0 : C) = (0 : D)) :
    SSet.toTop.map (SSet.EdgewiseSubdivision.subdivisionFunctor.map (sSetMap F.waldhausenExact))
      (subdivisionBasepoint EC) = subdivisionBasepoint ED := by
  have hz : (SSet.EdgewiseSubdivision.subdivisionFunctor.map (sSetMap F.waldhausenExact)).app
      (op ⦋0⦌) (subdivisionZeroVertex EC) = subdivisionZeroVertex ED :=
    sSetMap_zeroSimplex_of_zeroEq F h _
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (subdivisionZeroVertex EC)) ≫
    SSet.toTop.map
      (SSet.EdgewiseSubdivision.subdivisionFunctor.map (sSetMap F.waldhausenExact))) default = _
  rw [← CategoryTheory.Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  exact congrArg (fun z : (SSet.EdgewiseSubdivision.subdivision
    (sSet ED.inflation (MorphismProperty.isomorphisms D))).obj (op ⦋0⦌) ↦
      SSet.toTop.map (SSet.yonedaEquiv.symm z) default) hz

/-- The map on the original common subdivided source for a strictly based exact functor. -/
def subdivisionExactKMapOfZeroEq (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    SubdivisionK EC n →* SubdivisionK ED n :=
  HomotopyGroup.piMap n
    (SSet.toTop.map
      (SSet.EdgewiseSubdivision.subdivisionFunctor.map (sSetMap F.waldhausenExact))).hom
    (subdivisionExactMap_basepoint_of_zeroEq F h)

/-- The actual endpoint leg commutes with the existing canonical Waldhausen K-map. -/
theorem subdivisionEndpointK_naturality_of_zeroEq
    (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    (subdivisionEndpointK ED n).comp (subdivisionExactKMapOfZeroEq F h n) =
      (Waldhausen.KMap F.waldhausenExact n).comp (subdivisionEndpointK EC n) := by
  rw [Waldhausen.KMap_eq_piMap_of_zeroEq F.waldhausenExact h]
  apply piMap_of_commuting_square
  have hn := congrArg (fun f ↦ (SSet.toTop.map f).hom)
    (SSet.EdgewiseSubdivision.endpointNatTrans.naturality (sSetMap F.waldhausenExact))
  simpa only [CategoryTheory.Functor.map_comp, TopCat.hom_comp,
    SSet.EdgewiseSubdivision.endpointNatTrans, realizationEndpoint,
    CategoryTheory.Functor.id_map, deloopingMap] using! hn

/-- The Q leg commutes with the existing normalized Quillen K-map in the strict-zero case. -/
theorem subdivisionComparisonK_naturality_of_zeroEq
    (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    (subdivisionComparisonK ED n).comp (subdivisionExactKMapOfZeroEq F h n) =
      (F.KMap n).comp (subdivisionComparisonK EC n) := by
  rw [F.KMap_eq_piMap_of_zeroEq h]
  apply piMap_of_commuting_square
  have hn := congrArg (fun f ↦ (SSet.toTop.map f).hom) (comparisonMap_naturality F)
  simpa only [CategoryTheory.Functor.map_comp, TopCat.hom_comp,
    realizationComparison, classifyingSpaceMap] using hn

/-- Inverting only the proved endpoint equivalence gives strict-zero based naturality. -/
theorem comparisonK_naturality_of_zeroEq
    (h : F.toFunctor.obj (0 : C) = (0 : D)) (n : ℕ) :
    (comparisonK ED n).comp (Waldhausen.KMap F.waldhausenExact n) =
      (F.KMap n).comp (comparisonK EC n) := by
  apply (MonoidHom.cancel_right (f := subdivisionEndpointK EC n)
    (subdivisionKEquiv EC n).surjective).mp
  calc
    _ = (comparisonK ED n).comp
        ((subdivisionEndpointK ED n).comp (subdivisionExactKMapOfZeroEq F h n)) := by
      rw [MonoidHom.comp_assoc, subdivisionEndpointK_naturality_of_zeroEq]
    _ = (subdivisionComparisonK ED n).comp (subdivisionExactKMapOfZeroEq F h n) := by
      rw [← MonoidHom.comp_assoc, comparisonK_comp_endpoint]
    _ = (F.KMap n).comp (subdivisionComparisonK EC n) :=
      subdivisionComparisonK_naturality_of_zeroEq F h n
    _ = _ := by rw [MonoidHom.comp_assoc, comparisonK_comp_endpoint]

/-- The canonical Q/S homomorphism commutes with the two original K-map APIs in every
nonnegative degree. Both maps use their actual zero normalization; no extra exactness,
strict-zero preservation or comparison-equivalence hypothesis is imposed. -/
theorem comparisonK_naturality (n : ℕ) :
    (comparisonK ED n).comp (Waldhausen.KMap F.waldhausenExact n) =
      (F.KMap n).comp (comparisonK EC n) := by
  have hS : Waldhausen.KMap F.zeroNormalized.waldhausenExact n =
      Waldhausen.KMap F.waldhausenExact n :=
    (Waldhausen.KMap_eq_of_iso F.waldhausenExact F.zeroNormalized.waldhausenExact
      F.zeroNormalizedIso n).symm
  simpa only [hS, ExactCategory.ExactFunctor.zeroNormalized_KMap] using
    comparisonK_naturality_of_zeroEq F.zeroNormalized F.zeroNormalized_obj_zero n

end CategoryTheory.Waldhausen.QuillenComparison

attribute [colib_tag "COL-0243",
  colib_ref "quillen" "Quillen/Waldhausen/QuillenComparison/BasedNaturality.lean"
    "adaptation" "Based naturality for the two original canonical K-map APIs in every degree"]
  CategoryTheory.Waldhausen.QuillenComparison.comparisonK_naturality_of_zeroEq
  CategoryTheory.Waldhausen.QuillenComparison.comparisonK_naturality
