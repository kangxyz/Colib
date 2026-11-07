/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakGridTriangle
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformation
public import Colib.CategoryTheory.Waldhausen.SConstruction.Zero

/-!
# Actual based S-construction triangles of weak natural transformations

Three original exact functors and two pointwise weak natural transformations determine a genuine
Δ[2] family. Its three faces are the existing transformation cylinders, including their composite.
Explicit chosen-zero equalities make the entire zero-vertex triangle constant. Iterated structure
compatibility is a separate assertion.

This is a concrete compositional refinement of the natural-weak-equivalence homotopy
background in Thomason–Trobaugh, Sections 1.5.3–1.5.4, pp. 260–261, not a verbatim
statement there. No iterated S-construction or prespectrum theorem is asserted.
-/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/SConstruction/WeakNaturalTransformationTriangle.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (V : Structure C) (W : Structure D) {F G H : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact V.cof V.weq W.cof W.weq G)
  (hH : IsExact V.cof V.weq W.cof W.weq H)
  (η : F ⟶ G) (θ : G ⟶ H)
  (hη : ∀ X, W.weq (η.app X)) (hθ : ∀ X, W.weq (θ.app X))

/-- The actual two-transformation family on the original S-construction. -/
def weakNaturalTransformationTriangle : sSet V.cof V.weq ⊗ Δ[2] ⟶ sSet W.cof W.weq :=
  ((bisimplicialDiagonalIso V).inv ▷ Δ[2]) ≫
    weakGridFamilyTriangle W (bisimplicialSSetMap V.cof V.weq hF)
      (bisimplicialSSetMap V.cof V.weq hG) (bisimplicialSSetMap V.cof V.weq hH)
      (fun _ _ A ↦ whiskerLeft A.1 η) (fun _ _ A ↦ whiskerLeft A.1 θ)
      (fun _ _ A p ↦ hη (A.1.obj p)) (fun _ _ A p ↦ hθ (A.1.obj p))
      (fun _ _ _ ↦ HEq.rfl) (fun _ _ _ ↦ HEq.rfl) ≫ (bisimplicialDiagonalIso W).hom

/-- Every simplex retains the original S-grid and both original transformation components. -/
theorem weakNaturalTransformationTriangle_app_val (n : SimplexCategoryᵒᵖ)
    (z : (sSet V.cof V.weq).obj n × (Δ[2]).obj n) :
    (TypeCat.Hom.hom (X := (sSet V.cof V.weq).obj n × (Δ[2]).obj n)
      ((weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ).app n) z).val =
      nerveTriangleDiagram (whiskerLeft z.1.val η) (whiskerLeft z.1.val θ) z.2.down := rfl

/-- The first face is the existing first-transformation cylinder. -/
theorem weakNaturalTransformationTriangle_first :
    ((𝟙 (sSet V.cof V.weq)) ⊗ₘ SSet.stdSimplex.δ 2) ≫
        weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ =
      weakNaturalTransformationCylinder V W hF hG η hη := by
  ext n z
  apply Subtype.ext
  exact nerveTriangleDiagram_first (whiskerLeft z.1.val η) (whiskerLeft z.1.val θ) z.2.down

/-- The second face is the existing second-transformation cylinder. -/
theorem weakNaturalTransformationTriangle_second :
    ((𝟙 (sSet V.cof V.weq)) ⊗ₘ SSet.stdSimplex.δ 0) ≫
        weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ =
      weakNaturalTransformationCylinder V W hG hH θ hθ := by
  ext n z
  apply Subtype.ext
  exact nerveTriangleDiagram_second (whiskerLeft z.1.val η) (whiskerLeft z.1.val θ) z.2.down

/-- The long face is the existing cylinder of the genuine composite transformation. -/
theorem weakNaturalTransformationTriangle_composite :
    ((𝟙 (sSet V.cof V.weq)) ⊗ₘ SSet.stdSimplex.δ 1) ≫
        weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ =
      weakNaturalTransformationCylinder V W hF hH (η ≫ θ)
        (fun X ↦ W.weq.comp_mem _ _ (hη X) (hθ X)) := by
  ext n z
  apply Subtype.ext
  exact nerveTriangleDiagram_composite (whiskerLeft z.1.val η) (whiskerLeft z.1.val θ) z.2.down

/-- Chosen-zero equalities make the entire original triangle at the zero vertex constant. -/
theorem weakNaturalTransformationTriangle_fixed_zero
    (hF0 : F.obj V.zero = W.zero) (hG0 : G.obj V.zero = W.zero)
    (hH0 : H.obj V.zero = W.zero) :
    SSet.yonedaEquiv.symm (zeroSimplex V.cof V.weq V.zero V.isZero (op ⦋0⦌)) ▷ Δ[2] ≫
        weakNaturalTransformationTriangle V W hF hG hH η θ hη hθ =
      CartesianMonoidalCategory.fst Δ[0] Δ[2] ≫
        SSet.yonedaEquiv.symm (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌)) := by
  ext n z
  apply Subtype.ext
  exact nerveTriangleDiagram_eq_const_of_zero _ _ W.zero W.isZero
    (fun _ ↦ hF0) (fun _ ↦ hG0) (fun _ ↦ hH0) z.2.down

attribute [colib_tag "COL-0275"]
  weakNaturalTransformationTriangle
  weakNaturalTransformationTriangle_first
  weakNaturalTransformationTriangle_second
  weakNaturalTransformationTriangle_composite
  weakNaturalTransformationTriangle_fixed_zero

attribute [colib_ref "ThomasonTrobaugh1990" "Sections 1.5.3-1.5.4, pp. 260-261" "background"
  "Background on weak natural transformations; the explicit simplicial triangle is a refinement"]
  weakNaturalTransformationTriangle

end CategoryTheory.Waldhausen
