/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.CanonicalMap

public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedDeformationMap
public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedSumMap
public import Colib.KTheory.Waldhausen.WeakGridBasedHomotopy

/-! # Exact chosen-zero values of all normalized deformation endpoints

Implementation provenance: `Quillen/Waldhausen/Additivity/NormalizedZeroMaps.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open SSet.MixedOrdinalCylinder
open scoped Simplicial
universe u v

namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) {F G : C ⥤ D} (a : F ⟶ G)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)
variable (hc : IsCofibrationTransformation W a V)

/-- A diagram whose objects are literally the chosen zero is the actual
constant zero diagram; zero uniqueness supplies all arrow identities. -/
theorem diagram_eq_const_of_zero {J : Type*} [Category J] (A : J ⥤ D)
    (h : ∀ x, A.obj x = W.zero) : A = (Functor.const J).obj W.zero := by
  refine CategoryTheory.Functor.ext h ?_
  intro x y f
  exact (W.isZero.of_iso (eqToIso (h y))).eq_of_tgt _ _

/-- Every cut of the normalized mixed deformation sends the constant zero
input to exactly the chosen zero diagram, not merely an isomorphic one. -/
theorem normalizedMixedMap_zero_grid (n m : SimplexCategoryᵒᵖ) (φ : Cut n.unop) :
    ((normalizedMixedMap V W a hF hG hc).app n).app m
      ⟨φ, zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (mixedOrdinal φ)) m⟩ =
        zeroSimplex₂ W.cof W.weq W.zero W.isZero n m := by
  apply Subtype.ext
  exact diagram_eq_const_of_zero W _
    (fun x ↦ normalizedIntervalDiagram_zero_obj V W a hF hG hc _ _ _ x)

/-- The identity endpoint preserves the actual chosen zero diagram. -/
theorem normalizedIdentityMap_zero (n m : SimplexCategoryᵒᵖ) :
    ((normalizedIdentityMap V W a hF hG hc).app n).app m
      (zeroSimplex₂ V.cof V.weq V.zero V.isZero n m) =
        zeroSimplex₂ W.cof W.weq W.zero W.isZero n m := by
  apply Subtype.ext
  exact diagram_eq_const_of_zero W _
    (fun x ↦ normalizedIntervalDiagram_zero_obj V W a hF hG hc _ _ _ x)

/-- The separated endpoint preserves the actual chosen zero diagram. -/
theorem normalizedSeparatedMap_zero (n m : SimplexCategoryᵒᵖ) :
    ((normalizedSeparatedMap V W a hF hG hc).app n).app m
      (zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (SSet.OrdinalSubdivision.δ.obj n.unop)) m) =
        zeroSimplex₂ W.cof W.weq W.zero W.isZero n m := by
  apply Subtype.ext
  exact diagram_eq_const_of_zero W _
    (fun x ↦ normalizedIntervalDiagram_zero_obj V W a hF hG hc _ _ _ x)

/-- The canonically rebased middle map sends every constant-zero grid to
exactly the chosen target zero. -/
theorem rebasedGridMap_zero (n m : SimplexCategoryᵒᵖ) :
    ((bisimplicialSSetMap V.cof V.weq hG.rebase).app n).app m
      (zeroSimplex₂ V.cof V.weq V.zero V.isZero n m) =
        zeroSimplex₂ W.cof W.weq W.zero W.isZero n m := by
  apply Subtype.ext
  exact diagram_eq_const_of_zero W _
    (fun _ ↦ CategoryTheory.rebaseFunctor_obj_base G V.zero W.zero ((hG.zero
      V.isZero).iso W.isZero))

variable [HasBinaryCoproducts D] {H : C ⥤ D}
variable (hH : IsExact V.cof V.weq W.cof W.weq H)

/-- The normalized common endpoint preserves the same actual chosen zero. -/
theorem normalizedSumMap_zero (n m : SimplexCategoryᵒᵖ) :
    ((normalizedSumMap V W hH hF).app n).app m
      (zeroSimplex₂ V.cof V.weq V.zero V.isZero (op (SSet.OrdinalSubdivision.δ.obj n.unop)) m) =
        zeroSimplex₂ W.cof W.weq W.zero W.isZero n m := by
  apply Subtype.ext
  exact diagram_eq_const_of_zero W _
    (fun x ↦ normalizedSumGrid_zero_obj V W hH hF x)

end CategoryTheory.Waldhausen.Additivity
