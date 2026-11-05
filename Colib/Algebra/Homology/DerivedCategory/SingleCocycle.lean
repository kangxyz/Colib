/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.HomotopyCategory.SingleConeLift
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Computing a connecting morphism after an augmentation

A degree-zero lift of an augmentation and its degree-one boundary give a
cocycle formula for the standard connecting morphism. The negative sign is
inherited from Mathlib's actual cone triangle, not chosen by convention here.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex CochainComplex.HomComplex

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {S : ShortComplex C} (hS : S.ShortExact) {K : CochainComplex C ℤ}
  (b : K.X 0 ⟶ S.X₂) (c : K.X (-1) ⟶ S.X₁)
  (hc : K.d (-2) (-1) ≫ c = 0) (h : c ≫ S.f = K.d (-1) 0 ≫ b)
  (π : K ⟶ (singleFunctor C 0).obj S.X₃)
  (hπ : π.f 0 = b ≫ S.g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃).inv)

include h hπ in
/-- Pulling the connecting morphism back along an augmentation gives the negative cocycle. -/
theorem map_comp_singleδ_eq_neg_cocycle :
    DerivedCategory.Q.map π ≫ hS.singleδ =
      -(DerivedCategory.Q.map (Cocycle.equivHomShift.symm
          (Cocycle.toSingleMk c (show (-1 : ℤ) + 1 = 0 by decide) (-2) (by decide) hc)) ≫
        (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app ((singleFunctor C 0).obj S.X₁)) := by
  rw [← S.singleConeLift_comp_desc b c hc h π hπ, Functor.map_comp, Category.assoc]
  change DerivedCategory.Q.map (S.singleConeLift b c hc h) ≫
    (DerivedCategory.Q.map (mappingCone.descShortComplex (S.map (singleFunctor C 0))) ≫
      DerivedCategory.triangleOfSESδ (hS.map_of_exact (HomologicalComplex.single C (.up ℤ) 0))) = _
  rw [DerivedCategory.descShortComplex_triangleOfSESδ]
  dsimp only [ShortComplex.map_f, ShortComplex.map_X₁]
  rw [← Category.assoc]
  erw [← Functor.map_comp, S.singleConeLift_comp_triangle_mor₃, map_neg,
    Functor.map_neg, Preadditive.neg_comp]

end CategoryTheory.ShortComplex.ShortExact
