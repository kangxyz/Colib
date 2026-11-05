/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Homology.HomotopyCategory.SingleConeLift

open CategoryTheory CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C)
  {K : CochainComplex C ℤ} (b : K.X 0 ⟶ S.X₂) (c : K.X (-1) ⟶ S.X₁)
  (hc : K.d (-2) (-1) ≫ c = 0) (h : c ≫ S.f = K.d (-1) 0 ≫ b)

example (π : K ⟶ (singleFunctor C 0).obj S.X₃)
    (hπ : π.f 0 = b ≫ S.g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃).inv) :
    S.singleConeLift b c hc h ≫ mappingCone.descShortComplex (S.map (singleFunctor C 0)) = π :=
  S.singleConeLift_comp_desc b c hc h π hπ

example :
    S.singleConeLift b c hc h ≫ (mappingCone.triangle ((singleFunctor C 0).map S.f)).mor₃ =
      -(Cocycle.equivHomShift.symm
        (Cocycle.toSingleMk c (show (-1 : ℤ) + 1 = 0 by decide) (-2) (by decide) hc)) := by
  rw [S.singleConeLift_comp_triangle_mor₃, map_neg]
