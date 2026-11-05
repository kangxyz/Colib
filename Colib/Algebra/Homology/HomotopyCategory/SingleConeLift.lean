/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-!
# A cone lift from a degree-one cocycle and an augmentation lift

The construction uses the native mapping cone and single complexes. Its two
projection formulas retain the augmentation and the sign of the connecting
morphism, without choosing another resolution model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C] (S : ShortComplex C)
  {K : CochainComplex C ℤ}
  (b : K.X 0 ⟶ S.X₂) (c : K.X (-1) ⟶ S.X₁)
  (hc : K.d (-2) (-1) ≫ c = 0)
  (h : c ≫ S.f = K.d (-1) 0 ≫ b)

include h in
/-- The degree-one cocycle and degree-zero lift satisfy the native cone lift relation. -/
theorem singleConeLift_relation :
    δ 0 1 (Cochain.toSingleMk b (by simp)) +
      (Cocycle.toSingleMk c (show (-1 : ℤ) + 1 = 0 by decide) (-2) (by decide) hc).1.comp
        (Cochain.ofHom ((singleFunctor C 0).map S.f)) (add_zero 1) = 0 := by
  rw [Cocycle.toSingleMk_coe, Cochain.δ_toSingleMk _ _ 1 (-1) (by decide),
    ← Cochain.toSingleMk_postcomp, h]
  simp

/-- A compatible pair of maps gives a morphism to the native cone of the single differential. -/
def singleConeLift : K ⟶ mappingCone ((singleFunctor C 0).map S.f) :=
  mappingCone.lift _
    (Cocycle.toSingleMk c (show (-1 : ℤ) + 1 = 0 by decide) (-2) (by decide) hc)
    (Cochain.toSingleMk b (by simp)) (S.singleConeLift_relation b c hc h)

/-- Composing the lift with the standard cone projection retains the augmentation exactly. -/
theorem singleConeLift_comp_desc (π : K ⟶ (singleFunctor C 0).obj S.X₃)
    (hπ : π.f 0 = b ≫ S.g ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 S.X₃).inv) :
    S.singleConeLift b c hc h ≫ mappingCone.descShortComplex (S.map (singleFunctor C 0)) = π := by
  apply HomologicalComplex.to_single_hom_ext
  change (S.singleConeLift b c hc h).f 0 ≫
    (mappingCone.descShortComplex (S.map (singleFunctor C 0))).f 0 = π.f 0
  dsimp only [singleConeLift, mappingCone.descShortComplex, ShortComplex.map_f, ShortComplex.map_g]
  rw [mappingCone.lift_desc_f _ _ _ _ _ _ _ 0 1 (by decide)]
  simp only [Cochain.zero_v, Limits.comp_zero, zero_add, Cochain.toSingleMk_v]
  rw [hπ]
  simp [singleFunctor, singleFunctors, Category.assoc, HomologicalComplex.single_map_f_self]

/-- The third cone arrow is the negative of the specified degree-one cocycle. -/
theorem singleConeLift_comp_triangle_mor₃ :
    S.singleConeLift b c hc h ≫ (mappingCone.triangle ((singleFunctor C 0).map S.f)).mor₃ =
      Cocycle.equivHomShift.symm
        (-(Cocycle.toSingleMk c (show (-1 : ℤ) + 1 = 0 by decide) (-2) (by decide) hc)) :=
  mappingCone.lift_comp_triangle_mor₃ _ _ _ _

end CategoryTheory.ShortComplex
