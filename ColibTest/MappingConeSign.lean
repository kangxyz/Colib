/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Homology.HomotopyCategory.MappingCone

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  {K F G : CochainComplex C ℤ} (φ : F ⟶ G)
  (α : Cocycle K F 1) (β : Cochain K G 0)
  (h : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0)

example :
    CochainComplex.mappingCone.lift φ α β h ≫
        (CochainComplex.mappingCone.triangle φ).mor₃ =
      -(Cocycle.equivHomShift.symm α) := by
  rw [CochainComplex.mappingCone.lift_comp_triangle_mor₃, map_neg]
