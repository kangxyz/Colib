/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.InfinityResidueMap
import StacksFrontier.AlgebraicGeometry.Chow.MilnorNorm.SimpleNorm

/-!
Uncompiled consumers of native infinity-residue naturality, including its exact degree and sign.
These do not establish a simple-norm base-change formula or a field-norm tower law.
-/

noncomputable section

open Polynomial Stacks.Chow

universe u

variable {k K : Type u} [Field k] [Field K]

example (φ : k →+* K) (y : MilnorKRing (RatFunc k)) :
    MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc K)
        (irreducible_algebraMap_X (k := K))
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y)) =
      milnorKRingMap
        (IsLocalRing.ResidueField.map
          (Localization.localRingHom (Ideal.span ({X} : Set k[X]))
            (Ideal.span ({X} : Set K[X])) (Polynomial.mapRingHom φ)
            (Polynomial.span_X_comap_mapRingHom φ).symm))
        (MilnorKShift.shift (dvrMilnorShiftMap (F := RatFunc k)
          (irreducible_algebraMap_X (k := k)) y)) :=
  dvrMilnorShiftMap_shift_mapRingHom_at_origin φ y

example (φ : k →+* K) (y : MilnorKRing (RatFunc k)) :
    infinityResidueRing K
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) y) =
      milnorKRingMap φ (infinityResidueRing k y) :=
  infinityResidueRing_mapRingHom φ y

example (φ : k →+* K) :
    (infinityResidueRing K).comp
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))).toAddMonoidHom =
      (milnorKRingMap φ).toAddMonoidHom.comp (infinityResidueRing k) :=
  infinityResidueRing_comp_milnorKRingMap_mapRingHom φ

example (φ : k →+* K) (n : ℕ) (y : MilnorKTheory (RatFunc k) (n + 1)) :
    infinityResidue (k := K) n
        (milnorKTransport (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) (n + 1) y) =
      milnorKTransport φ n (infinityResidue (k := k) n y) :=
  infinityResidue_milnorKTransport_mapRingHom φ n y

-- Coefficient extension preserves the native negative-degree formula at infinity.
example (φ : k →+* K) {f : k[X]} (hf : f.Monic) :
    infinityResidueRing K
        (milnorKRingMap (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))
          (milnorKSymbol (RatFunc k) (polyUnit hf.ne_zero))) =
      (-(f.natDegree : ℤ)) • (1 : MilnorKRing K) := by
  rw [infinityResidueRing_mapRingHom, infinityResidueRing_milnorKSymbol_monic hf,
    map_zsmul, map_one]

end
