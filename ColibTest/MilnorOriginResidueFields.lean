/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.MilnorK.Norm.OriginResidueFields

/-! Uncompiled independent-universe consumers of the actual origin coefficient map. -/

noncomputable section

open Polynomial Stacks.Chow

universe u v

variable {k : Type u} [Field k] {K : Type v} [Field K]

example (φ : k →+* K) :
    (Ideal.span ({X} : Set K[X])).comap (Polynomial.mapRingHom φ) =
      Ideal.span ({X} : Set k[X]) :=
  Polynomial.span_X_comap_mapRingHom φ

example (φ : k →+* K) :
    Localization.localRingHom (Ideal.span ({X} : Set k[X]))
        (Ideal.span ({X} : Set K[X])) (Polynomial.mapRingHom φ)
        (Polynomial.span_X_comap_mapRingHom φ).symm
        (algebraMap k[X] (localRingAtOrigin k) X) =
      algebraMap K[X] (localRingAtOrigin K) X :=
  localRingHom_algebraMap_X φ

example (φ : k →+* K) :
    (residueFieldAtOriginEquiv K).symm.toRingHom.comp
      (IsLocalRing.ResidueField.map
        (Localization.localRingHom (Ideal.span ({X} : Set k[X]))
          (Ideal.span ({X} : Set K[X])) (Polynomial.mapRingHom φ)
          (Polynomial.span_X_comap_mapRingHom φ).symm)) =
      φ.comp (residueFieldAtOriginEquiv k).symm.toRingHom :=
  residueFieldAtOriginEquiv_symm_comp_residueField_map φ

end
