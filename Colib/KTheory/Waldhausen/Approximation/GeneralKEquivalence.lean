/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Approximation.KEquivalence
public import Colib.KTheory.Waldhausen.AsSmall.Approximation

/-! # Original S/K approximation with independent object and hom universes

The actual approximation and joint-cylinder data pass to the existing
common-universe model. Its proved approximation conclusion then transfers
back through the strictly natural original S-homeomorphism square. The
original realization map and canonical K-homomorphism remain unchanged.

Implementation provenance:
`Quillen/Waldhausen/Approximation/GeneralKEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat SSet
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}

namespace HasApproximationProperty
variable (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))
include h J

/-- Approximation for the original realization with independent object and
morphism universes, retaining the actual exact functor and map. -/
@[colib_tag "COL-0256", colib_ref "Waldhausen1985" "Theorem 1.6.7, p. 354" "adaptation"
  "The original realization map is weakly equivalent under App1/App2 and exact joint-cylinder data"]
theorem deloopingMap_isWeakHomotopyEquivalence_general :
    IsWeakHomotopyEquivalence (deloopingMap hF).hom :=
  deloopingMap_isWeakHomotopyEquivalence_of_asSmall hF
    (h.asSmall.deloopingMap_isWeakHomotopyEquivalence hF.asSmall J.reflexiveAsSmall)

/-- The original canonical K-map is bijective for arbitrary object/hom universes. -/
theorem KMap_bijective_general (n : ℕ) : Function.Bijective (Waldhausen.KMap hF n) :=
  KMap_bijective_of_isWeakHomotopyEquivalence hF
    (deloopingMap_isWeakHomotopyEquivalence_general h hF J) n

/-- The two-universe approximation equivalence retains the original canonical K-map. -/
@[colib_tag "COL-0256", colib_ref "quillen"
  "Quillen/Waldhausen/Approximation/GeneralKEquivalence.lean, KEquivGeneral" "adaptation"
  "The canonical original KMap is the forward map in every nonnegative degree"]
def KEquivGeneral (n : ℕ) : W.K n ≃* V.K n :=
  MulEquiv.ofBijective (Waldhausen.KMap hF n) (KMap_bijective_general h hF J n)

/-- The equivalence retains the literal original canonical K-homomorphism. -/
@[simp] theorem KEquivGeneral_coe (n : ℕ) :
    (↑(KEquivGeneral h hF J n) : W.K n →* V.K n) = Waldhausen.KMap hF n := rfl


end HasApproximationProperty
end CategoryTheory.Waldhausen
