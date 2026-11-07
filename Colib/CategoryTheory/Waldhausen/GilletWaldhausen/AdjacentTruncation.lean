/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.AdjacentTruncation
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationCoherence
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationLayer
public import Colib.CategoryTheory.Waldhausen.GilletWaldhausen.TruncationCofibrationSequence

/-! # The actual adjacent-truncation cofibration sequence

The natural coherence iso turns the internal truncation sequence of
truncLE (n+1) into the actual adjacent sequence
truncLE n → truncLE (n+1) → identityDisk n (cycles (n+1)).
All three functors are genuinely exact, and the relative-cofibration
condition is proved by the generic exact-functor sequence theorem.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/AdjacentTruncation.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open CochainComplex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace CategoryTheory.Waldhausen.GilletWaldhausen

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The actual adjacent sequence satisfies every structural additivity
hypothesis with isomorphism weak equivalences. -/
theorem adjacentTruncation_isCofibrationSequence (n : ℤ) :
    Additivity.IsCofibrationSequence (ofExactCategory (boundedAcyclicExactStructure P))
      (ofExactCategory (boundedAcyclicExactStructure P))
      (adjacentTruncationInclusion P n) (adjacentTruncationProjection P n) :=
  exactFunctorSequence_isCofibrationSequence _ _ _ _ (adjacentTruncation_comp_zero P n)
    (adjacentTruncation_conflation P n)
    (boundedAcyclicTruncLEExactFunctor P n) (boundedAcyclicTruncLEExactFunctor P (n + 1))
    (oneStepCycleDiskExactFunctor P n) rfl rfl rfl

/-- The same actual adjacent sequence with genuine quasi-isomorphisms. -/
theorem adjacentTruncation_isCofibrationSequence_quasiIso (n : ℤ) :
    Additivity.IsCofibrationSequence (complexSubcategory (boundedAcyclic P))
      (complexSubcategory (boundedAcyclic P))
      (adjacentTruncationInclusion P n) (adjacentTruncationProjection P n) where
  exactF := boundedAcyclicExactFunctor_waldhausenExact P (boundedAcyclicTruncLEExactFunctor P n)
  exactG := boundedAcyclicExactFunctor_waldhausenExact P (boundedAcyclicTruncLEExactFunctor P (n
    + 1))
  exactH := boundedAcyclicExactFunctor_waldhausenExact P (oneStepCycleDiskExactFunctor P n)
  cofibration := {
    app_cof := (adjacentTruncation_isCofibrationSequence P n).cofibration.app_cof
    relative_cof f hf := (adjacentTruncation_isCofibrationSequence P n).cofibration.relative_cof
      f hf }
  cofiber := (adjacentTruncation_isCofibrationSequence P n).cofiber

end CategoryTheory.Waldhausen.GilletWaldhausen
