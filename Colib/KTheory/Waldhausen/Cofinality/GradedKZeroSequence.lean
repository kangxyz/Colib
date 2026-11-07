/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Cofinality.GradedKZero
public import Colib.KTheory.Waldhausen.Cofinality.ZeroGrade

/-! # The actual K-zero tail with its original grading-group endpoint

The original change-of-weak-equivalences homomorphism followed by the proved
coarse K-zero identification gives the explicit grade-group homomorphism.
Its kernel and surjectivity follow from the genuine original fibration.

Implementation provenance: `Quillen/Waldhausen/Cofinality/GradedKZeroSequence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.Fibration


noncomputable section
open Topology SSet
open CategoryTheory
universe u
namespace CategoryTheory.Waldhausen.Cofinality.Grading
open Fibration
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))

/-- The genuine original fine K-zero homomorphism to the actual object-value group. -/
def gradeKZeroMap : W.K 0 →* Multiplicative (d.valueRange D.sourceFactorization) :=
  (d.coarseKZeroEquiv D.sourceFactorization).toMonoidHom.comp (KMap (changeWeak_exact d.nested) 0)

/-- The explicit grade endpoint changes neither the actual remaining kernel nor its original
source. -/
theorem gradeKZeroMap_ker : (d.gradeKZeroMap D).ker = (KMap (changeWeak_exact d.nested) 0).ker := by
  ext x
  change d.coarseKZeroEquiv D.sourceFactorization (KMap (changeWeak_exact d.nested) 0 x) = 1 ↔ _
  exact (d.coarseKZeroEquiv D.sourceFactorization).map_eq_one_iff

variable (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)
include hs

/-- Every actual grade-group element is reached under the original K-zero grading map. -/
theorem gradeKZeroMap_surjective : Function.Surjective (d.gradeKZeroMap D) :=
  (d.coarseKZeroEquiv D.sourceFactorization).surjective.comp (d.zeroGrade_KZero_exact D hs).2.2

/-- The original zero-grade K-zero inclusion is precisely the kernel of the explicit grade map. -/
theorem range_zeroGrade_KZero : (KMap (acyclicInclusion_exact d.nested) 0).range =
    (d.gradeKZeroMap D).ker := by
  rw [d.gradeKZeroMap_ker D]
  exact (d.zeroGrade_KZero_exact D hs).2.1

/-- The actual original short exact tail ends in the proved actual value group. -/
theorem gradeKZero_exact : Function.Injective (KMap (acyclicInclusion_exact d.nested) 0) ∧
    (KMap (acyclicInclusion_exact d.nested) 0).range = (d.gradeKZeroMap D).ker ∧
    Function.Surjective (d.gradeKZeroMap D) :=
  ⟨d.zeroGrade_KMap_injective D hs 0, d.range_zeroGrade_KZero D hs, d.gradeKZeroMap_surjective D hs⟩

end CategoryTheory.Waldhausen.Cofinality.Grading
