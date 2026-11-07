/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Cofinality.GradedKZeroSequence
public import Colib.KTheory.Waldhausen.Cofinality.DenseKEquivalence

/-! # The original dense-subcategory K-zero tail and actual complement classes

Every common-complement class has an actual original object representative.
The exact grading range therefore identifies with the full complement-class
group. The original inclusion has precisely the kernel of the resulting
original K-zero homomorphism, which is genuinely surjective onto these classes.

Implementation provenance: `Quillen/Waldhausen/Cofinality/DenseKZero.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.Fibration


noncomputable section
open Topology SSet
open CategoryTheory CategoryTheory.Limits
universe u
namespace CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
open Fibration
variable {C : Type u} [SmallCategory C] {W : Structure C} [HasBinaryCoproducts C]
  {P : ObjectProperty C} (h : DenseCofiberData W P)

/-- The exact realized grade subgroup is the entire actual common-complement class group. -/
def classRangeEquiv (T : FunctorialFactorization W) : h.grading.valueRange T ≃+ h.Classes :=
  AddEquiv.ofBijective (h.grading.valueRange T).subtype
    ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, h.classOf_surjective x⟩, rfl⟩⟩

variable (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))

/-- The original fine K-zero homomorphism to the actual categorical complement classes. -/
def classKZeroMap : W.K 0 →* Multiplicative h.Classes :=
  (h.classRangeEquiv D.sourceFactorization).toMultiplicative.toMonoidHom.comp
    (h.grading.gradeKZeroMap D)

/-- Passing from realized range to actual complement classes does not change the original kernel. -/
theorem classKZeroMap_ker : (h.classKZeroMap D).ker = (KMap (changeWeak_exact h.grading.nested)
    0).ker := by
  rw [← h.grading.gradeKZeroMap_ker D]
  ext x
  change (h.classRangeEquiv D.sourceFactorization).toMultiplicative
    (h.grading.gradeKZeroMap D x) = 1 ↔ _
  exact (h.classRangeEquiv D.sourceFactorization).toMultiplicative.map_eq_one_iff

variable (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)
include hs

/-- Every actual complement class has an original fine K-zero preimage. -/
theorem classKZeroMap_surjective : Function.Surjective (h.classKZeroMap D) :=
  (h.classRangeEquiv D.sourceFactorization).toMultiplicative.surjective.comp
    (h.grading.gradeKZeroMap_surjective D hs)

/-- The literal original full-inclusion image is exactly the actual complement-class kernel. -/
theorem range_inclusion_KZero_eq_classKernel : (KMap h.inclusion_exact 0).range =
    (h.classKZeroMap D).ker := by
  rw [h.classKZeroMap_ker D]
  exact h.range_inclusion_KMap D hs 0

/-- Genuine categorical density gives the exact K-zero tail with its actual class-group endpoint. -/
theorem classKZero_exact : Function.Injective (KMap h.inclusion_exact 0) ∧
    (KMap h.inclusion_exact 0).range = (h.classKZeroMap D).ker ∧
    Function.Surjective (h.classKZeroMap D) :=
  ⟨h.inclusion_KMap_injective D hs 0, h.range_inclusion_KZero_eq_classKernel D hs,
    h.classKZeroMap_surjective D hs⟩

end CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
