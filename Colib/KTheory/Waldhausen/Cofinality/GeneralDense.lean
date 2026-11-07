/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Cofinality.GeneralGraded
public import Colib.KTheory.Waldhausen.Cofinality.DenseKEquivalence

/-! # Genuine dense cofinality on the unchanged category in its original universes

The actual membership equivalence already preserves the original objects,
arrows and inclusion. General-universe graded vanishing and the genuine
original fibration therefore give the same positive and degree-zero results
without transporting or replacing the original dense subcategory.

Implementation provenance: `Quillen/Waldhausen/Cofinality/GeneralDense.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen.Fibration


noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
open Fibration
variable {C : Type u} [Category.{v} C] {W : Structure C} [HasBinaryCoproducts C]
  {P : ObjectProperty C} (h : DenseCofiberData W P)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)
include D hs

/-- The original inclusion is injective in every degree, including the genuine K-zero group. -/
@[colib_tag "COL-0268"]
theorem inclusion_KMap_injective_general (n : ℕ) : Function.Injective (KMap h.inclusion_exact n)
    := by
  let he := KEquivOfExactEquivalence h.zeroGradeEquivalence h.toZeroGrade_exact
    h.fromZeroGrade_exact n
  rw [← h.inclusion_KMap_factor n]
  exact (h.grading.zeroGrade_KMap_injective_general D hs n).comp he.injective

/-- Positive original K-classes have genuine original subcategory preimages. -/
theorem inclusion_KMap_succ_bijective_general (n : ℕ) :
    Function.Bijective (KMap h.inclusion_exact (n + 1)) := by
  let he := KEquivOfExactEquivalence h.zeroGradeEquivalence h.toZeroGrade_exact
    h.fromZeroGrade_exact (n + 1)
  rw [← h.inclusion_KMap_factor (n + 1)]
  exact (h.grading.zeroGradeKEquivGeneral D hs n).bijective.comp he.bijective

/-- The actual dense full inclusion supplies the positive K-equivalence itself. -/
@[colib_tag "COL-0268", colib_ref "ThomasonTrobaugh1990"
  "Exercise 1.10.2, p. 277" "adaptation"
  "Dense cofiber-closed inclusion induces the original positive K-equivalence with \
    explicit joint-cylinder data"]
def inclusionKEquivGeneral (n : ℕ) : h.waldhausenStructure.K (n + 1) ≃* W.K (n + 1) :=
  MulEquiv.ofBijective (KMap h.inclusion_exact (n + 1)) (h.inclusion_KMap_succ_bijective_general
    D hs n)

/-- This equivalence's forward map remains precisely the original full-inclusion KMap. -/
@[simp] theorem inclusionKEquivGeneral_apply (n : ℕ) (a : h.waldhausenStructure.K (n + 1)) :
    h.inclusionKEquivGeneral D hs n a = KMap h.inclusion_exact (n + 1) a := rfl

/-- The range of the literal original inclusion is exactly the kernel of changing weak classes. -/
theorem range_inclusion_KMap_general (n : ℕ) :
    (KMap h.inclusion_exact n).range = (KMap (changeWeak_exact h.grading.nested) n).ker := by
  let he := KEquivOfExactEquivalence h.zeroGradeEquivalence h.toZeroGrade_exact
    h.fromZeroGrade_exact n
  have hsurj : Function.Surjective (KMap h.toZeroGrade_exact n) := he.surjective
  rw [← h.inclusion_KMap_factor n, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj,
    ← MonoidHom.range_eq_map]
  exact range_acyclicInclusion_eq_ker_changeWeak_of_weak h.grading.nested
    (h.grading.canonicalFiberMap_isWeakHomotopyEquivalence D hs) n

/-- The full-subcategory K-zero tail retains the true remaining endpoint and only its proved
image. -/
@[colib_tag "COL-0268", colib_ref "ThomasonTrobaugh1990"
  "Theorem 1.10.1 and Exercise 1.10.2, pp. 275-277" "adaptation"
  "The original K-zero inclusion is injective with image the change-weak kernel and \
    surjective actual coarse endpoint"]
theorem inclusion_KZero_exact_general :
    Function.Injective (KMap h.inclusion_exact 0) ∧
    (KMap h.inclusion_exact 0).range = (KMap (changeWeak_exact h.grading.nested) 0).ker ∧
    Function.Surjective (KMap (changeWeak_exact h.grading.nested) 0) :=
  ⟨h.inclusion_KMap_injective_general D hs 0, h.range_inclusion_KMap_general D hs 0,
    (h.grading.zeroGrade_KZero_exact_general D hs).2.2⟩

end CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
