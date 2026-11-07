/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Cofinality.DenseGrading
public import Colib.KTheory.Waldhausen.Cofinality.ZeroGrade
public import Colib.CategoryTheory.Waldhausen.CofibrationClosedSubcategory
public import Colib.KTheory.Waldhausen.ExactEquivalence

/-! # Genuine dense-subcategory cofinality for the original inclusion

The grading and its exact zero locus are constructed from actual complements,
weak repleteness, extension closure and quotient closure. The original full
subcategory inclusion, with its actual inherited Waldhausen structure, is
then transported through the proved original zero-grade fibration.

Implementation provenance: `Quillen/Waldhausen/Cofinality/DenseKEquivalence.lean`
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
include h

/-- Original cofiber closure proves every required original pushout remains in the subcategory. -/
theorem closed : CofibrationClosedSubcategory.Closed W P where
  zero_mem := h.zero
  pushout_mem hi hQ hA hB hD := by
    apply (h.grading_zero_iff _).mp
    rw [h.grading.pushout hi hQ, (h.grading_zero_iff _).mpr hA,
      (h.grading_zero_iff _).mpr hB, (h.grading_zero_iff _).mpr hD]
    simp

/-- The actual inherited Waldhausen category on the original predicate. -/
def waldhausenStructure : Structure P.FullSubcategory :=
  CofibrationClosedSubcategory.waldhausenStructure W P h.closed

/-- The unchanged original full inclusion is exact. -/
theorem inclusion_exact : IsExact h.waldhausenStructure.cof h.waldhausenStructure.weq
    W.cof W.weq P.ι := CofibrationClosedSubcategory.inclusion_exact W P h.closed

/-- Transfer only the proved membership, retaining every original object and arrow. -/
def toZeroGrade : P.FullSubcategory ⥤ AcyclicCategory h.grading.nested :=
  ObjectProperty.ιOfLE (fun A hA ↦ (h.grading_acyclicObjects_iff A).mpr hA)

/-- Forget only the grade equation, using its proved exact original membership criterion. -/
def fromZeroGrade : AcyclicCategory h.grading.nested ⥤ P.FullSubcategory :=
  ObjectProperty.ιOfLE (fun A hA ↦ (h.grading_acyclicObjects_iff A).mp hA)

/-- The categorical comparison preserves every object and every ambient morphism literally. -/
def zeroGradeEquivalence : P.FullSubcategory ≌ AcyclicCategory h.grading.nested where
  functor := h.toZeroGrade
  inverse := h.fromZeroGrade
  unitIso := NatIso.ofComponents (fun _ ↦ P.isoMk (Iso.refl _)) (by
    intro A B f
    apply ObjectProperty.hom_ext
    simp [toZeroGrade, fromZeroGrade])
  counitIso := NatIso.ofComponents (fun _ ↦ (acyclicObjects h.grading.nested).isoMk (Iso.refl
    _)) (by
    intro A B f
    apply ObjectProperty.hom_ext
    simp [toZeroGrade, fromZeroGrade])

/-- The comparison is genuinely exact for the actual inherited cofibrations and fine weak maps. -/
theorem toZeroGrade_exact : IsExact h.waldhausenStructure.cof h.waldhausenStructure.weq
    (acyclicStructure h.grading.nested).cof (acyclicStructure h.grading.nested).weq
      h.toZeroGrade where
  zero hz := IsZero.of_full_of_faithful_of_isZero (acyclicObjects h.grading.nested).ι _
    (h.inclusion_exact.zero hz)
  cofibration _ hi := hi
  weak _ hf := hf
  pushout hi hp := IsPushout.of_map_of_faithful (acyclicObjects h.grading.nested).ι
    (h.inclusion_exact.pushout hi hp)

/-- The unchanged inverse is also genuinely exact. -/
theorem fromZeroGrade_exact : IsExact (acyclicStructure h.grading.nested).cof
    (acyclicStructure h.grading.nested).weq h.waldhausenStructure.cof h.waldhausenStructure.weq
    h.fromZeroGrade where
  zero hz := IsZero.of_full_of_faithful_of_isZero P.ι _
    ((acyclicInclusion_exact h.grading.nested).zero hz)
  cofibration _ hi := hi
  weak _ hf := hf
  pushout hi hp := IsPushout.of_map_of_faithful P.ι
    ((acyclicInclusion_exact h.grading.nested).pushout hi hp)

/-- The comparison retains the entire original full inclusion, not just its homotopy class. -/
@[simp] theorem toZeroGrade_comp_inclusion : h.toZeroGrade ⋙ acyclicInclusion h.grading.nested =
    P.ι := rfl

/-- The actual original inclusion KMap factors through the actual membership comparison. -/
theorem inclusion_KMap_factor (n : ℕ) :
    (KMap (acyclicInclusion_exact h.grading.nested) n).comp (KMap h.toZeroGrade_exact n) =
      KMap h.inclusion_exact n := (KMap_comp_KMap h.toZeroGrade_exact (acyclicInclusion_exact
        h.grading.nested) n).symm.symm

end CategoryTheory.Waldhausen.Cofinality.DenseCofiberData

namespace CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
open Fibration
variable {C : Type u} [SmallCategory C] {W : Structure C} [HasBinaryCoproducts C]
  {P : ObjectProperty C} (h : DenseCofiberData W P)
  (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)
include D hs

/-- The original inclusion is injective in every degree, including the genuine K-zero group. -/
theorem inclusion_KMap_injective (n : ℕ) : Function.Injective (KMap h.inclusion_exact n) := by
  let he := KEquivOfExactEquivalence h.zeroGradeEquivalence h.toZeroGrade_exact
    h.fromZeroGrade_exact n
  rw [← h.inclusion_KMap_factor n]
  exact (h.grading.zeroGrade_KMap_injective D hs n).comp he.injective

/-- Positive original K-classes have genuine original subcategory preimages. -/
theorem inclusion_KMap_succ_bijective (n : ℕ) :
    Function.Bijective (KMap h.inclusion_exact (n + 1)) := by
  let he := KEquivOfExactEquivalence h.zeroGradeEquivalence h.toZeroGrade_exact
    h.fromZeroGrade_exact (n + 1)
  rw [← h.inclusion_KMap_factor (n + 1)]
  exact (h.grading.zeroGradeKEquiv D hs n).bijective.comp he.bijective

/-- The actual dense full inclusion supplies the positive K-equivalence itself. -/
def inclusionKEquiv (n : ℕ) : h.waldhausenStructure.K (n + 1) ≃* W.K (n + 1) :=
  MulEquiv.ofBijective (KMap h.inclusion_exact (n + 1)) (h.inclusion_KMap_succ_bijective D hs n)

/-- This equivalence's forward map remains precisely the original full-inclusion KMap. -/
@[simp] theorem inclusionKEquiv_apply (n : ℕ) (a : h.waldhausenStructure.K (n + 1)) :
    h.inclusionKEquiv D hs n a = KMap h.inclusion_exact (n + 1) a := rfl

/-- The range of the literal original inclusion is exactly the kernel of changing weak classes. -/
theorem range_inclusion_KMap (n : ℕ) :
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
theorem inclusion_KZero_exact :
    Function.Injective (KMap h.inclusion_exact 0) ∧
    (KMap h.inclusion_exact 0).range = (KMap (changeWeak_exact h.grading.nested) 0).ker ∧
    Function.Surjective (KMap (changeWeak_exact h.grading.nested) 0) :=
  ⟨h.inclusion_KMap_injective D hs 0, h.range_inclusion_KMap D hs 0,
    (h.grading.zeroGrade_KZero_exact D hs).2.2⟩

end CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
