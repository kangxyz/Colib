/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Cofinality.ZeroGrade
public import Colib.KTheory.Waldhausen.AsSmall.Approximation
public import Mathlib.Algebra.Group.ULift

/-! # Original graded cofinality with independent category universes

The honest grading is transported through the actual up/down small model.
The original coarse K-groups are retained through their based homeomorphism;
the genuine original fibration then proves the unchanged inclusion results.

Implementation provenance: `Quillen/Waldhausen/Cofinality/GeneralGraded.lean`
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
namespace CategoryTheory.Waldhausen.Cofinality.Grading
open Fibration
variable {C G : Type u} [Category.{v} C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)

/-- The original additive values and actual pushout equations survive common-universe transport. -/
def asSmallGrading : Grading W.asSmall (ULift.{v} G) where
  value A := ULift.up (d.value (AsSmall.down.obj A))
  zero := ULift.ext d.zero
  weak f hf := ULift.ext (d.weak (AsSmall.down.map f) hf)
  pushout hi hQ := ULift.ext (d.pushout hi (W.asSmall_down_exact.pushout hi hQ))

/-- The actual coarse small-model structure is unchanged except for proved equality of lifted
grades. -/
theorem asSmallGrading_coarseStructure :
    d.asSmallGrading.coarseStructure = d.coarseStructure.asSmall := by
  unfold Grading.coarseStructure Structure.asSmall
  congr 1
  funext A B f
  exact propext ULift.ext_iff

variable (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))
include D

/-- Original positive coarse K-groups vanish with independent object and hom universes. -/
theorem coarse_K_succ_subsingleton_general (n : ℕ) : Subsingleton (d.coarseStructure.K (n + 1))
    := by
  let : Subsingleton (d.coarseStructure.asSmall.K (n + 1)) := by
    rw [← d.asSmallGrading_coarseStructure]
    exact d.asSmallGrading.coarse_K_succ_subsingleton D.reflexiveAsSmall.sourceFactorization n
  exact (d.coarseStructure.asSmallKEquiv (n + 1)).injective.subsingleton

variable (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)
include hs

/-- The unchanged zero-grade inclusion is injective in every original connective degree. -/
theorem zeroGrade_KMap_injective_general (n : ℕ) :
    Function.Injective (KMap (acyclicInclusion_exact d.nested) n) := by
  let : Subsingleton (d.nested.coarse.K (n + 1)) := d.coarse_K_succ_subsingleton_general D n
  apply (KMap (acyclicInclusion_exact d.nested) n).ker_eq_bot_iff.mp
  rw [← range_changeWeakConnectingHom_eq_ker_acyclicInclusion d.nested
    (d.canonicalFiberMap_isWeakHomotopyEquivalence D hs) n]
  apply le_antisymm _ bot_le
  rintro a ⟨b, rfl⟩
  change changeWeakConnectingHom d.nested
    (d.canonicalFiberMap_isWeakHomotopyEquivalence D hs) n b = 1
  rw [Subsingleton.elim b 1, map_one]

/-- Every positive original K-class has an original zero-grade preimage in its original
universes. -/
theorem zeroGrade_KMap_succ_surjective_general (n : ℕ) :
    Function.Surjective (KMap (acyclicInclusion_exact d.nested) (n + 1)) := by
  let : Subsingleton (d.nested.coarse.K (n + 1)) := d.coarse_K_succ_subsingleton_general D n
  intro a
  have ha : a ∈ (KMap (changeWeak_exact d.nested) (n + 1)).ker := Subsingleton.elim _ _
  rw [← range_acyclicInclusion_eq_ker_changeWeak_of_weak d.nested
    (d.canonicalFiberMap_isWeakHomotopyEquivalence D hs) (n + 1)] at ha
  exact ha

/-- The original positive inclusion KMap is an equivalence with independent category universes. -/
def zeroGradeKEquivGeneral (n : ℕ) : (acyclicStructure d.nested).K (n + 1) ≃* W.K (n + 1) :=
  MulEquiv.ofBijective (KMap (acyclicInclusion_exact d.nested) (n + 1))
    ⟨d.zeroGrade_KMap_injective_general D hs (n + 1), d.zeroGrade_KMap_succ_surjective_general D
      hs n⟩

/-- The general-universe equivalence retains the literal original inclusion homomorphism. -/
@[simp] theorem zeroGradeKEquivGeneral_coe (n : ℕ) :
    (↑(d.zeroGradeKEquivGeneral D hs n) : (acyclicStructure d.nested).K (n + 1) →* W.K (n + 1)) =
      KMap (acyclicInclusion_exact d.nested) (n + 1) := rfl

/-- The original degree-zero tail retains its exact remaining original coarse endpoint. -/
theorem zeroGrade_KZero_exact_general :
    Function.Injective (KMap (acyclicInclusion_exact d.nested) 0) ∧
    (KMap (acyclicInclusion_exact d.nested) 0).range = (KMap (changeWeak_exact d.nested) 0).ker ∧
    Function.Surjective (KMap (changeWeak_exact d.nested) 0) :=
  ⟨d.zeroGrade_KMap_injective_general D hs 0,
    range_acyclicInclusion_eq_ker_changeWeak_of_weak d.nested
      (d.canonicalFiberMap_isWeakHomotopyEquivalence D hs) 0,
    changeWeak_KMap_zero_surjective_of_weak d.nested
      (d.canonicalFiberMap_isWeakHomotopyEquivalence D hs)⟩

end CategoryTheory.Waldhausen.Cofinality.Grading
