/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Cofinality.JointData
public import Colib.KTheory.Waldhausen.Cofinality.GradedGroupRealization
public import Colib.Topology.ClassifyingSpace.Groupoid
public import Colib.KTheory.Waldhausen.Fibration.LongExactSequence

/-! # Actual zero-grade cofinality from the original fibration

The genuine group-nerve comparison and groupoid asphericity kill the positive
coarse K-groups. The proved original fibration, obtained from the given fine
joint cylinder and its actual second endpoint section, then proves that the
unchanged zero-grade inclusion is bijective in positive degrees and injective
in degree zero. The remaining degree-zero endpoint is retained literally.

Implementation provenance: `Quillen/Waldhausen/Cofinality/ZeroGrade.lean`
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
universe u
namespace CategoryTheory.Waldhausen.Cofinality.Grading
open Fibration
variable {C G : Type u} [SmallCategory C] [AddCommGroup G]
  {W : Structure C} (d : Grading W G)

/-- Positive coarse K-groups vanish by the original grade map and genuine groupoid asphericity. -/
theorem coarse_K_succ_subsingleton (T : FunctorialFactorization W) (n : ℕ) :
    Subsingleton (d.coarseStructure.K (n + 1)) := by
  let : Subsingleton (HomotopyGroup.Pi (n + 2)
      (SSet.toTop.obj (nerve (SingleObj (Multiplicative (d.valueRange T)))))
      ((SSet.toTop.map (d.groupGradeMap T)).hom d.coarseStructure.kBasepoint)) :=
    GroupoidClassifying.subsingleton_higher_pi_at
      (C := SingleObj (Multiplicative (d.valueRange T))) _ n
  exact ((d.groupGradeMap_isRealizationWeakEquivalence T).homotopy_bijective
    d.coarseStructure.kBasepoint (n + 2)).injective.subsingleton

variable (D : RowFactorization.JointData (NestedWeakEquivalences.refl W))
  (hs : RowFactorization.SecondEndpointSection (NestedWeakEquivalences.refl W) D)

include D hs

/-- The unchanged actual zero-grade inclusion is injective in every connective degree. -/
theorem zeroGrade_KMap_injective (n : ℕ) :
    Function.Injective (KMap (acyclicInclusion_exact d.nested) n) := by
  let : Subsingleton (d.nested.coarse.K (n + 1)) := d.coarse_K_succ_subsingleton
    D.sourceFactorization n
  apply (KMap (acyclicInclusion_exact d.nested) n).ker_eq_bot_iff.mp
  rw [← range_changeWeakConnectingHom_eq_ker_acyclicInclusion d.nested
    (d.canonicalFiberMap_isWeakHomotopyEquivalence D hs) n]
  apply le_antisymm _ bot_le
  rintro a ⟨b, rfl⟩
  change changeWeakConnectingHom d.nested
    (d.canonicalFiberMap_isWeakHomotopyEquivalence D hs) n b = 1
  rw [Subsingleton.elim b 1, map_one]

/-- In positive degree the original zero-grade inclusion is surjective as well. -/
theorem zeroGrade_KMap_succ_surjective (n : ℕ) :
    Function.Surjective (KMap (acyclicInclusion_exact d.nested) (n + 1)) := by
  let : Subsingleton (d.nested.coarse.K (n + 1)) := d.coarse_K_succ_subsingleton
    D.sourceFactorization n
  intro a
  have ha : a ∈ (KMap (changeWeak_exact d.nested) (n + 1)).ker := Subsingleton.elim _ _
  rw [← range_acyclicInclusion_eq_ker_changeWeak_of_weak d.nested
    (d.canonicalFiberMap_isWeakHomotopyEquivalence D hs) (n + 1)] at ha
  exact ha

/-- The original inclusion, without replacing its source or map, is a positive K-equivalence. -/
def zeroGradeKEquiv (n : ℕ) : (acyclicStructure d.nested).K (n + 1) ≃* W.K (n + 1) :=
  MulEquiv.ofBijective (KMap (acyclicInclusion_exact d.nested) (n + 1))
    ⟨d.zeroGrade_KMap_injective D hs (n + 1), d.zeroGrade_KMap_succ_surjective D hs n⟩

/-- The equivalence's forward function is literally the original canonical inclusion KMap. -/
@[simp] theorem zeroGradeKEquiv_apply (n : ℕ) (a : (acyclicStructure d.nested).K (n + 1)) :
    d.zeroGradeKEquiv D hs n a = KMap (acyclicInclusion_exact d.nested) (n + 1) a := rfl

/-- The exact degree-zero tail retains its true coarse endpoint, without a K-zero presentation. -/
theorem zeroGrade_KZero_exact :
    Function.Injective (KMap (acyclicInclusion_exact d.nested) 0) ∧
    (KMap (acyclicInclusion_exact d.nested) 0).range = (KMap (changeWeak_exact d.nested) 0).ker ∧
    Function.Surjective (KMap (changeWeak_exact d.nested) 0) :=
  ⟨d.zeroGrade_KMap_injective D hs 0,
    range_acyclicInclusion_eq_ker_changeWeak_of_weak d.nested
      (d.canonicalFiberMap_isWeakHomotopyEquivalence D hs) 0,
    changeWeak_KMap_zero_surjective_of_weak d.nested
      (d.canonicalFiberMap_isWeakHomotopyEquivalence D hs)⟩

end CategoryTheory.Waldhausen.Cofinality.Grading
