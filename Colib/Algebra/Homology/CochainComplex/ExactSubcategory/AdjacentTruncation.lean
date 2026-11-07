/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationCoherence
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationLayer
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationTransformations

/-!
# The actual adjacent smart-truncation short exact sequence

The original coherence isomorphism and disk identification retain the natural
adjacent maps and prove their inherited conflation, with the stated kernel and
extension closure hypotheses.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.AdjacentTruncation`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace CochainComplex

attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The canonical adjacent inclusion, characterized by compatibility with
both original inclusions into the untruncated complex. -/
def adjacentTruncationInclusion (n : ℤ) :
    boundedAcyclicTruncLEFunctor P n ⟶ boundedAcyclicTruncLEFunctor P (n + 1) :=
  (boundedAcyclicTruncLECompIso P n (n + 1) (by omega)).inv ≫
    Functor.whiskerLeft (boundedAcyclicTruncLEFunctor P (n + 1))
      (boundedAcyclicTruncationInclusion P n)

/-- The actual quotient projection, followed by the proved natural disk identification. -/
def adjacentTruncationProjection (n : ℤ) :
    boundedAcyclicTruncLEFunctor P (n + 1) ⟶
      boundedAcyclicCyclesFunctor P (n + 1) ⋙ boundedAcyclicDiskFunctor P n :=
  Functor.whiskerLeft (boundedAcyclicTruncLEFunctor P (n + 1))
    (boundedAcyclicTruncationProjection P n) ≫
    (oneStepLayerDiskIso P n).hom

/-- The adjacent inclusion has exactly the original ambient inclusion as composite. -/
@[reassoc]
theorem adjacentTruncationInclusion_ambient (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    ((adjacentTruncationInclusion P n).app K).hom ≫ K.obj.ιTruncLE (n + 1) =
      K.obj.ιTruncLE n := by
  change ((truncLECompIso (A := A) n (n + 1) (by omega)).inv.app K.obj ≫
      (K.obj.truncLE (n + 1)).ιTruncLE n) ≫ K.obj.ιTruncLE (n + 1) = _
  rw [Category.assoc, ← truncLECompIso_inclusion K.obj n (n + 1) (by omega)]
  simp

/-- The actual adjacent maps compose to zero. -/
@[reassoc]
theorem adjacentTruncation_comp_zero (n : ℤ) :
    adjacentTruncationInclusion P n ≫ adjacentTruncationProjection P n = 0 := by
  apply NatTrans.ext
  funext K
  let S := (acyclicTruncationSequenceFunctor P n).obj
    ((boundedAcyclicTruncLEFunctor P (n + 1)).obj K)
  change ((boundedAcyclicTruncLECompIso P n (n + 1) (by omega)).inv.app K ≫ S.f) ≫
    (S.g ≫ (oneStepLayerDiskIso P n).hom.app K) = 0
  rw [Category.assoc, ← Category.assoc S.f S.g, S.zero, zero_comp, comp_zero]

variable [(abelianExactStructure A).IsExtensionClosed P]

/-- The adjacent sequence is an actual inherited conflation, with its disk quotient. -/
theorem adjacentTruncation_conflation (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    (boundedAcyclicExactStructure P).conflation
      (ShortComplex.mk ((adjacentTruncationInclusion P n).app K)
        ((adjacentTruncationProjection P n).app K)
        (NatTrans.congr_app (adjacentTruncation_comp_zero P n) K)) := by
  let S := (acyclicTruncationSequenceFunctor P n).obj
    ((boundedAcyclicTruncLEFunctor P (n + 1)).obj K)
  let e := ShortComplex.isoMk
    ((boundedAcyclicTruncLECompIso P n (n + 1) (by omega)).app K)
    (Iso.refl S.X₂) ((oneStepLayerDiskIso P n).app K)
    (S₁ := S) (S₂ := ShortComplex.mk ((adjacentTruncationInclusion P n).app K)
      ((adjacentTruncationProjection P n).app K)
      (NatTrans.congr_app (adjacentTruncation_comp_zero P n) K))
    (by simp [adjacentTruncationInclusion, boundedAcyclicTruncationInclusion, S])
    (by simp [adjacentTruncationProjection, boundedAcyclicTruncationProjection, S])
  exact (boundedAcyclicExactStructure P).iso_closed e
    (acyclicTruncationSequenceFunctor_conflation P n _)

end CochainComplex
