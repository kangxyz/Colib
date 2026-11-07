/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.SkeletalCartesianAssembly

/-! # Outgoing stage face in its actual skeleton coordinates -/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremB/SkeletalCartesianStageRestriction.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd, retaining the actual replacement charts,
base restrictions and canonical comparisons. -/
@[expose] public section

open CategoryTheory.TheoremA SSet Topology.HomotopyPullback
open CategoryTheory.TheoremB


noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremB.Skeletal
open TheoremA
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- The cube's outgoing stage square is exactly the canonical square over
the actual base skeleton inclusion, after removing its point coefficients. -/
theorem restrictionCartesian_of_stageCartesian (n : ℕ)
    (hstage : Cartesian (stageProjection (replacementPointAugmentation H) n).hom
      (stageProjection (replacementPointAugmentation H) (n + 1)).hom
      (stageStep H n).hom (stageStep pointDiagram n).hom
      (congrArg TopCat.Hom.hom (stageStepSquare (replacementPointAugmentation H) n))) :
    RestrictionCartesian H ((nerve D).skeleton.monotone (Nat.le_succ n)) := by
  let eA := pointRestrictionHomeomorph ((nerve D).skeleton n)
  let eB := pointRestrictionHomeomorph ((nerve D).skeleton (n+1))
  apply cartesianOfCoordinates _ _ _ _ _
    (stageProjection (replacementPointAugmentation H) n).hom
    (stageProjection (replacementPointAugmentation H) (n+1)).hom
    (stageStep H n).hom (stageStep pointDiagram n).hom
    (congrArg TopCat.Hom.hom (stageStepSquare (replacementPointAugmentation H) n))
    (Homeomorph.refl _) (Homeomorph.refl _) eA.symm eB.symm
  · apply ContinuousMap.ext
    intro x
    apply eA.injective
    change eA (stageProjection (replacementPointAugmentation H) n x) =
      eA (eA.symm (SSet.toTop.map (restrictionProjection H ((nerve D).skeleton n)) x))
    rw [Homeomorph.apply_symm_apply]
    exact ConcreteCategory.congr_hom (pointRestrictionIso_projectionTower H n) x
  · apply ContinuousMap.ext
    intro x
    apply eB.injective
    change eB (stageProjection (replacementPointAugmentation H) (n+1) x) =
      eB (eB.symm (SSet.toTop.map (restrictionProjection H ((nerve D).skeleton (n+1))) x))
    rw [Homeomorph.apply_symm_apply]
    exact ConcreteCategory.congr_hom (pointRestrictionIso_projectionTower H (n+1)) x
  · rfl
  · apply ContinuousMap.ext
    intro x
    apply eB.injective
    change eB (stageStep pointDiagram n (eA.symm x)) =
      eB (eB.symm (SSet.toTop.map
        (SSet.Subcomplex.homOfLE ((nerve D).skeleton.monotone (Nat.le_succ n))) x))
    rw [Homeomorph.apply_symm_apply]
    have h := ConcreteCategory.congr_hom
      (pointRestrictionIso_baseTower (D := D) (Nat.le_succ n)) (eA.symm x)
    change eB (stageStep pointDiagram n (eA.symm x)) =
      SSet.toTop.map (SSet.Subcomplex.homOfLE ((nerve D).skeleton.monotone (Nat.le_succ n)))
        (eA (eA.symm x)) at h
    simpa only [Homeomorph.apply_symm_apply] using h
  · exact hstage

/-- The actual successor restriction comparison follows from the preceding
stage's characteristic charts and the diagram transition equivalences. -/
theorem replacementSuccessor_restriction
    (htrans : ∀ ⦃d e : D⦄ (f : d ⟶ e),
      ∃ E : ContinuousMap.HomotopyEquiv |H.obj d| |H.obj e|,
        E.toFun = (SSet.toTop.map (H.map f)).hom)
    (n : ℕ)
    (hchart : ∀ (k : ℕ) (v : (nerve D).obj (op ⦋k⦌))
      (hv : v ∈ ((nerve D).skeleton n).obj (op ⦋k⦌)),
      ChartCartesian H ((nerve D).skeleton n) v hv) :
    RestrictionCartesian H ((nerve D).skeleton.monotone (Nat.le_succ n)) :=
  restrictionCartesian_of_stageCartesian H n (replacementSuccessor_cartesian H htrans n hchart).1

end CategoryTheory.TheoremB.Skeletal
