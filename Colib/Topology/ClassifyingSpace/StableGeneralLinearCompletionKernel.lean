/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCharacter
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionBasedSurjectivity
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportFundamentalGroup

/-!
# The kernel of the original based stable completion comparison

The actual completion character detects the original quotient map. Its based
map uses the previously fixed inverse-homotopy correction, not a new comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Topology SSet HomotopyGroup CategoryTheory.Limits
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal
  ModuleCat.FiniteProjective.directSumSymmetric
namespace ModuleCat.FiniteProjective.StableCompletion
variable (R : Type u) [Ring R]

/-- The original vertex of the actual stable elementary quotient classifying space. -/
def quotientBase :=
  classifyingSpacePoint (SingleObj.star (StableGeneralLinear.ElementaryQuotient R))

/-- The actual detector restricted to the actual zero component. -/
def zeroDetectionMap : C(ZeroComponent R,
    ClassifyingSpace (SingleObj (StableGeneralLinear.ElementaryQuotient R))) :=
  (quotientDetectionMap R).comp ⟨Subtype.val, continuous_subtype_val⟩

/-- The detector preserves the specified zero vertex exactly. -/
lemma zeroDetectionMap_point : zeroDetectionMap R (zeroBase R) = quotientBase R := by
  change classifyingSpaceMapUniversal (stableCompletionCharacter R)
    (classifyingSpacePoint (stageObject R 0)) = _
  rw [classifyingSpaceMapUniversal_point]
  exact congrArg classifyingSpacePoint (Subsingleton.elim _ _)

/-- The detector carries the original correction path to this actual target path. -/
def detectionBasepointPath :
    Path ((zeroDetectionMap R).comp (stableZeroMap R) (stableBase R)) (quotientBase R) :=
  ((basepointPath R).map (zeroDetectionMap R).continuous).cast rfl (zeroDetectionMap_point R).symm

/-- The induced detector takes values in the actual stable elementary quotient. -/
def zeroPiOneDetector : HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R) →*
    StableGeneralLinear.ElementaryQuotient R :=
  (GroupoidClassifying.singleObjPiOneEquiv
    (StableGeneralLinear.ElementaryQuotient R)).symm.toMonoidHom.comp
      (piMap 0 (zeroDetectionMap R) (zeroDetectionMap_point R))

/-- Postcomposition retains precisely the previously chosen stable correction path. -/
lemma zeroDetection_stablePiOne (a : HomotopyGroup.Pi 1
    (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))) (stableBase R)) :
    piMap 0 (zeroDetectionMap R) (zeroDetectionMap_point R) (stablePiOneMap R a) =
      pathTransportMulEquiv (detectionBasepointPath R) 0
        (piMap 0 ((zeroDetectionMap R).comp (stableZeroMap R)) rfl a) := by
  have haux (z : ClassifyingSpace (SingleObj (StableGeneralLinear.ElementaryQuotient R)))
      (hz : zeroDetectionMap R (zeroBase R) = z) :
      HomotopyGroup.map (zeroDetectionMap R) hz (pathTransport (basepointPath R) 1
        (HomotopyGroup.map (stableZeroMap R) rfl a)) =
      pathTransport (((basepointPath R).map (zeroDetectionMap R).continuous).cast rfl hz.symm) 1
        (HomotopyGroup.map ((zeroDetectionMap R).comp (stableZeroMap R)) rfl a) := by
    subst z
    rw [HomotopyGroup.map_comp (stableZeroMap R) rfl (zeroDetectionMap R) rfl]
    exact (pathTransport_naturality (zeroDetectionMap R) (basepointPath R) 1 _).symm
  exact haux _ (zeroDetectionMap_point R)

/-- The quotient classifying space has its original commutative fundamental-group multiplication. -/
lemma quotientPiOne_mul_comm
    (a b : HomotopyGroup.Pi 1
      (ClassifyingSpace (SingleObj (StableGeneralLinear.ElementaryQuotient R))) (quotientBase R)) :
    a * b = b * a := by
  apply (GroupoidClassifying.singleObjPiOneEquiv
    (StableGeneralLinear.ElementaryQuotient R)).symm.injective
  simp only [map_mul]
  exact mul_comm _ _

/-- The based detector recovers the original quotient-induced fundamental-group map. -/
lemma zeroDetection_stablePiOne_quotient (a : HomotopyGroup.Pi 1
    (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))) (stableBase R)) :
    piMap 0 (zeroDetectionMap R) (zeroDetectionMap_point R) (stablePiOneMap R a) =
      GroupoidClassifying.piOneMap (StableGeneralLinear.quotientMap R) a := by
  let q := (GroupoidClassifying.classifyingMap (StableGeneralLinear.quotientMap R)).hom
  have hq : q (stableBase R) = quotientBase R :=
    GroupoidClassifying.classifyingMap_point _
  let δ : Path (q (stableBase R)) (quotientBase R) :=
    (Path.refl (quotientBase R)).cast hq rfl
  have hH : ((zeroDetectionMap R).comp (stableZeroMap R)).Homotopic q :=
    stableMap_quotientDetection_homotopic R
  have he := DFunLike.congr_fun (piOne_homotopy_corrected hH.some
    (detectionBasepointPath R) δ (quotientPiOne_mul_comm R)) a
  have haux (y : ClassifyingSpace (SingleObj (StableGeneralLinear.ElementaryQuotient R)))
      (hy : q (stableBase R) = y) :
      pathTransport ((Path.refl y).cast hy rfl) 1 (HomotopyGroup.map q rfl a) =
        HomotopyGroup.map q hy a := by
    subst y
    rw [Path.cast_rfl_rfl, pathTransport_refl]
    rfl
  rw [zeroDetection_stablePiOne]
  exact he.trans (haux _ hq)

/-- The detector recovers the original quotient value of every stable matrix. -/
lemma zeroPiOneDetector_stableGroup (g : StableGeneralLinear.Group R) :
    zeroPiOneDetector R (stableGroupPiOneMap R g) = StableGeneralLinear.quotientMap R g := by
  change (GroupoidClassifying.singleObjPiOneEquiv
    (StableGeneralLinear.ElementaryQuotient R)).symm
      (piMap 0 (zeroDetectionMap R) (zeroDetectionMap_point R)
        (stablePiOneMap R (GroupoidClassifying.singleObjPiOneEquiv
          (StableGeneralLinear.Group R) g))) = _
  rw [zeroDetection_stablePiOne_quotient, GroupoidClassifying.piOneMap_equiv]
  exact (GroupoidClassifying.singleObjPiOneEquiv
    (StableGeneralLinear.ElementaryQuotient R)).symm_apply_apply _

/-- The actual original stable comparison kills precisely the stable elementary subgroup. -/
theorem ker_stableGroupPiOneMap :
    (stableGroupPiOneMap R).ker = StableGeneralLinear.elementary R := by
  apply le_antisymm
  · intro g hg
    apply (StableGeneralLinear.quotientMap_eq_one R g).mp
    change stableGroupPiOneMap R g = 1 at hg
    rw [← zeroPiOneDetector_stableGroup R g, hg, map_one]
  · exact elementary_le_ker_stableGroupPiOneMap R

/-- The actual quotient detector is a left inverse to the already constructed original factor. -/
lemma zeroPiOneDetector_elementaryPiOneFactor (g : StableGeneralLinear.ElementaryQuotient R) :
    zeroPiOneDetector R (elementaryPiOneFactor R g) = g := by
  obtain ⟨g, rfl⟩ := StableGeneralLinear.quotientMap_surjective R g
  exact zeroPiOneDetector_stableGroup R g

/-- The original elementary-quotient factor is injective. -/
theorem elementaryPiOneFactor_injective : Function.Injective (elementaryPiOneFactor R) :=
  Function.LeftInverse.injective (zeroPiOneDetector_elementaryPiOneFactor R)

/-- The original quotient factor identifies the actual zero-component fundamental group. -/
def elementaryPiOneEquiv : StableGeneralLinear.ElementaryQuotient R ≃*
    HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R) :=
  MulEquiv.ofBijective (elementaryPiOneFactor R)
    ⟨elementaryPiOneFactor_injective R, elementaryPiOneFactor_surjective R⟩

/-- The isomorphism retains every original stable matrix value. -/
lemma elementaryPiOneEquiv_quotientMap (g : StableGeneralLinear.Group R) :
    elementaryPiOneEquiv R (StableGeneralLinear.quotientMap R g) = stableGroupPiOneMap R g := rfl

/-- In the original classifying-space fundamental group, the kernel is exactly the image of E. -/
theorem ker_stablePiOneMap :
    (stablePiOneMap R).ker = (StableGeneralLinear.elementary R).map
      (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R)).toMonoidHom := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, rfl⟩ := (GroupoidClassifying.singleObjPiOneEquiv
      (StableGeneralLinear.Group R)).surjective x
    apply Subgroup.mem_map_of_mem
    rw [← ker_stableGroupPiOneMap R]
    exact hx
  · exact elementaryPiOne_le_ker_stablePiOneMap R

/-- The inverse of the original quotient factor is the actual completion-character detector. -/
lemma elementaryPiOneEquiv_symm (a : HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R)) :
    (elementaryPiOneEquiv R).symm a = zeroPiOneDetector R a := by
  obtain ⟨g, rfl⟩ := elementaryPiOneFactor_surjective R a
  change (elementaryPiOneEquiv R).symm (elementaryPiOneEquiv R g) = _
  rw [MulEquiv.symm_apply_apply, zeroPiOneDetector_elementaryPiOneFactor]

end ModuleCat.FiniteProjective.StableCompletion
