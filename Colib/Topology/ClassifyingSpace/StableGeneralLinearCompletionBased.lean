/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionStages
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportGroup
public import Colib.Topology.ClassifyingSpace.FundamentalGroup

/-!
# The actual basepoint track and fundamental-group map of stable completion

The chosen inverse homotopy of the original Grothendieck projection supplies
the basepoint path. The same homotopy gives every finite-stage square, so the
basepoint correction is retained rather than replaced by strict pointedness.
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

namespace ModuleCat.FiniteProjective.StableCompletion
variable (R : Type u) [Ring R]

/-- The original stable single-object vertex. -/
def stableBase : ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)) :=
  classifyingSpacePoint (SingleObj.star _)

/-- The original zero-pair vertex, regarded in its actual path component. -/
def zeroBase : ZeroComponent R := ⟨zeroPoint R, Joined.refl _⟩

/-- The original rank-zero object of the finite matrix telescope. -/
def telescopeBase : StableGeneralLinear.GrothendieckModel.Telescope R :=
  ⟨StableGeneralLinear.rankIndex 0, AsSmall.up.obj (SingleObj.star _)⟩

/-- One chosen witness of the actual left-inverse homotopy, used throughout the based data. -/
def projectionInverseHomotopy :
    ((StableGeneralLinear.GrothendieckModel.classifyingHomotopyEquiv R).invFun.comp
      (StableGeneralLinear.GrothendieckModel.classifyingHomotopyEquiv R).toFun).Homotopy
        (ContinuousMap.id _) :=
  (StableGeneralLinear.GrothendieckModel.classifyingHomotopyEquiv R).left_inv.some

/-- The same inverse homotopy after mapping into the zero component. -/
def zeroInverseHomotopy :=
  (ContinuousMap.Homotopy.refl (telescopeZeroMap R)).comp (projectionInverseHomotopy R)

/-- Restrict the chosen zero-component inverse homotopy to any original finite fiber. -/
def finiteZeroHomotopy (n : ℕ) :=
  (zeroInverseHomotopy R).compContinuousMap
    (classifyingSpaceMap (CategoryTheory.Grothendieck.ι (StableGeneralLinear.categoryDiagram R)
      (StableGeneralLinear.rankIndex n))).hom

/-- The source of the chosen inverse track is the actual stable-map basepoint image. -/
lemma inverseTrack_source :
    (zeroInverseHomotopy R) (0, classifyingSpacePoint (telescopeBase R)) =
      stableZeroMap R (stableBase R) := by
  rw [(zeroInverseHomotopy R).apply_zero]
  apply Subtype.ext
  change telescopeMap R
    ((StableGeneralLinear.GrothendieckModel.classifyingHomotopyEquiv R).invFun
      (classifyingSpaceMap (StableGeneralLinear.GrothendieckModel.projection R)
        (classifyingSpacePoint (telescopeBase R)))) = _
  rw [classifyingSpaceMap_point]
  change _ = telescopeMap R
    ((StableGeneralLinear.GrothendieckModel.classifyingHomotopyEquiv R).invFun
      (asSmallClassifyingHomeomorph
        (SingleObj (StableGeneralLinear.Group R)) (stableBase R)))
  rw [stableBase, asSmallClassifyingHomeomorph_point]
  rfl

/-- The target of the chosen inverse track is the actual zero basepoint. -/
lemma inverseTrack_target :
    (zeroInverseHomotopy R) (1, classifyingSpacePoint (telescopeBase R)) = zeroBase R := by
  rw [(zeroInverseHomotopy R).apply_one]
  apply Subtype.ext
  exact classifyingSpaceMapUniversal_point (telescopeFunctor R) (telescopeBase R)

/-- The actual basepoint-correction path traced by the original inverse homotopy. -/
def basepointPath : Path (stableZeroMap R (stableBase R)) (zeroBase R) where
  toFun t := zeroInverseHomotopy R (t, classifyingSpacePoint (telescopeBase R))
  continuous_toFun :=
    (zeroInverseHomotopy R).continuous.comp (continuous_id.prodMk continuous_const)
  source' := inverseTrack_source R
  target' := inverseTrack_target R

/-- Every finite-stage basepoint track is the restriction of the same chosen inverse homotopy. -/
lemma finiteZeroHomotopy_vertex (n : ℕ) (t : unitInterval) :
    finiteZeroHomotopy R n
      (t, classifyingSpacePoint
        (AsSmall.up.obj (SingleObj.star (Matrix.GeneralLinearGroup (Fin n) R)))) =
        zeroInverseHomotopy R (t, classifyingSpacePoint
          (⟨StableGeneralLinear.rankIndex n, AsSmall.up.obj (SingleObj.star _)⟩ :
            StableGeneralLinear.GrothendieckModel.Telescope R)) := by
  change zeroInverseHomotopy R (t, classifyingSpaceMap
    (CategoryTheory.Grothendieck.ι (StableGeneralLinear.categoryDiagram R)
      (StableGeneralLinear.rankIndex n)) _ ) = _
  rw [classifyingSpaceMap_point]
  rfl

/-- The stable basepoint correction is exactly the rank-zero stage-square track. -/
lemma basepointPath_eq_finiteZeroHomotopy (t : unitInterval) :
    basepointPath R t = finiteZeroHomotopy R 0
      (t, classifyingSpacePoint
        (AsSmall.up.obj (SingleObj.star (Matrix.GeneralLinearGroup (Fin 0) R)))) :=
  (finiteZeroHomotopy_vertex R 0 t).symm

/-- The induced fundamental-group homomorphism includes the actual basepoint transport. -/
def stablePiOneMap :
    HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)))
      (stableBase R) →*
      HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R) :=
  (pathTransportMulEquiv (basepointPath R) 0).toMonoidHom.comp
    (piMap 0 (stableZeroMap R) rfl)

/-- The stable matrix group maps to the target fundamental group through its proved BG model. -/
def stableGroupPiOneMap : StableGeneralLinear.Group R →*
    HomotopyGroup.Pi 1 (ZeroComponent R) (zeroBase R) :=
  (stablePiOneMap R).comp (GroupoidClassifying.singleObjPiOneEquiv
    (StableGeneralLinear.Group R)).toMonoidHom

end ModuleCat.FiniteProjective.StableCompletion
