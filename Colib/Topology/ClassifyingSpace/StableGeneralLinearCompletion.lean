/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.StableGeneralLinearMap
public import Colib.Topology.ClassifyingSpace.Connectivity
public import Colib.Topology.ClassifyingSpace.UniverseMap

/-!
# The actual zero component of projective group completion

Original common-denominator arrows join the zero pair to every finite-stage
pair. These paths identify the precise path component of the original
finite-matrix construction.
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

/-- The original vertex of the pair of monoidal units. -/
def zeroPoint : ClassifyingSpace (Completion R) := classifyingSpacePoint (stageObject R 0)

/-- The actual path component of the zero pair, with its subspace topology. -/
abbrev ZeroComponent := ↥(pathComponent (zeroPoint R))

/-- The original stage translations give a path from zero to each finite-stage pair. -/
def zeroToStagePath (n : ℕ) :
    Path (zeroPoint R) (classifyingSpacePoint (stageObject R n)) :=
  classifyingSpacePath ((stageSequence R).map (homOfLE (Nat.zero_le n)))

/-- Any vertex-preserving realization of the original telescope functor lands in zero. -/
lemma telescopeMap_mem_zeroComponent
    (f : C(ClassifyingSpace (StableGeneralLinear.GrothendieckModel.Telescope R),
      ClassifyingSpace (Completion R)))
    (hf : ∀ X, f (classifyingSpacePoint X) =
      classifyingSpacePoint ((telescopeFunctor R).obj X))
    (x : ClassifyingSpace (StableGeneralLinear.GrothendieckModel.Telescope R)) :
    f x ∈ pathComponent (zeroPoint R) := by
  obtain ⟨X, hX⟩ := classifyingSpace_joined_vertex x
  have h := hX.map f.continuous
  rw [hf X] at h
  exact (show Joined (zeroPoint R) (classifyingSpacePoint ((telescopeFunctor R).obj X)) from
    ⟨zeroToStagePath R (StableGeneralLinear.rank X.base)⟩).trans h

/-- The original stable classifying space maps to the actual finite-rank telescope
using the inverse of the proved projection homotopy equivalence. -/
def originalStableToTelescope :
    C(ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)),
      ClassifyingSpace (StableGeneralLinear.GrothendieckModel.Telescope R)) :=
  (StableGeneralLinear.GrothendieckModel.classifyingHomotopyEquiv R).symm.toFun.comp
    ⟨asSmallClassifyingHomeomorph (SingleObj (StableGeneralLinear.Group R)),
      (asSmallClassifyingHomeomorph
        (SingleObj (StableGeneralLinear.Group R))).continuous⟩

/-- The telescope lift is a genuine homotopy inverse to the original projection. -/
lemma originalStableToTelescope_projection :
    ((classifyingSpaceMap (StableGeneralLinear.GrothendieckModel.projection R)).hom.comp
      (originalStableToTelescope R)).Homotopic
      (⟨asSmallClassifyingHomeomorph
          (SingleObj (StableGeneralLinear.Group R)),
        (asSmallClassifyingHomeomorph
          (SingleObj (StableGeneralLinear.Group R))).continuous⟩ : C(_, _)) := by
  let e := StableGeneralLinear.GrothendieckModel.classifyingHomotopyEquiv R
  let h : C(ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)),
      ClassifyingSpace (StableGeneralLinear.stableCategory R)) :=
    ⟨asSmallClassifyingHomeomorph
        (SingleObj (StableGeneralLinear.Group R)),
      (asSmallClassifyingHomeomorph
        (SingleObj (StableGeneralLinear.Group R))).continuous⟩
  change (e.toFun.comp (e.invFun.comp h)).Homotopic h
  simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
    e.right_inv.comp (ContinuousMap.Homotopic.refl h)

/-- The original Grothendieck-to-localization functor, realized across its actual universes. -/
def telescopeMap :
    C(ClassifyingSpace (StableGeneralLinear.GrothendieckModel.Telescope R),
      ClassifyingSpace (Completion R)) :=
  classifyingSpaceMapUniversal (telescopeFunctor R)

/-- The actual telescope map lands in the path component of the zero pair. -/
lemma telescopeMap_mem (x : ClassifyingSpace (StableGeneralLinear.GrothendieckModel.Telescope R)) :
    telescopeMap R x ∈ pathComponent (zeroPoint R) :=
  telescopeMap_mem_zeroComponent R (telescopeMap R)
    (classifyingSpaceMapUniversal_point (telescopeFunctor R)) x

/-- The original telescope map with codomain restricted to its proved zero component. -/
def telescopeZeroMap :
    C(ClassifyingSpace (StableGeneralLinear.GrothendieckModel.Telescope R), ZeroComponent R) where
  toFun x := ⟨telescopeMap R x, telescopeMap_mem R x⟩
  continuous_toFun := (telescopeMap R).continuous.subtype_mk _

/-- The actual map from the original stable matrix-group classifying space to projective
completion, formed through the proved finite-rank Grothendieck model. -/
def stableMap : C(ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)),
    ClassifyingSpace (Completion R)) :=
  (telescopeMap R).comp (originalStableToTelescope R)

/-- The actual stable map takes values in the zero path component. -/
def stableZeroMap : C(ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)),
    ZeroComponent R) :=
  (telescopeZeroMap R).comp (originalStableToTelescope R)

/-- Forgetting the zero-component restriction recovers exactly the original stable map. -/
@[simp]
lemma stableZeroMap_val (x : ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))) :
    (stableZeroMap R x).val = stableMap R x := rfl

/-- The actual telescope map restricts exactly to the original finite matrix map. -/
lemma telescopeMap_inclusion (n : ℕ) :
    (telescopeMap R).comp (classifyingSpaceMapUniversal
      (CategoryTheory.Grothendieck.ι (StableGeneralLinear.categoryDiagram R)
        (StableGeneralLinear.rankIndex n))) =
      classifyingSpaceMapUniversal (stageFunctor R n) := by
  rw [telescopeMap, ← classifyingSpaceMapUniversal_comp, inclusion_telescopeFunctor]

/-- The same stable comparison in the common-universe stable one-object model. -/
def smallStableMap : C(ClassifyingSpace (StableGeneralLinear.stableCategory R),
    ClassifyingSpace (Completion R)) :=
  (telescopeMap R).comp
    (StableGeneralLinear.GrothendieckModel.classifyingHomotopyEquiv R).symm.toFun

/-- The stable comparison retains the original finite-stage maps up to the proved
projection-inverse homotopy, rather than replacing those maps by abstract equivalences. -/
lemma smallStableMap_stage (n : ℕ) :
    ((smallStableMap R).comp (classifyingSpaceMap
      (StableGeneralLinear.smallFunctor (StableGeneralLinear.of R n))).hom).Homotopic
        (classifyingSpaceMapUniversal (stageFunctor R n)) := by
  let i := CategoryTheory.Grothendieck.ι (StableGeneralLinear.categoryDiagram R)
    (StableGeneralLinear.rankIndex n)
  let e := StableGeneralLinear.GrothendieckModel.classifyingHomotopyEquiv R
  have hi : e.toFun.comp (classifyingSpaceMap i).hom =
      (classifyingSpaceMap
        (StableGeneralLinear.smallFunctor (StableGeneralLinear.of R n))).hom := by
    change ((classifyingSpaceMap (StableGeneralLinear.GrothendieckModel.projection R)).hom).comp
      (classifyingSpaceMap i).hom = _
    rw [← TopCat.hom_comp, ← classifyingSpaceMap_comp,
      StableGeneralLinear.GrothendieckModel.inclusion_projection]
  have ht : (telescopeMap R).comp (classifyingSpaceMap i).hom =
      classifyingSpaceMapUniversal (stageFunctor R n) := by
    simpa only [classifyingSpaceMapUniversal_eq] using telescopeMap_inclusion R n
  rw [← hi, ← ht]
  change ((telescopeMap R).comp e.invFun |>.comp
    (e.toFun.comp (classifyingSpaceMap i).hom)).Homotopic _
  simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
    (ContinuousMap.Homotopic.refl (telescopeMap R)).comp
      (e.left_inv.comp (ContinuousMap.Homotopic.refl (classifyingSpaceMap i).hom))

end ModuleCat.FiniteProjective.StableCompletion
