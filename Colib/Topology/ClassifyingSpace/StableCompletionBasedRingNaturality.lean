/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.StableCompletionBaseChangeNaturality
public import Colib.Topology.ClassifyingSpace.UniverseHomotopyTracks
public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletionBasedSurjectivity

/-!
# Based change of rings for the original stable completion map

The original stable projection is a based homotopy equivalence. Its chosen
inverse track identifies the corrected stable completion map with the original
telescope map on every homotopy set. The exact finite-free comparison edge then
gives naturality by cancelling the projection's bijective homotopy maps. No
naturality of chosen homotopy inverses or trivial fundamental-group action is
assumed.

## Implementation provenance

Adapted from `Quillen/KTheory/Plus/StableCompletionBasedRingNaturality.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/

@[expose] public section

open StableGeneralLinear.GrothendieckModel

noncomputable section
open Topology SSet HomotopyGroup
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  ModuleCat.FiniteProjective.categoryDirectSumMonoidal
  ModuleCat.FiniteProjective.directSumMonoidal
  ModuleCat.FiniteProjective.rightBaseChangeMonoidal
namespace ModuleCat.FiniteProjective.StableCompletion
open StableGeneralLinear.GrothendieckModel
variable {R S : Type u} [Ring R] [Ring S]

/-- The actual stable projection, followed by the original universe homeomorphism. -/
def originalTelescopeProjection (R : Type u) [Ring R] :
    C(ClassifyingSpace (Telescope R),
      ClassifyingSpace (SingleObj (StableGeneralLinear.Group R))) :=
  (originalStableTelescopeEquiv R).invFun

/-- The original projection sends the actual rank-zero vertex to the stable vertex. -/
lemma originalTelescopeProjection_point (R : Type u) [Ring R] :
    originalTelescopeProjection R (classifyingSpacePoint (telescopeBase R)) =
      stableBase R := by
  let h := CategoryTheory.asSmallClassifyingHomeomorph
    (SingleObj (StableGeneralLinear.Group R))
  apply h.injective
  change h (h.symm (classifyingSpaceMap (projection R)
    (classifyingSpacePoint (telescopeBase R)))) = h (stableBase R)
  rw [h.apply_symm_apply, classifyingSpaceMap_point]
  exact (CategoryTheory.asSmallClassifyingHomeomorph_point
    (SingleObj (StableGeneralLinear.Group R)) (SingleObj.star _)).symm

/-- The original projection induces bijections, including in degree zero. -/
lemma originalTelescopeProjection_homotopyGroupMap_bijective (R : Type u) [Ring R]
    (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (originalTelescopeProjection R)
      (originalTelescopeProjection_point R)) :=
  homotopyGroupMap_bijective_of_homotopyEquiv (originalStableTelescopeEquiv R).symm
    (originalTelescopeProjection_point R) n

/-- Cancelling the original universe homeomorphism retains the chosen inverse composite. -/
lemma originalStableToTelescope_originalTelescopeProjection (R : Type u) [Ring R] :
    (originalStableToTelescope R).comp (originalTelescopeProjection R) =
      (classifyingHomotopyEquiv R).invFun.comp (classifyingHomotopyEquiv R).toFun := by
  ext x
  change (classifyingHomotopyEquiv R).invFun
    ((CategoryTheory.asSmallClassifyingHomeomorph
      (SingleObj (StableGeneralLinear.Group R)))
      ((CategoryTheory.asSmallClassifyingHomeomorph
        (SingleObj (StableGeneralLinear.Group R))).symm
        ((classifyingHomotopyEquiv R).toFun x))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

/-- The displayed stable-projection composite uses the original inverse homotopy. -/
def stableProjectionZeroHomotopy (R : Type u) [Ring R] :
    ((stableZeroMap R).comp (originalTelescopeProjection R)).Homotopy
      (telescopeZeroMap R) :=
  (zeroInverseHomotopy R).cast (by
    rw [← originalStableToTelescope_originalTelescopeProjection]
    rfl) (by rfl)

/-- Its whole vertex track is the original stable basepoint path. -/
lemma stableProjectionZeroHomotopy_track (R : Type u) [Ring R] (t : unitInterval) :
    stableProjectionZeroHomotopy R (t, classifyingSpacePoint (telescopeBase R)) =
      basepointPath R t := rfl

/-- The original inverse correction exactly cancels the actual projection in every degree. -/
theorem stableZeroMap_homotopyGroupMap_projection (R : Type u) [Ring R] (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace (Telescope R))
      (classifyingSpacePoint (telescopeBase R))) :
    pathTransport (basepointPath R) n
      (HomotopyGroup.map (stableZeroMap R) rfl
        (HomotopyGroup.map (originalTelescopeProjection R)
          (originalTelescopeProjection_point R) a)) =
      HomotopyGroup.map (telescopeZeroMap R) (telescopeZeroMap_point R) a := by
  rw [← HomotopyGroup.map_comp (originalTelescopeProjection R)
    (originalTelescopeProjection_point R) (stableZeroMap R) rfl]
  have ht : ((stableProjectionZeroHomotopy R).evalAt
      (classifyingSpacePoint (telescopeBase R))).cast
      (congrArg (stableZeroMap R) (originalTelescopeProjection_point R)).symm
      (telescopeZeroMap_point R).symm = basepointPath R := by
    ext t
    rfl
  rw [← ht]
  exact pathTransport_homotopyGroupMap_homotopy_cast (stableProjectionZeroHomotopy R)
    (classifyingSpacePoint (telescopeBase R))
    (congrArg (stableZeroMap R) (originalTelescopeProjection_point R))
    (telescopeZeroMap_point R) n a

/-- The matrix ring functor preserves the actual rank-zero vertex. -/
lemma ringFunctor_telescopeBase (f : R →+* S) :
    (ringFunctor f).obj (telescopeBase R) = telescopeBase S := rfl

/-- The original realized telescope ring map is strictly based at rank zero. -/
lemma ringFunctor_point (f : R →+* S) :
    classifyingSpaceMap (ringFunctor f) (classifyingSpacePoint (telescopeBase R)) =
      classifyingSpacePoint (telescopeBase S) :=
  classifyingSpaceMap_point (ringFunctor f) (telescopeBase R)

/-- The original stable ring map preserves the unique object vertex. -/
lemma stableRingMap_point (f : R →+* S) :
    classifyingSpaceMap (StableGeneralLinear.map f).toFunctor (stableBase R) =
      stableBase S :=
  classifyingSpaceMap_point (StableGeneralLinear.map f).toFunctor (SingleObj.star _)

/-- The actual projection square is strictly natural on the original stable spaces. -/
lemma originalTelescopeProjection_ringMap (f : R →+* S) :
    (originalTelescopeProjection S).comp (classifyingSpaceMap (ringFunctor f)).hom =
      (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom.comp
        (originalTelescopeProjection R) := by
  let hR := CategoryTheory.asSmallClassifyingHomeomorph
    (SingleObj (StableGeneralLinear.Group R))
  let hS := CategoryTheory.asSmallClassifyingHomeomorph
    (SingleObj (StableGeneralLinear.Group S))
  ext x
  apply hS.injective
  change hS (hS.symm (classifyingSpaceMap (projection S)
      (classifyingSpaceMap (ringFunctor f) x))) =
    hS (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor
      (hR.symm (classifyingSpaceMap (projection R) x)))
  rw [hS.apply_symm_apply, ← StableGeneralLinear.smallFunctor_classifying_naturality,
    hR.apply_symm_apply]
  exact congrArg (fun g => g x) (ringFunctor_projection_realization f)

/-- The actual finite-free natural isomorphism, realized before component restriction. -/
def telescopeBaseChangeHomotopy (f : R →+* S) :
    ((completionBaseChangeMap f).comp (telescopeMap R)).Homotopy
      ((telescopeMap S).comp (classifyingSpaceMap (ringFunctor f)).hom) :=
  (classifyingSpaceUniversalHomotopy (telescopeBaseChangeIso f).hom).cast
    (classifyingSpaceMapUniversal_comp _ _)
    (by rw [classifyingSpaceMapUniversal_comp, classifyingSpaceMapUniversal_eq]; rfl)

/-- Restrict the original homotopy to the genuine zero component, point for point. -/
def telescopeZeroBaseChangeHomotopy (f : R →+* S) :
    ((zeroCompletionBaseChangeMap f).comp (telescopeZeroMap R)).Homotopy
      ((telescopeZeroMap S).comp (classifyingSpaceMap (ringFunctor f)).hom) where
  toFun z := ⟨telescopeBaseChangeHomotopy f z,
    path_mem_pathComponent ((telescopeBaseChangeHomotopy f).evalAt z.2)
      (zeroCompletionBaseChangeMap f (telescopeZeroMap R z.2)).property z.1⟩
  continuous_toFun := (telescopeBaseChangeHomotopy f).continuous.subtype_mk _
  map_zero_left x := Subtype.ext ((telescopeBaseChangeHomotopy f).apply_zero x)
  map_one_left x := Subtype.ext ((telescopeBaseChangeHomotopy f).apply_one x)

/-- The rank-zero track is the prescribed original unit-comparison path. -/
lemma telescopeZeroBaseChangeHomotopy_track (f : R →+* S) (t : unitInterval) :
    telescopeZeroBaseChangeHomotopy f (t, classifyingSpacePoint (telescopeBase R)) =
      zeroCompletionBaseChangeBasepointPath f t := by
  apply Subtype.ext
  change classifyingSpaceUniversalHomotopy (telescopeBaseChangeIso f).hom
    (t, classifyingSpacePoint (telescopeBase R)) =
      classifyingSpacePath (completionBaseChangeZeroIso f).hom t
  rw [classifyingSpaceUniversalHomotopy_vertex_track]
  change classifyingSpacePath (stageBaseChangeIso f 0).hom t = _
  rw [stageBaseChangeIso_zero]

/-- Naturality on the original telescope, with exactly the prescribed completion correction. -/
theorem telescopeZeroMap_homotopyGroupMap_ringMap (f : R →+* S) (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace (Telescope R))
      (classifyingSpacePoint (telescopeBase R))) :
    pathTransport (zeroCompletionBaseChangeBasepointPath f) n
      (HomotopyGroup.map (zeroCompletionBaseChangeMap f) rfl
        (HomotopyGroup.map (telescopeZeroMap R) (telescopeZeroMap_point R) a)) =
      HomotopyGroup.map (telescopeZeroMap S) (telescopeZeroMap_point S)
        (HomotopyGroup.map (classifyingSpaceMap (ringFunctor f)).hom
          (ringFunctor_point f) a) := by
  rw [← HomotopyGroup.map_comp (telescopeZeroMap R) (telescopeZeroMap_point R)
    (zeroCompletionBaseChangeMap f) rfl,
    ← HomotopyGroup.map_comp (classifyingSpaceMap (ringFunctor f)).hom
      (ringFunctor_point f) (telescopeZeroMap S) (telescopeZeroMap_point S)]
  have ht : ((telescopeZeroBaseChangeHomotopy f).evalAt
      (classifyingSpacePoint (telescopeBase R))).cast
      (congrArg (zeroCompletionBaseChangeMap f) (telescopeZeroMap_point R)).symm
      ((congrArg (telescopeZeroMap S) (ringFunctor_point f)).trans
        (telescopeZeroMap_point S)).symm = zeroCompletionBaseChangeBasepointPath f := by
    apply Path.ext
    funext t
    exact telescopeZeroBaseChangeHomotopy_track f t
  rw [← ht]
  exact pathTransport_homotopyGroupMap_homotopy_cast (telescopeZeroBaseChangeHomotopy f)
    (classifyingSpacePoint (telescopeBase R))
    (congrArg (zeroCompletionBaseChangeMap f) (telescopeZeroMap_point R))
    ((congrArg (telescopeZeroMap S) (ringFunctor_point f)).trans
      (telescopeZeroMap_point S)) n a

/-- Change of rings commutes with the original corrected stable map in every degree. -/
theorem stableZeroMap_homotopyGroupMap_ringMap (f : R →+* S) (n : ℕ)
    (a : HomotopyGroup.Pi n (ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)))
      (stableBase R)) :
    pathTransport (zeroCompletionBaseChangeBasepointPath f) n
      (HomotopyGroup.map (zeroCompletionBaseChangeMap f) rfl
        (pathTransport (basepointPath R) n (HomotopyGroup.map (stableZeroMap R) rfl a))) =
      pathTransport (basepointPath S) n
        (HomotopyGroup.map (stableZeroMap S) rfl
          (HomotopyGroup.map (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom
            (stableRingMap_point f) a)) := by
  obtain ⟨b, rfl⟩ := (originalTelescopeProjection_homotopyGroupMap_bijective R n).surjective a
  rw [stableZeroMap_homotopyGroupMap_projection, telescopeZeroMap_homotopyGroupMap_ringMap]
  rw [← stableZeroMap_homotopyGroupMap_projection S n]
  congr 2
  rw [← HomotopyGroup.map_comp (classifyingSpaceMap (ringFunctor f)).hom
      (ringFunctor_point f) (originalTelescopeProjection S)
      (originalTelescopeProjection_point S),
    ← HomotopyGroup.map_comp (originalTelescopeProjection R)
      (originalTelescopeProjection_point R)
      (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom (stableRingMap_point f)]
  exact congrFun (homotopyGroupMap_congr (originalTelescopeProjection_ringMap f) _ _) b

/-- The same square as an equality of the actual based fundamental-group homomorphisms. -/
theorem stablePiOneMap_ringMap (f : R →+* S) :
    ((pathTransportMulEquiv (zeroCompletionBaseChangeBasepointPath f) 0).toMonoidHom.comp
      (HomotopyGroup.piMap 0 (zeroCompletionBaseChangeMap f) (x := zeroBase R) rfl)).comp
        (stablePiOneMap R) =
      (stablePiOneMap S).comp
        (HomotopyGroup.piMap 0 (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom
          (stableRingMap_point f)) := by
  apply MonoidHom.ext
  exact stableZeroMap_homotopyGroupMap_ringMap f 1

end ModuleCat.FiniteProjective.StableCompletion
