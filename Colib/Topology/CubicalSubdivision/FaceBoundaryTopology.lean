/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.FaceComplex
public import Colib.Topology.HELP.CubeBoundaryHomeomorph

/-! # Actual face-boundary tests in an arbitrary common universe

Only the finite coordinate set is reindexed and the universe is lifted. The
original parameter and boundary coordinates are retained by explicit
homeomorphisms, so HLP/HELP targets need not be universe zero.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/FaceBoundaryTopology.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision
universe u

/-- The unit cube on the active coordinates of the face `F`, lifted to the chosen universe. -/
abbrev FaceCube {n m : ℕ} (F : FaceIndex n m) := ULift.{u} (Active F → unitInterval)
/-- The boundary subspace of `FaceCube F`, where an active interval coordinate is zero or one,
with the same universe lift. -/
abbrev FaceCubeBoundary {n m : ℕ} (F : FaceIndex n m) :=
  {z : FaceCube.{u} F // z.down ∈ _root_.Cube.boundary (Active F)}

/-- Reindex the finite set of active face coordinates by `Fin (faceDimension F)`. -/
def activeEquivFin {n m : ℕ} (F : FaceIndex n m) : Active F ≃ Fin (faceDimension F) :=
  Fintype.equivFin (Active F)

/-- The actual finite-coordinate reindexing in the required common universe. -/
def faceCubeHomeomorph {n m : ℕ} (F : FaceIndex n m) :
    FaceCube.{u} F ≃ₜ CubicalTests.cube.{u} (faceDimension F) where
  toFun t := ⟨fun j ↦ t.down ((activeEquivFin F).symm j)⟩
  invFun t := ⟨fun i ↦ t.down (activeEquivFin F i)⟩
  left_inv t := by apply ULift.ext; funext i; simp
  right_inv t := by apply ULift.ext; funext i; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem faceCubeHomeomorph_apply {n m : ℕ} (F : FaceIndex n m)
    (t : FaceCube.{u} F) (j : Fin (faceDimension F)) :
    (faceCubeHomeomorph F t).down j = t.down ((activeEquivFin F).symm j) := rfl

theorem faceCubeHomeomorph_boundary_iff {n m : ℕ} (F : FaceIndex n m) (t : FaceCube.{u} F) :
    (faceCubeHomeomorph F t).down ∈ _root_.Cube.boundary (Fin (faceDimension F)) ↔
      t.down ∈ _root_.Cube.boundary (Active F) := by
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨(activeEquivFin F).symm j,hj⟩
  · rintro ⟨i,hi⟩
    refine ⟨activeEquivFin F i,?_⟩
    change t.down ((activeEquivFin F).symm ((activeEquivFin F) i)) = 0 ∨
      t.down ((activeEquivFin F).symm ((activeEquivFin F) i)) = 1
    rw [(activeEquivFin F).symm_apply_apply i]
    exact hi

/-- The same exact coordinate reindexing on the entire actual boundary. -/
def faceCubeBoundaryHomeomorph {n m : ℕ} (F : FaceIndex n m) :
    FaceCubeBoundary.{u} F ≃ₜ CubicalTests.boundary.{u} (faceDimension F) where
  toFun z := ⟨faceCubeHomeomorph F z.val,(faceCubeHomeomorph_boundary_iff F z.val).mpr z.2⟩
  invFun z := ⟨(faceCubeHomeomorph F).symm z.val,by
    apply (faceCubeHomeomorph_boundary_iff F _).mp
    simpa only [Homeomorph.apply_symm_apply] using z.2⟩
  left_inv z := Subtype.ext ((faceCubeHomeomorph F).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((faceCubeHomeomorph F).apply_symm_apply z.val)
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

instance faceCube_compactSpace {n m : ℕ} (F : FaceIndex n m) : CompactSpace (FaceCube.{u} F) :=
  inferInstanceAs (CompactSpace (ULift.{u} (Active F → unitInterval)))

instance faceCubeBoundary_compactSpace {n m : ℕ} (F : FaceIndex n m) :
    CompactSpace (FaceCubeBoundary.{u} F) := by
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} (faceDimension F)).space :=
    (CubicalTests.boundaryPresentation (faceDimension F)).compact
  exact ((CubicalTests.boundaryPresentationHomeomorph (faceDimension F)).trans
    (faceCubeBoundaryHomeomorph F).symm).compactSpace

/-- The literal inclusion of the whole face boundary in the lifted cube. -/
def faceBoundaryInclusion {n m : ℕ} (F : FaceIndex n m) :
    TopCat.of (FaceCubeBoundary.{u} F) ⟶ TopCat.of (FaceCube.{u} F) :=
  TopCat.ofHom ⟨Subtype.val,continuous_subtype_val⟩

/-- Its factorization retains both actual parameter maps exactly. -/
theorem faceBoundaryInclusion_factorization {n m : ℕ} (F : FaceIndex n m) :
    (TopCat.isoOfHomeo (faceCubeBoundaryHomeomorph.{u} F)).hom ≫
      CubicalTests.boundaryInclusion (faceDimension F) ≫
      (TopCat.isoOfHomeo (faceCubeHomeomorph.{u} F)).inv = faceBoundaryInclusion F := by
  ext z : 1
  exact (faceCubeHomeomorph F).symm_apply_apply z.val

/-- Genuine HEP of the original face boundary, in arbitrary TopCat universe. -/
theorem faceBoundaryInclusion_hep {n m : ℕ} (F : FaceIndex n m) :
    TopCat.HomotopyExtensionProperty (faceBoundaryInclusion.{u} F) := by
  rw [← faceBoundaryInclusion_factorization]
  exact TopCat.homotopyExtensionProperty_comp (TopCat.homotopyExtensionProperty_of_isIso _)
    (TopCat.homotopyExtensionProperty_comp (CubicalTests.boundaryInclusion_hep _)
      (TopCat.homotopyExtensionProperty_of_isIso _))

/-- Remove only ULift on the boundary; the actual coordinates stay unchanged. -/
def faceBoundaryUnliftedHomeomorph {n m : ℕ} (F : FaceIndex n m) :
    FaceCubeBoundary.{u} F ≃ₜ
      {t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)} where
  toFun z := ⟨z.val.down,z.2⟩
  invFun z := ⟨⟨z.val⟩,z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem faceBoundaryUnliftedHomeomorph_apply {n m : ℕ} (F : FaceIndex n m)
    (z : FaceCubeBoundary.{u} F) : (faceBoundaryUnliftedHomeomorph F z).val = z.val.down := rfl

end Topology.CubicalSubdivision
