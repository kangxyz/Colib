/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.SimplexAttachmentDeformation
public import Colib.Topology.Category.TopCat.PushoutInteriors

/-!
Adapted from `Quillen/Topology/Realization/SimplexAttachmentRelativeCharts.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original pair maps.

# Actual relative charts for arbitrarily parametrized simplex attachments

The original geometric boundary and the original old-space image have genuine
open collar neighborhoods. Their inclusions are homotopy equivalences, and the
original characteristic map is a homeomorphism of the complementary interior
charts and of their collar intersections. All parameter spaces and all dimensions
are allowed, including the empty-boundary case in dimension zero.
-/

@[expose] public section

open Topology
noncomputable section
open CategoryTheory Limits _root_.stdSimplex TopCat
open scoped Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.SimplexAttachment

/-- Product coordinates on the actual subspace cut out in the simplex factor. -/
def sourceSubspaceHomeomorph (X : TopCat.{u}) (n : ℕ)
    (U : Set (_root_.stdSimplex ℝ (Fin (n + 1)))) :
    (X × U) ≃ₜ {z : X × _root_.stdSimplex ℝ (Fin (n + 1)) // z.2 ∈ U} where
  toFun z := ⟨(z.1, z.2.val), z.2.property⟩
  invFun z := (z.val.1, ⟨z.val.2, z.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The actual boundary subspace of the parameterized geometric simplex. -/
def sourceBoundary (X : TopCat.{u}) (n : ℕ) : Set (X × _root_.stdSimplex ℝ (Fin (n + 1))) :=
  {z | z.2 ∈ _root_.stdSimplex.boundary n}

/-- The open radial collar in the parameterized geometric simplex. -/
def sourceCollar (X : TopCat.{u}) (n : ℕ) : Set (X × _root_.stdSimplex ℝ (Fin (n + 1))) :=
  {z | z.2 ∈ simplexBoundaryCollar n}

/-- The entire parameterized interior, rather than one point-parameter slice. -/
def sourceInterior (X : TopCat.{u}) (n : ℕ) : Set (X × _root_.stdSimplex ℝ (Fin (n + 1))) :=
  (sourceBoundary X n)ᶜ

/-- The geometric boundary is exactly the image of the original attaching inclusion. -/
theorem range_boundaryInclusion (X : TopCat.{u}) (n : ℕ) :
    Set.range (TopCat.parameterizedSimplexBoundaryInclusion X n) = sourceBoundary X n := by
  ext z
  constructor
  · rintro ⟨⟨x, b⟩, rfl⟩
    exact b.property
  · intro hz
    exact ⟨(z.1, ⟨z.2, hz⟩), rfl⟩

theorem sourceBoundary_subset_collar (X : TopCat.{u}) (n : ℕ) :
    sourceBoundary X n ⊆ sourceCollar X n := fun _ hz ↦ simplexBoundary_subset_collar n hz

theorem sourceCollar_isOpen (X : TopCat.{u}) (n : ℕ) : IsOpen (sourceCollar X n) :=
  (isOpen_simplexBoundaryCollar n).preimage continuous_snd

theorem sourceInterior_isOpen (X : TopCat.{u}) (n : ℕ) : IsOpen (sourceInterior X n) :=
  ((isClosed_boundary n).preimage continuous_snd).isOpen_compl

theorem sourceInterior_union_collar (X : TopCat.{u}) (n : ℕ) :
    sourceInterior X n ∪ sourceCollar X n = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro z
  by_cases hz : z ∈ sourceBoundary X n
  · exact Or.inr (sourceBoundary_subset_collar X n hz)
  · exact Or.inl hz

/-- The actual included boundary is homotopy equivalent to the open source collar. -/
def sourceBoundaryCollarEquiv (X : TopCat.{u}) (n : ℕ) :
    ContinuousMap.HomotopyEquiv (sourceBoundary X n) (sourceCollar X n) :=
  ((sourceSubspaceHomeomorph X n (_root_.stdSimplex.boundary n)).symm.toHomotopyEquiv.trans
    ((ContinuousMap.HomotopyEquiv.refl X).prodCongr
      (simplexBoundaryCollarHomotopyEquiv n))).trans
    (sourceSubspaceHomeomorph X n (simplexBoundaryCollar n)).toHomotopyEquiv

@[simp]
theorem sourceBoundaryCollarEquiv_apply (X : TopCat.{u}) (n : ℕ)
    (z : sourceBoundary X n) :
    ((sourceBoundaryCollarEquiv X n).toFun z).val = z.val := rfl

variable (X : TopCat.{u}) (n : ℕ) {B D : TopCat.{u}}
  {f : TopCat.of (X × _root_.stdSimplex.boundary n) ⟶ B}
  {g : TopCat.of (X × _root_.stdSimplex ℝ (Fin (n + 1))) ⟶ D} {j : B ⟶ D}
  (sq : IsPushout (TopCat.parameterizedSimplexBoundaryInclusion X n) f g j)

/-- The original old-space image, with its actual subspace topology. -/
def baseImage : Set D := Set.range j

/-- The entire open complement of the original old-space image. -/
def targetInterior : Set D := (baseImage (j := j))ᶜ

/-- The actual old space is homeomorphic to its closed embedded image. -/
def baseImageHomeomorph : B ≃ₜ baseImage (j := j) :=
  (simplexAttachment_old_isClosedEmbedding X n sq).isEmbedding.toHomeomorph

theorem baseImage_subset_collar : baseImage (j := j) ⊆ simplexAttachmentCollar X n sq :=
  range_old_subset_simplexAttachmentCollar X n sq

include sq in
theorem targetInterior_isOpen : IsOpen (targetInterior (j := j)) :=
  (simplexAttachment_old_isClosedEmbedding X n sq).isClosed_range.isOpen_compl

theorem targetInterior_union_collar :
    targetInterior (j := j) ∪ simplexAttachmentCollar X n sq = Set.univ := by
  classical
  apply Set.eq_univ_iff_forall.mpr
  intro z
  by_cases hz : z ∈ baseImage (j := j)
  · exact Or.inr (baseImage_subset_collar X n sq hz)
  · exact Or.inl hz

/-- The original image-subspace inclusion is homotopy equivalent to the target collar. -/
def baseImageCollarEquiv :
    ContinuousMap.HomotopyEquiv (baseImage (j := j)) (simplexAttachmentCollar X n sq) :=
  (baseImageHomeomorph X n sq).symm.toHomotopyEquiv.trans
    (simplexAttachmentCollarHomotopyEquiv X n sq)

@[simp]
theorem baseImageCollarEquiv_apply (z : baseImage (j := j)) :
    ((baseImageCollarEquiv X n sq).toFun z).val = z.val := by
  exact congrArg Subtype.val ((baseImageHomeomorph X n sq).apply_symm_apply z)

include sq in
/-- The original cell map respects the original distinguished subspaces. -/
theorem cell_mapsTo_boundary : Set.MapsTo g (sourceBoundary X n) (baseImage (j := j)) := by
  intro z hz
  refine ⟨f (z.1, ⟨z.2, hz⟩), ?_⟩
  exact (ConcreteCategory.congr_hom sq.w (z.1, ⟨z.2, hz⟩)).symm

theorem cell_mapsTo_collar :
    Set.MapsTo g (sourceCollar X n) (simplexAttachmentCollar X n sq) := by
  intro z hz
  exact (simplexAttachmentCollar_cell_iff X n sq z).mpr hz

/-- The original cell complement is homeomorphic to the actual target complement. -/
def cellInteriorHomeomorph : sourceInterior X n ≃ₜ targetInterior (j := j) :=
  ((Homeomorph.setCongr (congrArg (fun S : Set (X × _root_.stdSimplex ℝ (Fin (n + 1))) ↦ Sᶜ)
      (range_boundaryInclusion X n)).symm).trans
    (isOpenEmbedding_pushout_cell_compl sq
      (isClosedEmbedding_parameterizedSimplexBoundary X n)).isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr (range_pushout_cell_compl sq
      (isClosedEmbedding_parameterizedSimplexBoundary X n).injective))

@[simp]
theorem cellInteriorHomeomorph_apply (z : sourceInterior X n) :
    (cellInteriorHomeomorph X n sq z).val = g z.val := rfl

include sq in
theorem cell_mapsTo_interior :
    Set.MapsTo g (sourceInterior X n) (targetInterior (j := j)) := by
  intro z hz
  exact (cellInteriorHomeomorph X n sq ⟨z, hz⟩).property

/-- The interior chart preserves the actual radial collar membership exactly. -/
theorem cellInteriorHomeomorph_mem_collar (z : sourceInterior X n) :
    z.val ∈ sourceCollar X n ↔
      (cellInteriorHomeomorph X n sq z).val ∈ simplexAttachmentCollar X n sq :=
  (simplexAttachmentCollar_cell_iff X n sq z.val).symm

/-- The original interior map is a homeomorphism of the nested collar intersections. -/
def cellInteriorCollarHomeomorph :
    {z : sourceInterior X n // z.val ∈ sourceCollar X n} ≃ₜ
      {z : targetInterior (j := j) // z.val ∈ simplexAttachmentCollar X n sq} :=
  (cellInteriorHomeomorph X n sq).subtype (cellInteriorHomeomorph_mem_collar X n sq)

end TopCat.SimplexAttachment
