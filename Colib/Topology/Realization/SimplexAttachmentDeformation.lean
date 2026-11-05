/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.SimplexAttachmentCollar
public import Colib.Topology.Realization.Cylinder

/-!
# Deforming a simplex-attachment collar onto the previous space

The boundary-fixed radial deformation descends through the actual topological
pushout. The previous space is a strong deformation retract of the resulting
open neighborhood, including for arbitrary parameter spaces.

## Implementation provenance

Adapted from all fifteen declarations of
`Quillen/Topology/Realization/EdgePathPresentation/Deformation.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual pushout, cylinder descent,
radial map, endpoint equations and relative homotopy are retained. Only native
namespace and lower import ownership change. No homotopy extension property,
separation axiom or compactness of the parameter space is assumed.
-/
@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Convexity Topology Set
open Convexity.StdSimplex
open scoped Topology unitInterval

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TopCat

section SimplexAttachment

variable (X : TopCat.{u}) (n : ℕ) {C D : TopCat.{u}}
    {f : TopCat.of (X × simplexBoundary n) ⟶ C}
    {g : TopCat.of (X × StdSimplex ℝ (Fin (n + 1))) ⟶ D}
    {j : C ⟶ D}
    (sq : IsPushout (TopCat.parameterizedSimplexBoundaryInclusion X n) f g j)

/-- The radial deformation on the attached cells, glued to the constant
homotopy on the previous space using preservation of pushouts by cylinders. -/
def simplexAttachmentRadialCylinder : D ⊗ TopCat.I ⟶ D := by
  let b : TopCat.of (X × StdSimplex ℝ (Fin (n + 1))) ⊗ TopCat.I ⟶ D :=
    TopCat.ofHom ⟨fun z ↦ g (z.1.1, simplexBoundaryRetractPoint (z.1.2, z.2.down)), by fun_prop⟩
  let c : C ⊗ TopCat.I ⟶ D :=
    TopCat.ofHom ⟨fun z ↦ j z.1, by fun_prop⟩
  have h : (TopCat.parameterizedSimplexBoundaryInclusion X n ▷ TopCat.I) ≫ b =
      (f ▷ TopCat.I) ≫ c := by
    apply ConcreteCategory.hom_ext
    intro z
    change g (z.1.1, simplexBoundaryRetractPoint (z.1.2.1, z.2.down)) = j (f z.1)
    rw [simplexBoundaryRetractPoint_boundary]
    exact ConcreteCategory.congr_hom sq.w z.1
  exact (sq.map (tensorRight TopCat.I)).desc b c h

/-- The descended radial deformation, with ordinary unit-interval parameter. -/
def simplexAttachmentRadial : C(unitInterval × D, D) where
  toFun z := simplexAttachmentRadialCylinder X n sq (z.2, ULift.up z.1)
  continuous_toFun := (simplexAttachmentRadialCylinder X n sq).hom.continuous.comp
    (continuous_snd.prodMk (continuous_uliftUp.comp continuous_fst))

@[simp] theorem simplexAttachmentRadial_cell (t : unitInterval)
    (z : X × StdSimplex ℝ (Fin (n + 1))) :
    simplexAttachmentRadial X n sq (t, g z) =
      g (z.1, simplexBoundaryRetractPoint (z.2, t)) := by
  change simplexAttachmentRadialCylinder X n sq ((g ▷ TopCat.I) (z, ULift.up t)) = _
  dsimp only [simplexAttachmentRadialCylinder]
  rw [← ConcreteCategory.comp_apply]
  erw [(sq.map (tensorRight TopCat.I)).inl_desc]
  rfl

@[simp] theorem simplexAttachmentRadial_old (t : unitInterval) (c : C) :
    simplexAttachmentRadial X n sq (t, j c) = j c := by
  change simplexAttachmentRadialCylinder X n sq ((j ▷ TopCat.I) (c, ULift.up t)) = _
  dsimp only [simplexAttachmentRadialCylinder]
  rw [← ConcreteCategory.comp_apply]
  erw [(sq.map (tensorRight TopCat.I)).inr_desc]
  rfl

@[simp] theorem simplexAttachmentRadial_zero (z : D) :
    simplexAttachmentRadial X n sq (0, z) = z := by
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) z with ⟨b, rfl⟩ | ⟨c, rfl⟩
  · change simplexAttachmentRadial X n sq (0, g b) = g b
    rw [simplexAttachmentRadial_cell, simplexBoundaryRetractPoint_zero]
  · exact simplexAttachmentRadial_old X n sq 0 c

/-- The descended deformation stays inside the open collar. -/
theorem simplexAttachmentRadial_mem_collar (t : unitInterval)
    (z : simplexAttachmentCollar X n sq) :
    simplexAttachmentRadial X n sq (t, z.1) ∈ simplexAttachmentCollar X n sq := by
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) z.1 with ⟨b, hb⟩ | ⟨c, hc⟩
  · change g b = z.1 at hb
    have hz : b.2 ∈ simplexBoundaryCollar n :=
      (simplexAttachmentCollar_cell_iff X n sq b).mp (hb.symm ▸ z.2)
    rw [← hb, simplexAttachmentRadial_cell]
    apply (simplexAttachmentCollar_cell_iff X n sq _).mpr
    exact simplexBoundaryRetractPoint_mem_collar ⟨b.2, hz⟩ t
  · change j c = z.1 at hc
    rw [← hc, simplexAttachmentRadial_old]
    exact range_old_subset_simplexAttachmentCollar X n sq (Set.mem_range_self c)

/-- Every point of the collar reaches the previous space at time one. -/
theorem simplexAttachmentRadial_one_mem_range
    (z : simplexAttachmentCollar X n sq) :
    simplexAttachmentRadial X n sq (1, z.1) ∈ Set.range j := by
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) z.1 with ⟨b, hb⟩ | ⟨c, hc⟩
  · change g b = z.1 at hb
    have hz : b.2 ∈ simplexBoundaryCollar n :=
      (simplexAttachmentCollar_cell_iff X n sq b).mp (hb.symm ▸ z.2)
    let a : X × simplexBoundary n :=
      (b.1, ⟨simplexBoundaryRetractPoint (b.2, 1),
        simplexBoundaryRetractPoint_one_mem_boundary ⟨b.2, hz⟩⟩)
    refine ⟨f a, ?_⟩
    rw [← hb, simplexAttachmentRadial_cell]
    exact (ConcreteCategory.congr_hom sq.w a).symm
  · change j c = z.1 at hc
    rw [← hc, simplexAttachmentRadial_old]
    exact Set.mem_range_self c

/-- The previous space included into its open collar neighborhood. -/
def simplexAttachmentCollarInclusion : C(C, simplexAttachmentCollar X n sq) where
  toFun c := ⟨j c, range_old_subset_simplexAttachmentCollar X n sq (Set.mem_range_self c)⟩
  continuous_toFun := j.hom.continuous.subtype_mk _

/-- The set-theoretic retraction is uniquely specified because the previous
space is embedded in the pushout. -/
def simplexAttachmentCollarRetractionFun (z : simplexAttachmentCollar X n sq) : C :=
  (simplexAttachmentRadial_one_mem_range X n sq z).choose

@[simp] theorem simplexAttachmentCollarRetractionFun_spec
    (z : simplexAttachmentCollar X n sq) :
    j (simplexAttachmentCollarRetractionFun X n sq z) =
      simplexAttachmentRadial X n sq (1, z.1) :=
  (simplexAttachmentRadial_one_mem_range X n sq z).choose_spec

/-- Continuity of the retraction follows from the actual subspace embedding,
not merely from its set-theoretic description. -/
def simplexAttachmentCollarRetraction : C(simplexAttachmentCollar X n sq, C) where
  toFun := simplexAttachmentCollarRetractionFun X n sq
  continuous_toFun := by
    apply (simplexAttachment_old_isClosedEmbedding X n sq).isInducing.continuous_iff.mpr
    have h : (fun z : simplexAttachmentCollar X n sq ↦
        j (simplexAttachmentCollarRetractionFun X n sq z)) =
        (fun z ↦ simplexAttachmentRadial X n sq (1, z.1)) := by
      funext z
      exact simplexAttachmentCollarRetractionFun_spec X n sq z
    rw [show j ∘ simplexAttachmentCollarRetractionFun X n sq = _ from h]
    exact (simplexAttachmentRadial X n sq).continuous.comp
      (continuous_const.prodMk continuous_subtype_val)

@[simp] theorem simplexAttachmentCollarRetraction_inclusion (c : C) :
    simplexAttachmentCollarRetraction X n sq (simplexAttachmentCollarInclusion X n sq c) = c := by
  apply (simplexAttachment_old_isClosedEmbedding X n sq).injective
  change j (simplexAttachmentCollarRetractionFun X n sq _) = j c
  rw [simplexAttachmentCollarRetractionFun_spec]
  exact simplexAttachmentRadial_old X n sq 1 c

/-- The actual open collar deformation, fixed on the entire previous space. -/
def simplexAttachmentCollarHomotopy :
    (ContinuousMap.id (simplexAttachmentCollar X n sq)).HomotopyRel
      ((simplexAttachmentCollarInclusion X n sq).comp
        (simplexAttachmentCollarRetraction X n sq))
      (Set.range (simplexAttachmentCollarInclusion X n sq)) where
  toFun z := ⟨simplexAttachmentRadial X n sq (z.1, z.2.1),
    simplexAttachmentRadial_mem_collar X n sq z.1 z.2⟩
  continuous_toFun := ((simplexAttachmentRadial X n sq).continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  map_zero_left z := Subtype.ext (simplexAttachmentRadial_zero X n sq z.1)
  map_one_left z := Subtype.ext (simplexAttachmentCollarRetractionFun_spec X n sq z).symm
  prop' t _ hx := by
    obtain ⟨c, rfl⟩ := hx
    exact Subtype.ext (simplexAttachmentRadial_old X n sq t c)

/-- A simplex attachment has a genuine open neighborhood of the old space
homotopy equivalent to it, via the exact old-space inclusion. -/
def simplexAttachmentCollarHomotopyEquiv :
    ContinuousMap.HomotopyEquiv C (simplexAttachmentCollar X n sq) where
  toFun := simplexAttachmentCollarInclusion X n sq
  invFun := simplexAttachmentCollarRetraction X n sq
  left_inv := by
    have h : (simplexAttachmentCollarRetraction X n sq).comp
        (simplexAttachmentCollarInclusion X n sq) = ContinuousMap.id C := by
      apply ContinuousMap.ext
      exact simplexAttachmentCollarRetraction_inclusion X n sq
    rw [h]
  right_inv := ⟨(simplexAttachmentCollarHomotopy X n sq).toHomotopy.symm⟩

/-- The global descended radial deformation as an ordinary homotopy. -/
def simplexAttachmentRadialHomotopy :
    (ContinuousMap.id D).Homotopy
      (⟨fun z ↦ simplexAttachmentRadial X n sq (1, z),
        (simplexAttachmentRadial X n sq).continuous.comp
          (continuous_const.prodMk continuous_id)⟩ : C(D, D)) where
  toFun := simplexAttachmentRadial X n sq
  continuous_toFun := (simplexAttachmentRadial X n sq).continuous
  map_zero_left := simplexAttachmentRadial_zero X n sq
  map_one_left _ := rfl

end SimplexAttachment

end TopCat

attribute [colib_tag "COL-0103",
  colib_ref "BoardmanPushouts" "Proposition 7 and Corollary 8, page 2"
    "ingredient"
    "Compatible homotopies descend through the pushout using the fixed interval"]
  TopCat.simplexAttachmentRadialCylinder
  TopCat.simplexAttachmentRadialHomotopy
  TopCat.simplexAttachmentCollarRetraction
  TopCat.simplexAttachmentCollarHomotopy
  TopCat.simplexAttachmentCollarHomotopyEquiv

attribute [colib_ref "HatcherAT" "Chapter 0, proof of Proposition 0.16, page 15"
  "background" "Radial deformation of the collar, not a general CW homotopy extension theorem"]
  TopCat.simplexAttachmentCollarHomotopy
  TopCat.simplexAttachmentCollarHomotopyEquiv
