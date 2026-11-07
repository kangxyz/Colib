/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Category.TopCat.Pushouts
public import Colib.Topology.Realization.SimplexBoundaryCollar

/-!
# The open collar in an actual parametrized simplex attachment

The actual product boundary inclusion is closed. For its pushout, the boundary
defect extends continuously across the old space by the value one. The strict
superlevel set at one half is an open neighborhood of the old space.

The parameter space is arbitrary. There is no discreteness, separation,
compactness or local connectedness hypothesis on it or the old space.

Adapted from `Quillen/Topology/Realization/EdgePathPresentation/Pushout.lean`
(all nine declarations after the generic pushout theorem), and the actual
`parameterizedSimplexBoundaryInclusion` definition from `SimplexBoundaryHEP.lean`,
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
No HEP theorem or radial deformation of the pushout is assumed or asserted.
The actual maps, coordinate formulas and universe parameters are retained.
-/
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits _root_.stdSimplex Topology Set
open scoped Topology unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TopCat

/-- The actual inclusion of a parametrized simplex boundary. -/
def parameterizedSimplexBoundaryInclusion (X : TopCat.{u}) (n : ℕ) :
    TopCat.of (X × _root_.stdSimplex.boundary n) ⟶
      TopCat.of (X × _root_.stdSimplex ℝ (Fin (n + 1))) :=
  TopCat.ofHom ⟨fun p ↦ (p.1, p.2.1), continuous_fst.prodMk
    (continuous_subtype_val.comp continuous_snd)⟩

/-- The actual inclusion of a parametrized geometric simplex boundary is
closed, without any separation or compactness assumption on the parameters. -/
theorem isClosedEmbedding_parameterizedSimplexBoundary
    (X : TopCat.{u}) (n : ℕ) :
    IsClosedEmbedding (TopCat.parameterizedSimplexBoundaryInclusion X n) := by
  exact (Homeomorph.refl X).isClosedEmbedding.prodMap
    (isClosed_boundary n).isClosedEmbedding_subtypeVal

section SimplexAttachment

variable (X : TopCat.{u}) (n : ℕ) {C D : TopCat.{u}}
    {f : TopCat.of (X × _root_.stdSimplex.boundary n) ⟶ C}
    {g : TopCat.of (X × _root_.stdSimplex ℝ (Fin (n + 1))) ⟶ D}
    {j : C ⟶ D}
    (sq : IsPushout (TopCat.parameterizedSimplexBoundaryInclusion X n) f g j)

/-- Extend the simplex's radial boundary coordinate across the old space,
where it has the constant value one. -/
def simplexAttachmentDefect : C(D, ℝ) := by
  let b : TopCat.of (X × _root_.stdSimplex ℝ (Fin (n + 1))) ⟶ TopCat.of (ULift.{u} ℝ) :=
    TopCat.ofHom ⟨fun z ↦ ULift.up (simplexBoundaryDefect z.2), by fun_prop⟩
  let c : C ⟶ TopCat.of (ULift.{u} ℝ) := TopCat.const (ULift.up (1 : ℝ))
  have h : TopCat.parameterizedSimplexBoundaryInclusion X n ≫ b = f ≫ c := by
    apply ConcreteCategory.hom_ext
    intro z
    change ULift.up (simplexBoundaryDefect z.2.1) = ULift.up (1 : ℝ)
    rw [(simplexBoundaryDefect_eq_one_iff z.2.1).mpr z.2.2]
  exact (⟨ULift.down, continuous_uliftDown⟩ : C(ULift.{u} ℝ, ℝ)).comp (sq.desc b c h).hom

@[simp] theorem simplexAttachmentDefect_cell (z : X × _root_.stdSimplex ℝ (Fin (n + 1))) :
    simplexAttachmentDefect X n sq (g z) = simplexBoundaryDefect z.2 := by
  simp only [simplexAttachmentDefect, ContinuousMap.comp_apply]
  rw [← ConcreteCategory.comp_apply, sq.inl_desc]
  rfl

@[simp] theorem simplexAttachmentDefect_old (c : C) :
    simplexAttachmentDefect X n sq (j c) = 1 := by
  simp only [simplexAttachmentDefect, ContinuousMap.comp_apply]
  rw [← ConcreteCategory.comp_apply, sq.inr_desc]
  rfl

/-- The old space together with the outer half of every attached simplex. -/
def simplexAttachmentCollar : Set D :=
  {z | (1 : ℝ) / 2 < simplexAttachmentDefect X n sq z}

theorem isOpen_simplexAttachmentCollar : IsOpen (simplexAttachmentCollar X n sq) :=
  isOpen_lt continuous_const (simplexAttachmentDefect X n sq).continuous

@[simp] theorem simplexAttachmentCollar_cell_iff
    (z : X × _root_.stdSimplex ℝ (Fin (n + 1))) :
    g z ∈ simplexAttachmentCollar X n sq ↔ z.2 ∈ simplexBoundaryCollar n := by
  change (1 : ℝ) / 2 < simplexAttachmentDefect X n sq (g z) ↔ _
  rw [simplexAttachmentDefect_cell]
  rfl

theorem range_old_subset_simplexAttachmentCollar :
    Set.range j ⊆ simplexAttachmentCollar X n sq := by
  rintro _ ⟨c, rfl⟩
  change (1 : ℝ) / 2 < simplexAttachmentDefect X n sq (j c)
  rw [simplexAttachmentDefect_old]
  norm_num

include sq in
/-- The previous space is a closed embedded subspace of the actual attachment. -/
theorem simplexAttachment_old_isClosedEmbedding : IsClosedEmbedding j :=
  isClosedEmbedding_pushout_right sq (isClosedEmbedding_parameterizedSimplexBoundary X n)

end SimplexAttachment


end TopCat

attribute [colib_tag "COL-0102",
  colib_ref "BoardmanPushouts" "Proposition 9, pages 2-3"
    "specialization"
    "Closed embedding of the old space in the actual parametrized simplex attachment"]
  TopCat.simplexAttachment_old_isClosedEmbedding

attribute [colib_tag "COL-0102",
  colib_ref "BoardmanPushouts" "Proposition 4 and Corollary 5, page 1"
    "ingredient"
    "Pushout gluing and topology for the explicit defect and open collar"]
  TopCat.simplexAttachmentDefect
  TopCat.simplexAttachmentDefect_cell
  TopCat.simplexAttachmentDefect_old
  TopCat.simplexAttachmentCollar
  TopCat.isOpen_simplexAttachmentCollar
  TopCat.range_old_subset_simplexAttachmentCollar
