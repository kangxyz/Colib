/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexAttachment.AttachmentCharts
public import Colib.Topology.Homotopy.OpenCover.ChartRecovery
public import Colib.Topology.Homotopy.OpenCover.StarDescent

/-!
# Attachment Decoder

The genuine open collar/interior cover of the original higher attachment.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory CategoryTheory.Limits _root_.stdSimplex TopCat
open FundamentalGroupoid.OpenCover
universe u v w
namespace TopCat.SimplexAttachment
open FundamentalGroupoid.OpenCover
variable (A : TopCat.{u}) [DiscreteTopology A] (n : ℕ) {O D : TopCat.{u}}
    {f : TopCat.of (A × _root_.stdSimplex.boundary (n + 3)) ⟶ O}
    {g : TopCat.of (A × _root_.stdSimplex ℝ (Fin (n + 4))) ⟶ D} {j : O ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion A (n + 3)) f g j)
    {C : Type v} [Groupoid.{w} C] (F : FundamentalGroupoid O ⥤ C)

/-- The genuine open collar/interior cover of the original higher attachment. -/
theorem attachmentCover :
    CoverData (starSet (simplexAttachmentCollar A (n + 3) sq)
      (simplexAttachmentInterior A (n + 3) (g := g))) where
  isOpen i := by
    cases i with
    | none => exact isOpen_simplexAttachmentCollar _ _ sq
    | some a => exact isOpen_simplexAttachmentInterior _ _ sq a
  covers x := by
    have hx : x ∈ simplexAttachmentCollar A (n + 3) sq ∪
        ⋃ a, simplexAttachmentInterior A (n + 3) (g := g) a := by
      rw [simplexAttachmentCollar_union_interiors _ _ sq]
      trivial
    rcases hx with hx | hx
    · exact mem_iUnion.mpr ⟨none, hx⟩
    · obtain ⟨a, ha⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨some a, ha⟩

omit [DiscreteTopology A] in
include sq in
/-- An actual common interior point forces equality of cell indices. -/
theorem interior_eq_of_mem (a b : A) (x : D)
    (ha : x ∈ simplexAttachmentInterior A (n + 3) (g := g) a)
    (hb : x ∈ simplexAttachmentInterior A (n + 3) (g := g) b) : a = b := by
  by_contra h
  exact Set.disjoint_left.mp (pairwiseDisjoint_simplexAttachmentInteriors _ _ sq h) ha hb

/-- Full actual transition data; no overlap path compatibility is assumed. -/
def attachmentTransitionData :
    TransitionData (C := C) (starSet (simplexAttachmentCollar A (n + 3) sq)
      (simplexAttachmentInterior A (n + 3) (g := g))) :=
  starData (simplexAttachmentCollar A (n + 3) sq)
    (simplexAttachmentInterior A (n + 3) (g := g)) (interior_eq_of_mem A n sq)
    (collarFunctor A n sq F)
    (fun a => F.obj (FundamentalGroupoid.mk
      (f (a, _root_.stdSimplex.Boundary.vertex (0 : Fin (n + 4))))))
    (overlapTransition A n sq F)

/-- A constructed extension across an arbitrary genuine higher-simplex attachment.
The input is only the old-space functor and the actual geometric pushout. -/
def attachmentDecoder : FundamentalGroupoid D ⥤ C :=
  (attachmentTransitionData A n sq F).descent (attachmentCover A n sq)

end TopCat.SimplexAttachment
