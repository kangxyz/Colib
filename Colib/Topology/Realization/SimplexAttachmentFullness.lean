/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.SimplexAttachmentCover
public import Colib.Topology.Homotopy.OpenCoverFull
public import Colib.Topology.Realization.SimplexAttachmentDeformation
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# Simplex attachments in dimension at least two add no path generators

For a discrete family of geometric simplices attached along their actual
boundaries, the inclusion of the previous space is full on fundamental
groupoids in dimensions at least two. This is proved from genuine open collar
and interior charts, compact path subdivision, and local path homotopies.
-/
/-!
Adapted from `Quillen/Topology/Realization/EdgePathPresentation/Attachment.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Actual cell maps, endpoint tracks and relative homotopy classes are retained.
The source path, endpoint and dimension hypotheses are retained.
-/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Limits Convexity Convexity.StdSimplex Topology Set
open scoped Topology unitInterval

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TopCat

section SimplexAttachment

variable (X : TopCat.{u}) [DiscreteTopology X] (n : ℕ) {C D : TopCat.{u}}
    {f : TopCat.of (X × simplexBoundary n) ⟶ C}
    {g : TopCat.of (X × StdSimplex ℝ (Fin (n + 1))) ⟶ D}
    {j : C ⟶ D}
    (sq : IsPushout (TopCat.parameterizedSimplexBoundaryInclusion X n) f g j)

include sq in
/-- Attaching any discrete family of `n`-simplices for `n ≥ 2` creates no new
fundamental-groupoid morphism generators between points of the old space. -/
theorem simplexAttachment_fundamentalGroupoid_full (hn : 2 ≤ n) :
    (FundamentalGroupoid.map j.hom).Full := by
  let U := simplexAttachmentCollar X n sq
  let ι : C(U, D) := ⟨Subtype.val, continuous_subtype_val⟩
  let e := simplexAttachmentCollarHomotopyEquiv X n sq
  have hU : (FundamentalGroupoid.map ι).Full :=
    FundamentalGroupoid.openInclusion_full U (simplexAttachmentInterior X n (g := g))
      (isOpen_simplexAttachmentCollar X n sq)
      (isOpen_simplexAttachmentInterior X n sq)
      (by rw [simplexAttachmentCollar_union_interiors X n sq])
      (pairwiseDisjoint_simplexAttachmentInteriors X n sq)
      (isSimplyConnected_simplexAttachmentInterior X n sq)
      (isPathConnected_simplexAttachmentCollar_inter_interior X n sq hn)
  let := hU
  have he : (FundamentalGroupoid.map e.toFun).IsEquivalence :=
    (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).isEquivalence_functor
  let := he
  have hcomp : FundamentalGroupoid.map j.hom =
      FundamentalGroupoid.map e.toFun ⋙ FundamentalGroupoid.map ι := by
    rw [← FundamentalGroupoid.map_comp]
    congr 1
  rw [hcomp]
  infer_instance

include sq in
/-- Every actual path in the attachment between old-space points is homotopic,
relative to its endpoints, to a path coming from the old space. -/
theorem simplexAttachment_path_homotopic_from_old (hn : 2 ≤ n)
    {c d : C} (p : Path (j c) (j d)) :
    ∃ q : Path c d, (q.map j.hom.continuous).Homotopic p := by
  let := simplexAttachment_fundamentalGroupoid_full X n sq hn
  let F := FundamentalGroupoid.map j.hom
  obtain ⟨q, hq⟩ := F.map_surjective
    (X := FundamentalGroupoid.mk c) (Y := FundamentalGroupoid.mk d) ⟦p⟧
  obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
  refine ⟨q, ?_⟩
  change Path.Homotopic.Quotient.mk (q.map j.hom.continuous) =
    Path.Homotopic.Quotient.mk p at hq
  exact Path.Homotopic.Quotient.eq.mp hq

end SimplexAttachment

end TopCat

attribute [colib_tag "COL-0106",
  colib_ref "HatcherAT" "Section 1.1, Exercise 18, page 39"
    "background"
    "Higher-dimensional attachment fullness between old points, not faithfulness"]
  TopCat.simplexAttachment_fundamentalGroupoid_full
  TopCat.simplexAttachment_path_homotopic_from_old

attribute [colib_ref "HatcherAT" "Section 1.2, Proposition 1.26(a),(b), pages 50-51"
  "background" "Only absence of new path generators; no kernel formula or isomorphism is asserted"]
  TopCat.simplexAttachment_fundamentalGroupoid_full
