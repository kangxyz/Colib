/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Closed embeddings in topological pushouts

Cobase change of a closed embedding is a closed embedding in ordinary TopCat.
The other attaching map is arbitrary; no separation or cofibration hypothesis
is required. Open complements and T1 preservation are in `PushoutInteriors`.

## Implementation provenance

Adapted from the first theorem of
`Quillen/Topology/Realization/EdgePathPresentation/Pushout.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual pushout square, maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology Set
open scoped Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TopCat

/-- Cobase change of a closed embedding in actual topological spaces is a
closed embedding. The underlying injectivity and intersection statement are
proved in the set-theoretic pushout; closedness uses the colimit topology. -/
theorem isClosedEmbedding_pushout_right
    {A B C D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (hi : IsClosedEmbedding i) : IsClosedEmbedding j := by
  let sqT := sq.map (forget TopCat)
  have hj : Function.Injective j :=
    Types.pushoutCocone_inr_injective_of_isColimit sqT.isColimit hi.injective
  refine IsClosedEmbedding.of_continuous_injective_isClosedMap j.hom.continuous hj ?_
  intro W hW
  have hleft : g ⁻¹' (j '' W) = i '' (f ⁻¹' W) := by
    ext b
    constructor
    · rintro ⟨c, hc, hcb⟩
      obtain ⟨a, hab, hac⟩ :=
        (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit sqT.isColimit
          hi.injective b c).mp hcb.symm
      change f a = c at hac
      exact ⟨a, by change f a ∈ W; rwa [hac], hab⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨f a, ha, (ConcreteCategory.congr_hom sq.w a).symm⟩
  rw [TopCat.isClosed_iff_of_isColimit sq.cocone sq.isColimit]
  rintro (_ | _ | _)
  · change IsClosed ((i ≫ g) ⁻¹' (j '' W))
    change IsClosed (i ⁻¹' (g ⁻¹' (j '' W)))
    rw [hleft]
    exact (hi.isClosedMap _ (hW.preimage f.hom.continuous)).preimage i.hom.continuous
  · change IsClosed (g ⁻¹' (j '' W))
    rw [hleft]
    exact hi.isClosedMap _ (hW.preimage f.hom.continuous)
  · change IsClosed (j ⁻¹' (j '' W))
    rw [Set.preimage_image_eq _ hj]
    exact hW

end TopCat

attribute [colib_tag "COL-0094",
  colib_ref "BoardmanPushouts" "Proposition 9, pages 2-3"
    "adaptation"
    "Cobase change of a closed embedding in ordinary topological spaces"]
  TopCat.isClosedEmbedding_pushout_right
