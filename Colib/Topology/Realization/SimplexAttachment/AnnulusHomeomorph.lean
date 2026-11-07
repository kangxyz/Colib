/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexAttachmentCover
public import Colib.Topology.Realization.SimplexAnnulus

/-!
# Annulus Homeomorph

The geometric annulus is homeomorphic to the actual collar/interior overlap,
using the given characteristic map, not just an abstract homotopy equivalence.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory CategoryTheory.Limits TopCat Convexity.StdSimplex
universe u
namespace TopCat.SimplexAttachment
variable (A : TopCat.{u}) [DiscreteTopology A] (n : ℕ) {O D : TopCat.{u}}
    {f : TopCat.of (A × Convexity.StdSimplex.boundary n) ⟶ O}
    {g : TopCat.of (A × Convexity.StdSimplex ℝ (Fin (n + 1))) ⟶ D} {j : O ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion A n) f g j)

/-- The geometric annulus is homeomorphic to the actual collar/interior overlap,
using the given characteristic map, not just an abstract homotopy equivalence. -/
def annulusOverlapHomeomorph (a : A) : simplexAnnulus n ≃ₜ
    ↥(simplexAttachmentCollar A n sq ∩ simplexAttachmentInterior A n (g := g) a) := by
  let S : Set (simplexInterior n) := {x | x.val ∈ simplexBoundaryCollar n}
  let e : simplexAnnulus n ≃ₜ S := {
    toFun := fun x => ⟨⟨x.val, x.property.2⟩, x.property.1⟩
    invFun := fun x => ⟨x.val.val, x.property, x.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  have him : (simplexAttachmentInteriorMap A n (g := g) a) '' S =
      simplexAttachmentCollar A n sq ∩ simplexAttachmentInterior A n (g := g) a := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(simplexAttachmentCollar_cell_iff A n sq (a, x.val)).mpr hx, ⟨x, rfl⟩⟩
    · rintro ⟨hc, x, hx⟩
      refine ⟨x, ?_, hx⟩
      exact (simplexAttachmentCollar_cell_iff A n sq (a, x.val)).mp (hx.symm ▸ hc)
  exact e.trans (((isOpenEmbedding_simplexAttachmentInteriorMap A n sq a).isEmbedding
    |>.homeomorphImage S).trans (Homeomorph.setCongr him))

/-- The forward homeomorphism is the actual original characteristic map. -/
theorem annulusOverlapHomeomorph_apply (a : A) (x : simplexAnnulus n) :
    (annulusOverlapHomeomorph A n sq a x).val = g (a, x.val) := rfl

end TopCat.SimplexAttachment
