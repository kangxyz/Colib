/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexAttachmentDeformation
public import Colib.Topology.Realization.SimplexAttachment.AnnulusBoundary

/-!
# Collar Retraction

The actual geometric annulus of one cell maps into its attachment collar.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory CategoryTheory.Limits TopCat Convexity.StdSimplex
universe u
namespace TopCat.SimplexAttachment
variable (A : TopCat.{u}) (n : ℕ) {O D : TopCat.{u}}
    {f : TopCat.of (A × simplexBoundary n) ⟶ O}
    {g : TopCat.of (A × Convexity.StdSimplex ℝ (Fin (n + 1))) ⟶ D} {j : O ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion A n) f g j)

/-- The actual geometric annulus of one cell maps into its attachment collar. -/
def annulusToCollar (a : A) : C(simplexAnnulus n, simplexAttachmentCollar A n sq) where
  toFun x := ⟨g (a, x.val), (simplexAttachmentCollar_cell_iff A n sq (a, x.val)).mpr
    x.property.1⟩
  continuous_toFun := by fun_prop

/-- The actual attachment collar retraction on a cell annulus is the original
attaching map applied to the actual radial boundary projection. -/
theorem collarRetraction_annulus (a : A) (x : simplexAnnulus n) :
    simplexAttachmentCollarRetraction A n sq (annulusToCollar A n sq a x) =
      f (a, annulusBoundary n x) := by
  apply (simplexAttachment_old_isClosedEmbedding A n sq).injective
  change j (simplexAttachmentCollarRetractionFun A n sq _) = _
  rw [simplexAttachmentCollarRetractionFun_spec]
  change simplexAttachmentRadial A n sq (1, g (a, x.val)) = _
  rw [simplexAttachmentRadial_cell]
  exact ConcreteCategory.congr_hom sq.w (a, annulusBoundary n x)

end TopCat.SimplexAttachment
