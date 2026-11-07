/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexAttachment.AnnulusHomeomorph
public import Colib.Topology.Realization.SimplexAttachment.CollarRetraction
public import Colib.Topology.Homotopy.OpenCover.CollarOverlap
public import Mathlib.CategoryTheory.Whiskering

/-!
# Overlap Functor

Transfer a specified annulus natural isomorphism to the ACTUAL collar/cell
overlap using its original characteristic-map homeomorphism. Naturality is for
every actual overlap path and not just a selected family of generators.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory CategoryTheory.Limits TopCat Convexity.StdSimplex
universe u v w
namespace TopCat.SimplexAttachment
open FundamentalGroupoid.OpenCover
variable (A : TopCat.{u}) [DiscreteTopology A] (n : ℕ) {O D : TopCat.{u}}
    {f : TopCat.of (A × Convexity.StdSimplex.boundary n) ⟶ O}
    {g : TopCat.of (A × Convexity.StdSimplex ℝ (Fin (n + 1))) ⟶ D} {j : O ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion A n) f g j)
    {C : Type v} [Category.{w} C]

/-- Transfer a specified annulus natural isomorphism to the ACTUAL collar/cell
overlap using its original characteristic-map homeomorphism. Naturality is for
every actual overlap path and not just a selected family of generators. -/
def actualOverlapIsoOfAnnulus (a : A)
    (F : FundamentalGroupoid (simplexAttachmentCollar A n sq) ⥤ C) (b : C)
    (η : FundamentalGroupoid.map (annulusToCollar A n sq a) ⋙ F ≅
      (Functor.const (FundamentalGroupoid (simplexAnnulus n))).obj b) :
    FundamentalGroupoid.map ((ContinuousMap.inclusion (s := (simplexAttachmentCollar A n sq) ∩
        (simplexAttachmentInterior A n (g := g) a)) Set.inter_subset_left)) ⋙ F ≅
      (Functor.const (FundamentalGroupoid
        ↥(simplexAttachmentCollar A n sq ∩ simplexAttachmentInterior A n (g := g) a))).obj b := by
  let H := annulusOverlapHomeomorph A n sq a
  let hInv : C(↥(simplexAttachmentCollar A n sq ∩
      simplexAttachmentInterior A n (g := g) a), simplexAnnulus n) :=
    ⟨H.symm, H.symm.continuous⟩
  let k := annulusToCollar A n sq a
  have hk : k.comp hInv = (ContinuousMap.inclusion (s := (simplexAttachmentCollar A n sq) ∩
      (simplexAttachmentInterior A n (g := g) a)) Set.inter_subset_left) := by
    ext x
    exact congrArg (fun y : ↥(simplexAttachmentCollar A n sq ∩
      simplexAttachmentInterior A n (g := g) a) => y.val) (H.apply_symm_apply x)
  have hf : FundamentalGroupoid.map hInv ⋙ (FundamentalGroupoid.map k ⋙ F) =
      FundamentalGroupoid.map ((ContinuousMap.inclusion (s := (simplexAttachmentCollar A n sq) ∩
          (simplexAttachmentInterior A n (g := g) a)) Set.inter_subset_left)) ⋙ F := by
    rw [← Functor.assoc, ← FundamentalGroupoid.map_comp, hk]
  have e := Functor.isoWhiskerLeft (FundamentalGroupoid.map hInv) η
  rw [hf] at e
  exact e

end TopCat.SimplexAttachment
