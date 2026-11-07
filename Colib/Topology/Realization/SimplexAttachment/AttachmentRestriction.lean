/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexAttachment.AttachmentDecoder

/-!
# Attachment Restriction

The constructed decoder restricts along the ORIGINAL old-space map to the
input functor, naturally on every actual old-space path.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory CategoryTheory.Limits Convexity.StdSimplex TopCat
open FundamentalGroupoid.OpenCover
universe u v w
namespace TopCat.SimplexAttachment
open FundamentalGroupoid.OpenCover
variable (A : TopCat.{u}) [DiscreteTopology A] (n : ℕ) {O D : TopCat.{u}}
    {f : TopCat.of (A × Convexity.StdSimplex.boundary (n + 3)) ⟶ O}
    {g : TopCat.of (A × Convexity.StdSimplex ℝ (Fin (n + 4))) ⟶ D} {j : O ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion A (n + 3)) f g j)
    {C : Type v} [Groupoid.{w} C] (F : FundamentalGroupoid O ⥤ C)

/-- The constructed decoder restricts along the ORIGINAL old-space map to the
input functor, naturally on every actual old-space path. -/
def attachmentRestrictionIso : FundamentalGroupoid.map j.hom ⋙ attachmentDecoder A n sq F ≅ F := by
  let inc := simplexAttachmentCollarInclusion A (n + 3) sq
  let r := simplexAttachmentCollarRetraction A (n + 3) sq
  let U := starSet (simplexAttachmentCollar A (n + 3) sq)
    (simplexAttachmentInterior A (n + 3) (g := g))
  have hi : ((ContinuousMap.subtypeVal (U none))).comp inc = j.hom := rfl
  have hr : r.comp inc = ContinuousMap.id O := by
    apply ContinuousMap.ext
    exact simplexAttachmentCollarRetraction_inclusion _ _ sq
  have e := Functor.isoWhiskerLeft (FundamentalGroupoid.map inc)
    ((attachmentTransitionData A n sq F).descentChartIso (attachmentCover A n sq) none)
  have hs : FundamentalGroupoid.map inc ⋙
      (FundamentalGroupoid.map ((ContinuousMap.subtypeVal (U none))) ⋙ attachmentDecoder A n sq F) =
      FundamentalGroupoid.map j.hom ⋙ attachmentDecoder A n sq F := by
    rw [← Functor.assoc, ← FundamentalGroupoid.map_comp, hi]
  have ht : FundamentalGroupoid.map inc ⋙ collarFunctor A n sq F = F := by
    change FundamentalGroupoid.map inc ⋙ (FundamentalGroupoid.map r ⋙ F) = F
    rw [← Functor.assoc, ← FundamentalGroupoid.map_comp, hr, FundamentalGroupoid.map_id]
    rfl
  change FundamentalGroupoid.map inc ⋙
      (FundamentalGroupoid.map ((ContinuousMap.subtypeVal (U none))) ⋙ attachmentDecoder A n sq F) ≅
      FundamentalGroupoid.map inc ⋙ collarFunctor A n sq F at e
  rw [hs, ht] at e
  exact e

/-- Exact preservation of every old-space path, with the constructed endpoint transports. -/
theorem attachmentDecoder_old_path {x y : O} (p : Path x y) :
    (attachmentDecoder A n sq F).map
        (Path.Homotopic.Quotient.mk (p.map j.hom.continuous)) =
      (attachmentRestrictionIso A n sq F).hom.app (FundamentalGroupoid.mk x) ≫
        F.map (Path.Homotopic.Quotient.mk p) ≫
        (attachmentRestrictionIso A n sq F).inv.app (FundamentalGroupoid.mk y) := by
  have h := (attachmentRestrictionIso A n sq F).hom.naturality (Path.Homotopic.Quotient.mk p)
  change (attachmentDecoder A n sq F).map
      (Path.Homotopic.Quotient.mk (p.map j.hom.continuous)) ≫
      (attachmentRestrictionIso A n sq F).hom.app (FundamentalGroupoid.mk y) =
    (attachmentRestrictionIso A n sq F).hom.app (FundamentalGroupoid.mk x) ≫
      F.map (Path.Homotopic.Quotient.mk p) at h
  rw [← Category.assoc]
  exact (Iso.eq_comp_inv ((attachmentRestrictionIso A n sq F).app
    (FundamentalGroupoid.mk y))).mpr h

end TopCat.SimplexAttachment
