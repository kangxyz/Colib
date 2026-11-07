/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.EdgeGeometry

/-!
# Split Transport

A parameter equality retains exactly the source object equality transport.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Convexity.StdSimplex TopCat
universe u v w
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment
/-- A parameter equality retains exactly the source object equality transport. -/
theorem isoFamily_parameter_eq {B : Type u} {D : Type v} [Category.{w} D]
    (obj : B → D) (target : D) (γ : ∀ b, obj b ≅ target)
    {x y : B} (h : x = y) {a : D} (hx : a = obj x) (hy : a = obj y) :
    eqToIso hx ≪≫ γ x = eqToIso hy ≪≫ γ y := by
  subst y
  rfl

attribute [local instance] Localization.groupoid

/-- Retraction of the actual source overlap image is the original source vertex. -/
theorem nerveSourceSplit_retraction (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    simplexAttachmentCollarRetraction (NerveGraphData.Index C) 1
      (NerveGraphData.pushout C)
      (annulusToCollar (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a sourceSplit) =
        NerveGraphData.attaching C (a, boundaryZero) := by
  rw [collarRetraction_annulus, sourceSplit_boundary]

/-- Retraction of the actual target overlap image is the original target vertex. -/
theorem nerveTargetSplit_retraction (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    simplexAttachmentCollarRetraction (NerveGraphData.Index C) 1
      (NerveGraphData.pushout C)
      (annulusToCollar (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a targetSplit) =
        NerveGraphData.attaching C (a, boundaryOne) := by
  rw [collarRetraction_annulus, targetSplit_boundary]

/-- The source split transport is exactly the retraction equality transport. -/
theorem nerveAnnulusTransport_source (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    nerveAnnulusTransport C a sourceSplit =
      eqToIso (congrArg (NerveGraphData.vertex C) (nerveSourceSplit_retraction C a)) := by
  have h := isoFamily_parameter_eq
    (fun b => NerveGraphData.vertex C (NerveGraphData.attaching C (a, b))) _
    (nerveBoundaryTransport C a) sourceSplit_boundary
    (congrArg (NerveGraphData.vertex C)
      (collarRetraction_annulus (NerveGraphData.Index C) 1
        (NerveGraphData.pushout C) a sourceSplit))
    (congrArg (NerveGraphData.vertex C) (nerveSourceSplit_retraction C a))
  simpa only [nerveAnnulusTransport, nerveBoundaryTransport_zero, Iso.trans_refl] using h

/-- The target split transport retains the inverse of the actual original edge. -/
theorem nerveAnnulusTransport_target (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    nerveAnnulusTransport C a targetSplit =
      eqToIso (congrArg (NerveGraphData.vertex C) (nerveTargetSplit_retraction C a)) ≪≫
        (asIso (NerveGraphData.edge C a)).symm := by
  have h := isoFamily_parameter_eq
    (fun b => NerveGraphData.vertex C (NerveGraphData.attaching C (a, b))) _
    (nerveBoundaryTransport C a) targetSplit_boundary
    (congrArg (NerveGraphData.vertex C)
      (collarRetraction_annulus (NerveGraphData.Index C) 1
        (NerveGraphData.pushout C) a targetSplit))
    (congrArg (NerveGraphData.vertex C) (nerveTargetSplit_retraction C a))
  simpa only [nerveAnnulusTransport, nerveBoundaryTransport_one] using h

end CategoryTheory.NerveCompletion
