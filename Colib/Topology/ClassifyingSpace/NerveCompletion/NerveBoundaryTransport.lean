/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexAttachment.CollarRetraction
public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveGraphCharts

/-!
# Nerve Boundary Transport

Transport from either actual edge endpoint to the specified source object.
At the target it is the inverse of the actual original localized edge.
-/

@[expose] public section

noncomputable section
open CategoryTheory Convexity.StdSimplex
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment
attribute [local instance] Localization.groupoid

/-- Transport from either actual edge endpoint to the specified source object.
At the target it is the inverse of the actual original localized edge. -/
def nerveBoundaryTransport (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) (b : Convexity.StdSimplex.boundary 1) :
    NerveGraphData.vertex C (NerveGraphData.attaching C (a, b)) ≅
      NerveGraphData.vertex C (NerveGraphData.attaching C (a, boundaryZero)) := by
  classical
  by_cases h : b = boundaryZero
  · exact eqToIso (congrArg (fun b => NerveGraphData.vertex C
      (NerveGraphData.attaching C (a, b))) h)
  · have hb : b = boundaryOne := (boundary_eq_zero_or_one b).resolve_left h
    exact eqToIso (congrArg (fun b => NerveGraphData.vertex C
      (NerveGraphData.attaching C (a, b))) hb) ≪≫ (asIso (NerveGraphData.edge C a)).symm

@[simp]
theorem nerveBoundaryTransport_zero (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    nerveBoundaryTransport C a boundaryZero = Iso.refl _ := by
  simp [nerveBoundaryTransport]

@[simp]
theorem nerveBoundaryTransport_one (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) :
    nerveBoundaryTransport C a boundaryOne = (asIso (NerveGraphData.edge C a)).symm := by
  simp [nerveBoundaryTransport, boundaryZero_ne_one.symm]

/-- The specified geometric overlap transport, including the exact collar
retraction/attaching equality before the original edge transport. -/
def nerveAnnulusTransport (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) (x : simplexAnnulus 1) :
    (nerveGraphCollarDecoder C).obj (FundamentalGroupoid.mk
      (annulusToCollar (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a x)) ≅
    NerveGraphData.vertex C (NerveGraphData.attaching C (a, boundaryZero)) :=
  eqToIso (congrArg (NerveGraphData.vertex C)
    (collarRetraction_annulus (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a x)) ≪≫
      nerveBoundaryTransport C a (annulusBoundary 1 x)

end CategoryTheory.NerveCompletion
