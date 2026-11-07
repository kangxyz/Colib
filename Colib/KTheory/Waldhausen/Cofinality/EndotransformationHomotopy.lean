/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Cofinality.Grading
public import Colib.KTheory.Waldhausen.Iterated.EndotransformationContraction
public import Colib.Topology.Prespectrum.HomotopyLoop
public import Colib.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# Actual endotransformation tracks in a grading-coarse model

Every zero endomorphism is weak for the original endpoint-grade weak class. The actual
zero endotransformation therefore absorbs any original endotransformation. Its genuine
composition triangle and explicit reverse-track cancellation contract the unchanged
canonically normalized prespectrum self-track, relative to both endpoints and the point.
The zero endotransformation is a self-track, not a nullhomotopy of the underlying map.
No concentration or choice of pointwise contractions is used.
-/
/-! Implementation provenance: `Quillen/Waldhausen/Cofinality/EndotransformationHomotopy.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
normalized self-tracks, null legs and independent parameters and universes are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u v w
namespace CategoryTheory.Waldhausen.Cofinality.Grading

open Topology
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) {V : Structure D} {G : Type w} [AddCommGroup G]
  (d : Grading V G) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq d.coarseStructure.cof d.coarseStructure.weq F)

/-- The original normalized track of any endotransformation is contracted through the
same weak zero endotransformation and its original composition triangle. -/
def exactEndotransformationContraction (η : F ⟶ F) :
    (exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
      (fun _ ↦ rfl)).RelHomotopy
      (LoopPrespectrum.Homotopy.refl (exactOriginalPrespectrumMap W d.coarseStructure hF)) := by
  unfold exactOriginalPrespectrumHomotopy originalPrespectrumTransformationHomotopy
  exact prespectrumEndotransformationContraction _ _ _ (fun _ ↦ rfl)

/-- The prescribed null-conjugate is globally null when its original self-track comes
from an endotransformation in the actual grading-coarse target. Both original null legs
are retained before the genuine relative contractions are applied. -/
def exactEndotransformationNullLoopHomotopy (η : F ⟶ F)
    {T : LoopPrespectrum.{max u v}} (j : originalPrespectrum d.coarseStructure ⟶ T)
    (N : Homotopy (exactOriginalPrespectrumMap W d.coarseStructure hF ≫ j)
      (zeroHom (originalPrespectrum W) T)) :
    Homotopy (((exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
      (fun _ ↦ rfl)).postcomp j).nullLoopMap N)
      (zeroHom (originalPrespectrum W) (parameterLooping T)) := by
  let H := (exactOriginalPrespectrumHomotopy W d.coarseStructure hF hF η
    (fun _ ↦ rfl)).postcomp j
  have J : H.RelHomotopy (LoopPrespectrum.Homotopy.refl
      (exactOriginalPrespectrumMap W d.coarseStructure hF ≫ j)) :=
    (d.exactEndotransformationContraction W hF η).postcomp j
  have K : (H.conjugateToZero N).RelHomotopy
      (LoopPrespectrum.Homotopy.refl (zeroHom (originalPrespectrum W) T)) :=
    ((LoopPrespectrum.Homotopy.RelHomotopy.refl N.symm).hcomp
      ((J.hcomp (LoopPrespectrum.Homotopy.RelHomotopy.refl N)).trans
        (LoopPrespectrum.Homotopy.RelHomotopy.reflTrans N))).trans
      (LoopPrespectrum.Homotopy.RelHomotopy.reflSymmTrans N).symm
  exact K.zeroLoopMapHomotopy

end CategoryTheory.Waldhausen.Cofinality.Grading

attribute [colib_tag "COL-0278",
  colib_ref "ThomasonTrobaugh1990" "Section 1.5.4, pp. 260-261" "background"
    "Homotopy background; the relative zero-track contraction is proved here"]
  CategoryTheory.Waldhausen.Cofinality.Grading.exactEndotransformationContraction

attribute [colib_tag "COL-0278"]
  CategoryTheory.Waldhausen.Cofinality.Grading.exactEndotransformationNullLoopHomotopy
