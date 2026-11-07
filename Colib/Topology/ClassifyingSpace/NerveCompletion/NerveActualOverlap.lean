/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexAttachment.AnnulusHomeomorph
public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveAnnulusNaturality
public import Mathlib.CategoryTheory.Whiskering

/-!
# Nerve Actual Overlap

The actual overlap, not its geometric parameter space.
-/

@[expose] public section

noncomputable section
open Set CategoryTheory stdSimplex TopCat
universe u v
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment
attribute [local instance] Localization.groupoid

/-- The actual overlap, not its geometric parameter space. -/
abbrev nerveGraphOverlap (C : Type u) [Category.{v} C] (a : NerveGraphData.Index C) :=
  nerveGraphCollar C ∩ nerveGraphInterior C a

/-- The collar chart functor restricted to the actual overlap subtype. -/
def nerveActualOverlapDecoder (C : Type u) [Category.{v} C] (a : NerveGraphData.Index C) :
    FundamentalGroupoid (nerveGraphOverlap C a) ⥤ (⊤ : MorphismProperty C).Localization :=
  FundamentalGroupoid.map ((ContinuousMap.inclusion (s := (nerveGraphCollar C) ∩
      (nerveGraphInterior C a)) Set.inter_subset_left)) ⋙
    nerveGraphCollarDecoder C

/-- The original edge transport is natural on all actual overlap paths. The
homeomorphism is induced by the actual characteristic map, so this statement
includes the required lifting of every overlap path into the geometric annulus. -/
def nerveActualOverlapTransition (C : Type u) [Category.{v} C] (a : NerveGraphData.Index C) :
    nerveActualOverlapDecoder C a ≅
      (Functor.const (FundamentalGroupoid (nerveGraphOverlap C a))).obj
        (NerveGraphData.vertex C (NerveGraphData.attaching C (a, boundaryZero))) := by
  let H := annulusOverlapHomeomorph (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a
  let hInv : C(nerveGraphOverlap C a, simplexAnnulus 1) := ⟨H.symm, H.symm.continuous⟩
  let k := annulusToCollar (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a
  have hk : k.comp hInv =
      (ContinuousMap.inclusion (s := (nerveGraphCollar C) ∩ (nerveGraphInterior C a))
          Set.inter_subset_left) := by
    ext x
    exact congrArg (fun y : nerveGraphOverlap C a => y.val) (H.apply_symm_apply x)
  have hf : FundamentalGroupoid.map hInv ⋙ nerveAnnulusDecoder C a =
      nerveActualOverlapDecoder C a := by
    change FundamentalGroupoid.map hInv ⋙
      (FundamentalGroupoid.map k ⋙ nerveGraphCollarDecoder C) = _
    rw [← Functor.assoc, ← FundamentalGroupoid.map_comp, hk]
    rfl
  have h := Functor.isoWhiskerLeft (FundamentalGroupoid.map hInv)
    (nerveAnnulusTransition C a)
  rw [hf] at h
  exact h

end CategoryTheory.NerveCompletion
