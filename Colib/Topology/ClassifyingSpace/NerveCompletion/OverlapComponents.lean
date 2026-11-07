/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.EdgeGeometry
public import Colib.CategoryTheory.NaturalTransformation.Transport
public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveActualOverlap

/-!
# Overlap Components

At the actual characteristic image of a geometric annulus point, the
actual-overlap transition is exactly the specified original geometric transport.
-/

@[expose] public section

noncomputable section
open CategoryTheory Convexity.StdSimplex TopCat
universe u v w z
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment

attribute [local instance] Localization.groupoid

/-- At the actual characteristic image of a geometric annulus point, the
actual-overlap transition is exactly the specified original geometric transport. -/
theorem nerveActualOverlapTransition_image (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) (x : simplexAnnulus 1) :
    (nerveActualOverlapTransition C a).hom.app (FundamentalGroupoid.mk
      (annulusOverlapHomeomorph (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a x)) =
      (nerveAnnulusTransport C a x).hom := by
  let H := annulusOverlapHomeomorph (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a
  let hInv : C(nerveGraphOverlap C a, simplexAnnulus 1) := ⟨H.symm, H.symm.continuous⟩
  let k := annulusToCollar (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a
  have hk : k.comp hInv =
      (ContinuousMap.inclusion (s := (nerveGraphCollar C) ∩ (nerveGraphInterior C a))
          Set.inter_subset_left) := by
    ext z
    exact congrArg (fun y : nerveGraphOverlap C a => y.val) (H.apply_symm_apply z)
  have hf : FundamentalGroupoid.map hInv ⋙ nerveAnnulusDecoder C a =
      nerveActualOverlapDecoder C a := by
    change FundamentalGroupoid.map hInv ⋙
      (FundamentalGroupoid.map k ⋙ nerveGraphCollarDecoder C) = _
    rw [← Functor.assoc, ← FundamentalGroupoid.map_comp, hk]
    rfl
  let e := Functor.isoWhiskerLeft (FundamentalGroupoid.map hInv)
    (nerveAnnulusTransition C a)
  have he : nerveActualOverlapTransition C a =
      cast (congrArg (fun K => K ≅
        (Functor.const (FundamentalGroupoid (nerveGraphOverlap C a))).obj
          (NerveGraphData.vertex C (NerveGraphData.attaching C (a, boundaryZero)))) hf) e := rfl
  rw [he, natIso_transport_hom_app hf]
  change eqToHom _ ≫ (nerveAnnulusTransport C a (H.symm (H x))).hom = _
  exact isoFamily_parameter_transport
    (fun z => (nerveAnnulusDecoder C a).obj (FundamentalGroupoid.mk z)) _
    (nerveAnnulusTransport C a) (H.symm_apply_apply x).symm _

end CategoryTheory.NerveCompletion
