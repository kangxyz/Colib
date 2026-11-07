/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.NerveBoundaryTransport

/-!
# Nerve Annulus Naturality

Equality transports commute with a chosen iso family whenever the actual
parameter agrees. Both endpoint equalities are retained in the formula.
-/

@[expose] public section

noncomputable section
open CategoryTheory stdSimplex TopCat
universe u v w z
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment

/-- Equality transports commute with a chosen iso family whenever the actual
parameter agrees. Both endpoint equalities are retained in the formula. -/
theorem eqToHom_isoFamily {B : Type u} {D : Type v} [Category.{w} D]
    (obj : B → D) (target : D) (γ : ∀ b, obj b ≅ target)
    {a b : D} {x y : B} (h : x = y) (hx : a = obj x) (hy : b = obj y) (hab : a = b) :
    eqToHom hab ≫ (eqToIso hy ≪≫ γ y).hom = (eqToIso hx ≪≫ γ x).hom := by
  subst y
  simp only [Iso.trans_hom, eqToIso.hom, ← Category.assoc, eqToHom_trans]

attribute [local instance] Localization.groupoid

/-- The actual collar decoder restricted through a specified edge annulus. -/
def nerveAnnulusDecoder (C : Type u) [Category.{v} C] (a : NerveGraphData.Index C) :
    FundamentalGroupoid (simplexAnnulus 1) ⥤ (⊤ : MorphismProperty C).Localization :=
  FundamentalGroupoid.map
    (annulusToCollar (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a) ⋙
      nerveGraphCollarDecoder C

/-- The specified original-edge transports are natural on EVERY actual annulus
path, even when the attached edge is a loop with identified endpoint objects. -/
theorem nerveAnnulusTransport_path (C : Type u) [Category.{v} C]
    (a : NerveGraphData.Index C) {x y : simplexAnnulus 1} (p : Path x y) :
    (nerveAnnulusDecoder C a).map (Path.Homotopic.Quotient.mk p) ≫
      (nerveAnnulusTransport C a y).hom = (nerveAnnulusTransport C a x).hom := by
  let r := simplexAttachmentCollarRetraction (NerveGraphData.Index C) 1
    (NerveGraphData.pushout C)
  let k := annulusToCollar (NerveGraphData.Index C) 1 (NerveGraphData.pushout C) a
  let oldPath := p.map (r.continuous.comp k.continuous)
  have hm : (nerveAnnulusDecoder C a).map (Path.Homotopic.Quotient.mk p) =
      eqToHom (congrArg (NerveGraphData.vertex C)
        (vertexEndpoints_eq (Path.Homotopic.Quotient.mk oldPath))) := rfl
  have hb : annulusBoundary 1 x = annulusBoundary 1 y := by
    simpa using (annulusBoundary_one_path_constant p 1).symm
  rw [hm]
  exact eqToHom_isoFamily (fun b => NerveGraphData.vertex C
    (NerveGraphData.attaching C (a, b))) _ (nerveBoundaryTransport C a) hb _ _ _

/-- The actual annulus transition iso to the constant interior object. -/
def nerveAnnulusTransition (C : Type u) [Category.{v} C] (a : NerveGraphData.Index C) :
    nerveAnnulusDecoder C a ≅
      (Functor.const (FundamentalGroupoid (simplexAnnulus 1))).obj
        (NerveGraphData.vertex C (NerveGraphData.attaching C (a, boundaryZero))) :=
  NatIso.ofComponents (fun x => nerveAnnulusTransport C a x.as) (by
    intro x y f
    induction f using _root_.Quotient.ind with | _ p =>
      simpa using nerveAnnulusTransport_path C a p)

end CategoryTheory.NerveCompletion
