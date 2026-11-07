/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.PrespectrumCompositionHomotopy
public import Colib.Topology.Prespectrum.RelativeHomotopyReparam

/-!
# Contracting original transformation tracks by the weak zero endotransformation

The actual chosen-zero endotransformation absorbs an original weak endotransformation.
When its components are weak, the original composition triangle and explicit reverse-track
cancellation contract the original prespectrum self-track. Both endpoints, the entire point line,
and the independent structure coordinate are fixed. The zero endotransformation is retained
as a self-track; this does not contract the underlying prespectrum map or its target spectrum.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContraction.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
normalized self-tracks, null legs and independent parameters and universes are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
universe u
namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory Topology
variable {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- The actual endotransformation through the target category's specified zero object. -/
def zeroEndotransformation : F.hom.toFunctor ⟶ F.hom.toFunctor where
  app A := W.obj.waldhausen.isZero.from_ (F.hom.toFunctor.obj A) ≫
    W.obj.waldhausen.isZero.to_ (F.hom.toFunctor.obj A)
  naturality {A B} f := by
    have h₀ := W.obj.waldhausen.isZero.eq_of_tgt
      (F.hom.toFunctor.map f ≫ W.obj.waldhausen.isZero.from_ (F.hom.toFunctor.obj B))
      (W.obj.waldhausen.isZero.from_ (F.hom.toFunctor.obj A))
    have h₁ := W.obj.waldhausen.isZero.eq_of_src
      (W.obj.waldhausen.isZero.to_ (F.hom.toFunctor.obj A) ≫ F.hom.toFunctor.map f)
      (W.obj.waldhausen.isZero.to_ (F.hom.toFunctor.obj B))
    rw [← Category.assoc, h₀, Category.assoc, h₁]

/-- Absorption is an equality of the original transformations, before realization. -/
theorem zeroEndotransformation_absorb (η : F.hom.toFunctor ⟶ F.hom.toFunctor) :
    η ≫ zeroEndotransformation F = zeroEndotransformation F := by
  ext A
  change η.app A ≫ (W.obj.waldhausen.isZero.from_ (F.hom.toFunctor.obj A) ≫
    W.obj.waldhausen.isZero.to_ (F.hom.toFunctor.obj A)) = _
  rw [← Category.assoc, W.obj.waldhausen.isZero.eq_of_tgt
    (η.app A ≫ W.obj.waldhausen.isZero.from_ (F.hom.toFunctor.obj A))
    (W.obj.waldhausen.isZero.from_ (F.hom.toFunctor.obj A))]
  rfl

/-- The specified original triangle compares the weak zero track to the scalar-then-zero
track, without replacing either whole homotopy. -/
def prespectrumEndotransformationAbsorptionTriangle
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) :
    (prespectrumTransformationHomotopy (zeroEndotransformation F) hz).RelHomotopy
      ((prespectrumTransformationHomotopy η hη).trans
        (prespectrumTransformationHomotopy (zeroEndotransformation F) hz)) := by
  have J := prespectrumTransformationCompositionHomotopy η
    (zeroEndotransformation F) hη hz
  simpa only [zeroEndotransformation_absorb F η] using J

/-- A genuine weak zero endotransformation contracts the original whole prespectrum self-track.
Only the supplied weakness of its actual components is used. -/
def prespectrumEndotransformationContraction
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) :
    (prespectrumTransformationHomotopy η hη).RelHomotopy
      (LoopPrespectrum.Homotopy.refl (prespectrumMap F)) := by
  let H := prespectrumTransformationHomotopy η hη
  let Z := prespectrumTransformationHomotopy (zeroEndotransformation F) hz
  let J := prespectrumEndotransformationAbsorptionTriangle F η hη hz
  exact (LoopPrespectrum.Homotopy.RelHomotopy.transRefl H).symm.trans
    (((LoopPrespectrum.Homotopy.RelHomotopy.refl H).hcomp
      (LoopPrespectrum.Homotopy.RelHomotopy.reflTransSymm Z)).trans
      ((LoopPrespectrum.Homotopy.RelHomotopy.transAssoc H Z Z.symm).symm.trans
        ((J.symm.hcomp (LoopPrespectrum.Homotopy.RelHomotopy.refl Z.symm)).trans
          (LoopPrespectrum.Homotopy.RelHomotopy.reflTransSymm Z).symm)))

end CategoryTheory.Waldhausen.IteratedS
