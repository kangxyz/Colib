/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Functor.PointwiseCoproduct
public import Colib.CategoryTheory.Waldhausen.Additivity.CofiberEndpoint
public import Colib.CategoryTheory.Waldhausen.Additivity.PushoutCofibrations

/-! # Genuine cofibration sequences of exact functors

The hypotheses are pointwise cofiber squares and the standard relative
cofibration condition. They contain no K-theory or realization assertion.
The zero-arrow endpoint of the deformation is identified naturally with
the coproduct of the quotient and subobject functors.


Implementation provenance: `Quillen/Waldhausen/Additivity/CofibrationSequence.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v u' v'

namespace CategoryTheory.Waldhausen.Additivity

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (V : Structure C) (W : Structure D)

/-- The canonical zero map through the chosen zero object. -/
def zeroMorphism (X Y : C) : X ⟶ Y := V.isZero.from_ X ≫ V.isZero.to_ Y

@[simp, reassoc]
theorem comp_zeroMorphism {X Y Z : C} (f : X ⟶ Y) :
    f ≫ zeroMorphism V Y Z = zeroMorphism V X Z := by
  dsimp [zeroMorphism]
  rw [← Category.assoc, V.isZero.eq_of_tgt (f ≫ V.isZero.from_ Y) (V.isZero.from_ X)]

@[simp, reassoc]
theorem zeroMorphism_comp {X Y Z : C} (f : Y ⟶ Z) :
    zeroMorphism V X Y ≫ f = zeroMorphism V X Z := by
  dsimp [zeroMorphism]
  rw [Category.assoc, V.isZero.eq_of_src (V.isZero.to_ Y ≫ f) (V.isZero.to_ Z)]

/-- The functor assigning the actual zero arrow to each pair of objects. -/
def zeroArrow : C × C ⥤ Arrow C where
  obj X := Arrow.mk (zeroMorphism V X.1 X.2)
  map {X Y} f := Arrow.homMk f.1 f.2 (by simp)
  map_id _ := by apply Arrow.hom_ext <;> rfl
  map_comp _ _ := by apply Arrow.hom_ext <;> rfl

variable {F G H : C ⥤ D}

/-- Exactness preserves the canonical zero maps without demanding strict
preservation of the chosen zero object. -/
theorem map_zeroMorphism (hF : IsExact V.cof V.weq W.cof W.weq F) (X Y : C) :
    F.map (zeroMorphism V X Y) = zeroMorphism W (F.obj X) (F.obj Y) := by
  dsimp [zeroMorphism]
  rw [F.map_comp]
  have hz := hF.zero V.isZero
  rw [hz.eq_of_src (F.map (V.isZero.to_ Y))
    (W.isZero.from_ (F.obj V.zero) ≫ W.isZero.to_ (F.obj Y)),
    ← Category.assoc,
    W.isZero.eq_of_tgt (F.map (V.isZero.from_ X) ≫ W.isZero.from_ (F.obj V.zero))
      (W.isZero.from_ (F.obj X))]

/-- A cofibration sequence of exact functors, expressed entirely by
structural exactness and actual categorical cofiber squares. -/
structure IsCofibrationSequence (a : F ⟶ G) (b : G ⟶ H) : Prop where
  exactF : IsExact V.cof V.weq W.cof W.weq F
  exactG : IsExact V.cof V.weq W.cof W.weq G
  exactH : IsExact V.cof V.weq W.cof W.weq H
  cofibration : IsCofibrationTransformation W a V
  cofiber (X : C) : IsPushout (a.app X) (W.isZero.from_ (F.obj X))
    (b.app X) (W.isZero.to_ (H.obj X))

variable [HasBinaryCoproducts D]

variable (a : F ⟶ G) (b : G ⟶ H) (h : IsCofibrationSequence V W a b)

/-- The zero-arrow endpoint is naturally the actual split functor. -/
def cofiberEndpointNatIso :
    zeroArrow V ⋙ pushoutFunctor W a h.cofibration.app_cof ≅ splitEndpoint H F :=
  NatIso.ofComponents (fun X ↦ cofiberEndpointIso W a h.cofibration.app_cof
    ((zeroArrow V).obj X) (b.app X.1) (h.cofiber X.1)
    (map_zeroMorphism V W h.exactF X.1 X.2)) (by
      intro X Y f
      apply (pushoutFunctor_isPushout W a h.cofibration.app_cof
        ((zeroArrow V).obj X)).hom_ext
      · simp only [Functor.comp_map, sourceι_naturality_assoc, sourceι_cofiberEndpointIso,
          sourceι_cofiberEndpointIso_assoc]
        change G.map f.1 ≫ b.app Y.1 ≫ coprod.inl =
          b.app X.1 ≫ coprod.inl ≫ coprod.map (H.map f.1) (F.map f.2)
        rw [coprod.inl_map, ← Category.assoc, b.naturality, Category.assoc]
      · simp only [Functor.comp_map, targetι_naturality_assoc, targetι_cofiberEndpointIso,
          targetι_cofiberEndpointIso_assoc]
        change F.map f.2 ≫ coprod.inr = coprod.inr ≫ coprod.map (H.map f.1) (F.map f.2)
        rw [coprod.inr_map])

end CategoryTheory.Waldhausen.Additivity
