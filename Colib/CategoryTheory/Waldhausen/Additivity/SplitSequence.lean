/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Functor.PointwiseCoproduct
public import Colib.CategoryTheory.Waldhausen.Additivity.CofibrationSequence
public import Colib.CategoryTheory.Waldhausen.Additivity.CoproductAlgebra
public import Colib.CategoryTheory.Limits.PointwisePushoutInterchange

/-! # The actual split cofibration sequence of exact functors

The split sequence has middle functor `H ⨿ F`, subobject inclusion from `F`,
and quotient `H`. Its relative cofibration condition is proved using an
actual pushout identification and cobase change, rather than assumed.


Implementation provenance: `Quillen/Waldhausen/Additivity/SplitSequence.lean`
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
variable [HasBinaryCoproducts D]

/-- The canonical transformation from the chosen constant zero functor. -/
def zeroToFunctor (F : C ⥤ D) : (Functor.const C).obj W.zero ⟶ F where
  app X := W.isZero.to_ (F.obj X)
  naturality _ _ _ := W.isZero.eq_of_src _ _

/-- Projection onto the quotient summand, through the chosen zero on `F`. -/
def sumProjection (H F : C ⥤ D) : sumFunctor H F ⟶ H where
  app X := coprod.desc (𝟙 (H.obj X)) (zeroMorphism W (F.obj X) (H.obj X))
  naturality _ _ f := by
    apply coprod.hom_ext <;> simp [sumFunctor]

variable {F H : C ⥤ D}

/-- The pointwise coproduct of exact functors is genuinely exact. -/
theorem sumFunctor_isExact
    (hH : IsExact V.cof V.weq W.cof W.weq H)
    (hF : IsExact V.cof V.weq W.cof W.weq F) :
    IsExact V.cof V.weq W.cof W.weq (sumFunctor H F) where
  zero hz := coprod_isZero W (hH.zero hz) (hF.zero hz)
  cofibration f hf := coprod_map_cof W _ _ (hH.cofibration f hf) (hF.cofibration f hf)
  weak f hf := coprod_map_weak W _ _ (hH.weak f hf) (hF.weak f hf)
  pushout {A B D P} {i f g j} hi hp :=
    isPushout_of_pointwise_pushouts (zeroToFunctor W H) (zeroToFunctor W F)
      (sumInl H F) (sumInr H F) (fun X ↦ coprod_isPushout W (H.obj X) (F.obj X))
      i f g j hp.w (by
        change IsPushout (𝟙 W.zero) (𝟙 W.zero) (𝟙 W.zero) (𝟙 W.zero)
        exact IsPushout.of_horiz_isIso ⟨by simp⟩)
      (hH.pushout hi hp) (hF.pushout hi hp)

/-- The split projection is the actual cofiber of the second summand. -/
theorem coprod_inr_cofiber (X Y : D) :
    IsPushout (coprod.inr : Y ⟶ X ⨿ Y) (W.isZero.from_ Y)
      (coprod.desc (𝟙 X) (zeroMorphism W Y X)) (W.isZero.to_ X) := by
  let p := coprod.desc (𝟙 X) (zeroMorphism W Y X)
  have wp : (coprod.inr : Y ⟶ X ⨿ Y) ≫ p = W.isZero.from_ Y ≫ W.isZero.to_ X := by
    simp [p, zeroMorphism]
  apply IsPushout.of_isColimit (c := PushoutCocone.mk p (W.isZero.to_ X) wp)
  refine PushoutCocone.IsColimit.mk wp (fun s ↦ coprod.inl ≫ s.inl) ?_ ?_ ?_
  · intro s
    apply coprod.hom_ext
    · simp [p]
    · rw [← Category.assoc, wp, Category.assoc]
      rw [W.isZero.eq_of_src (W.isZero.to_ X ≫ coprod.inl ≫ s.inl) s.inr]
      exact s.condition.symm
  · intro s
    exact W.isZero.eq_of_src _ _
  · intro s m hm _
    have hm' := congrArg (fun z ↦ (coprod.inl : X ⟶ X ⨿ Y) ≫ z) hm
    simpa [p, ← Category.assoc] using hm'

/-- The relative pushout for the split inclusion is the mixed coproduct. -/
def splitRelativeIso (f : Arrow C) :
    (pushoutFunctor W (sumInr H F) (fun X ↦ coprod_inr_cof W (H.obj X) (F.obj X))).obj f ≅
      H.obj f.left ⨿ F.obj f.right := by
  letI : HasPushout (coprod.inr : F.obj f.left ⟶ H.obj f.left ⨿ F.obj f.left)
      (F.map f.hom) := (coprod_map_right_isPushout W (H.obj f.left) (F.map f.hom)).flip.hasPushout
  exact (coprod_map_right_isPushout W (H.obj f.left) (F.map f.hom)).flip.isoPushout.symm

/-- The actual relative comparison is the first-summand map under that iso. -/
theorem splitRelative_comparison (f : Arrow C) :
    comparison W (sumInr H F) (fun X ↦ coprod_inr_cof W (H.obj X) (F.obj X)) f =
      (splitRelativeIso W f).hom ≫ coprod.map (H.map f.hom) (𝟙 (F.obj f.right)) := by
  let ha := fun X ↦ coprod_inr_cof W (H.obj X) (F.obj X)
  have hs := (coprod_map_right_isPushout W (H.obj f.left) (F.map f.hom)).flip
  let : HasPushout (coprod.inr : F.obj f.left ⟶ H.obj f.left ⨿ F.obj f.left) (F.map f.hom) :=
    hs.hasPushout
  apply (pushoutFunctor_isPushout W (sumInr H F) ha f).hom_ext
  · rw [sourceι_comparison]
    change coprod.map (H.map f.hom) (F.map f.hom) =
      pushout.inl _ _ ≫ hs.isoPushout.inv ≫ coprod.map (H.map f.hom) (𝟙 _)
    rw [hs.inl_isoPushout_inv_assoc]
    apply coprod.hom_ext <;> simp
  · rw [targetι_comparison]
    change coprod.inr = pushout.inr _ _ ≫ hs.isoPushout.inv ≫ coprod.map (H.map f.hom) (𝟙 _)
    rw [hs.inr_isoPushout_inv_assoc]
    simp

/-- The split inclusion satisfies the genuine relative-cofibration condition. -/
theorem splitIsCofibrationTransformation
    (hH : IsExact V.cof V.weq W.cof W.weq H) :
    IsCofibrationTransformation W (sumInr H F) V where
  app_cof X := coprod_inr_cof W (H.obj X) (F.obj X)
  relative_cof f hf := by
    rw [splitRelative_comparison]
    exact W.cof.comp_mem _ _ (W.cof_iso _ (by infer_instance))
      (coprod_map_cof W _ _ (hH.cofibration f hf) (W.cof.id_mem _))

/-- Every pair of exact functors has the actual split cofibration sequence. -/
theorem splitIsCofibrationSequence
    (hH : IsExact V.cof V.weq W.cof W.weq H)
    (hF : IsExact V.cof V.weq W.cof W.weq F) :
    IsCofibrationSequence V W (sumInr H F) (sumProjection W H F) where
  exactF := hF
  exactG := sumFunctor_isExact V W hH hF
  exactH := hH
  cofibration := splitIsCofibrationTransformation V W hH
  cofiber X := coprod_inr_cofiber W (H.obj X) (F.obj X)

end CategoryTheory.Waldhausen.Additivity
