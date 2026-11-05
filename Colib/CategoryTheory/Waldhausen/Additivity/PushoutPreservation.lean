/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Limits.PointwisePushoutInterchange
public import Colib.CategoryTheory.Waldhausen.Additivity.PushoutCofibrations
public import Colib.CategoryTheory.Waldhausen.SConstruction

/-! # Exactness properties of the actual additivity deformation

The pushout functor preserves displayed pointwise pushouts and zero objects.
Together with cofibration and gluing results, this transports actual
S-construction diagrams, without positing an additivity equivalence.


Implementation provenance: `Quillen/Waldhausen/Additivity/PushoutPreservation.lean`
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
variable (W : Structure D) {F G : C ⥤ D} (a : F ⟶ G)
variable (ha : ∀ X, W.cof (a.app X))

/-- The source inclusions form an actual natural transformation. -/
def sourceιNatTrans : Arrow.leftFunc ⋙ G ⟶ pushoutFunctor W a ha where
  app := sourceι W a ha
  naturality _ _ φ := (sourceι_naturality W a ha φ).symm

/-- The target inclusions form an actual natural transformation. -/
def targetιNatTrans : Arrow.rightFunc ⋙ F ⟶ pushoutFunctor W a ha where
  app := targetι W a ha
  naturality _ _ φ := (targetι_naturality W a ha φ).symm

/-- The finite interchange theorem applied to the actual defining span. -/
theorem pushoutFunctor_map_isPushout {A B R Q : Arrow C}
    (f : A ⟶ B) (g : A ⟶ R) (h : B ⟶ Q) (k : R ⟶ Q)
    (w : f ≫ h = g ≫ k)
    (h₀ : IsPushout (F.map f.left) (F.map g.left) (F.map h.left) (F.map k.left))
    (h₁ : IsPushout (G.map f.left) (G.map g.left) (G.map h.left) (G.map k.left))
    (h₂ : IsPushout (F.map f.right) (F.map g.right) (F.map h.right) (F.map k.right)) :
    IsPushout ((pushoutFunctor W a ha).map f) ((pushoutFunctor W a ha).map g)
      ((pushoutFunctor W a ha).map h) ((pushoutFunctor W a ha).map k) :=
  isPushout_of_pointwise_pushouts (Functor.whiskerLeft Arrow.leftFunc a)
    (Functor.whiskerRight Arrow.leftToRight F) (sourceιNatTrans W a ha) (targetιNatTrans W a ha)
    (pushoutFunctor_isPushout W a ha) f g h k w h₀ h₁ h₂

variable (V : Structure C)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)

include hF hG in
/-- A displayed pointwise pushout along pointwise cofibrations is preserved. -/
theorem pushoutFunctor_map_isPushout_of_exact {A B R Q : Arrow C}
    (f : A ⟶ B) (g : A ⟶ R) (h : B ⟶ Q) (k : R ⟶ Q)
    (w : f ≫ h = g ≫ k) (hl : V.cof f.left) (hr : V.cof f.right)
    (hleft : IsPushout f.left g.left h.left k.left)
    (hright : IsPushout f.right g.right h.right k.right) :
    IsPushout ((pushoutFunctor W a ha).map f) ((pushoutFunctor W a ha).map g)
      ((pushoutFunctor W a ha).map h) ((pushoutFunctor W a ha).map k) :=
  pushoutFunctor_map_isPushout W a ha f g h k w
    (hF.pushout hl hleft) (hG.pushout hl hleft) (hF.pushout hr hright)

include hF hG in
/-- An arrow whose endpoints are zero is carried to an actual zero object. -/
theorem pushoutFunctor_obj_isZero (f : Arrow C) (hl : IsZero f.left) (hr : IsZero f.right) :
    IsZero ((pushoutFunctor W a ha).obj f) := by
  let : IsIso (F.map f.hom) := (hF.zero hl).isIso (hF.zero hr) _
  let : IsIso (sourceι W a ha f) := (pushoutFunctor_isPushout W a ha f).isIso_inl_of_isIso
  exact (hG.zero hl).of_iso (asIso (sourceι W a ha f)).symm

variable (hc : IsCofibrationTransformation W a V)

include hF hG in
/-- The actual additivity pushout construction carries every pointwise
S-construction arrow diagram to an S-construction diagram. -/
theorem pushoutFunctor_isSimplex {n : SimplexCategory} (A : Grid n ⥤ Arrow C)
    (hl : IsSimplex V.cof V.weq (A ⋙ Arrow.leftFunc))
    (hr : IsSimplex V.cof V.weq (A ⋙ Arrow.rightFunc)) :
    IsSimplex W.cof W.weq (A ⋙ pushoutFunctor W a hc.app_cof) where
  zero t i := pushoutFunctor_obj_isZero W a hc.app_cof V hF hG _ (hl.zero t i) (hr.zero t i)
  cofibration t i j k hij hjk := pushoutFunctor_map_cof W a V hF hc _
    (hl.cofibration t i j k hij hjk) (hr.cofibration t i j k hij hjk)
  quotient t i j k hij hjk := pushoutFunctor_map_isPushout_of_exact W a hc.app_cof V hF hG
    _ _ _ _ (by simp only [← A.map_comp]; congr 1)
    (hl.cofibration t i j k hij hjk) (hr.cofibration t i j k hij hjk)
    (hl.quotient t i j k hij hjk) (hr.quotient t i j k hij hjk)
  weak s t i j hst hij := pushoutFunctor_map_weak_of_exact W a V hF hG hc _
    (hl.weak s t i j hst hij) (hr.weak s t i j hst hij)

end CategoryTheory.Waldhausen.Additivity
