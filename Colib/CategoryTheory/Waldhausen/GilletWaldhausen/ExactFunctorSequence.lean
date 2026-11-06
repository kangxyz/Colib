/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.RelativePushout
public import Colib.CategoryTheory.Limits.Shapes.CokernelPushout
public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.CategoryTheory.Waldhausen.Additivity.CofibrationSequence
public import Colib.CategoryTheory.ExactCategory.Functor.Waldhausen
public import Colib.CategoryTheory.Waldhausen.Rows.PullbackQuotients

/-!
# Actual conflation sequences of exact functors are cofibration sequences

The relative-cofibration axiom is derived from exactness of the quotient
functor. The genuine relative pushout fits in a conflation with the same
kernel as the target; its comparison is the pullback of an admissible
inclusion along an admissible epimorphism. No additivity conclusion occurs
among the hypotheses.


Implementation provenance:
`Quillen/Waldhausen/GilletWaldhausen/ExactFunctorSequence.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
universe v u v' u'

namespace CategoryTheory.Waldhausen.GilletWaldhausen

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
variable (E : ExactStructure C) (E' : ExactStructure D)
variable {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H) (w : a ≫ b = 0)
variable (hc : ∀ X, E'.conflation
  (ShortComplex.mk (a.app X) (b.app X) (NatTrans.congr_app w X)))

include hc in
/-- Quotient exactness forces the genuine relative-cofibration condition. -/
theorem exactFunctorSequence_cofibration
    (hH : ∀ {X Y : C} (f : X ⟶ Y), E.inflation f → E'.inflation (H.map f)) :
    Additivity.IsCofibrationTransformation (ofExactCategory E') a (ofExactCategory E) where
  app_cof X := E'.inflation_of_conflation (hc X)
  relative_cof {X Y} f hf := by
    let : HasPushout (exactFunctorSequenceAt a b w X).f
        (exactFunctorSequenceMap a b w f).τ₁ := Additivity.hasPushout (ofExactCategory E') a
      (fun X ↦ E'.inflation_of_conflation (hc X)) f
    exact relativePushout_inflation E' (exactFunctorSequenceMap a b w f)
      (hc X) (hc Y) (hH f hf)

include w hc in
/-- A pointwise conflation sequence of genuine exact functors satisfies
all structural hypotheses of Waldhausen additivity. -/
theorem exactFunctorSequence_isCofibrationSequence
    (EF : ExactCategory.ExactFunctor E E') (EG : ExactCategory.ExactFunctor E E')
    (EH : ExactCategory.ExactFunctor E E')
    (hF : EF.toFunctor = F) (hG : EG.toFunctor = G) (hH : EH.toFunctor = H) :
    Additivity.IsCofibrationSequence (ofExactCategory E) (ofExactCategory E') a b where
  exactF := hF ▸ EF.waldhausenExact
  exactG := hG ▸ EG.waldhausenExact
  exactH := hH ▸ EH.waldhausenExact
  cofibration := exactFunctorSequence_cofibration E E' a b w hc (by
    intro X Y f hf
    rw [← hH]
    exact EH.map_inflation f hf)
  cofiber X := CategoryTheory.Limits.isPushout_of_isColimit_cokernel _ (E'.cokernel _ (hc X))
    (ofExactCategory E').isZero _ _

end CategoryTheory.Waldhausen.GilletWaldhausen
