/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckGroup.Functor
public import Colib.KTheory.Waldhausen.AsSmall.Basic
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-! # Universe lifting preserves the original classical Waldhausen presentation

The actual exact up/down functors between the original category and its
existing common-universe model induce mutually inverse maps on the original
object/weak-arrow/cofibration-pushout quotient. Every original generator is retained.

Implementation provenance: `Quillen/Waldhausen/GrothendieckGroup/SmallModel.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u v
namespace CategoryTheory.Waldhausen.AlgebraicGrothendieck
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The actual downward presentation map is a left inverse to the actual upward map. -/
theorem asSmall_down_comp_up :
    (map W.asSmall (AsSmall.down : AsSmall.{0} C ⥤ C) W.asSmall_down_exact).comp
      (map W (AsSmall.up : C ⥤ AsSmall.{0} C) W.asSmall_up_exact) =
        AddMonoidHom.id (Group W) := by
  apply hom_ext W
  intro A
  simp only [AddMonoidHom.comp_apply, map_objectClass, AddMonoidHom.id_apply]
  rfl

/-- The actual upward presentation map is a left inverse to the actual downward map. -/
theorem asSmall_up_comp_down :
    (map W (AsSmall.up : C ⥤ AsSmall.{0} C) W.asSmall_up_exact).comp
      (map W.asSmall (AsSmall.down : AsSmall.{0} C ⥤ C) W.asSmall_down_exact) =
        AddMonoidHom.id (Group W.asSmall) := by
  apply hom_ext W.asSmall
  intro A
  simp only [AddMonoidHom.comp_apply, map_objectClass, AddMonoidHom.id_apply]
  rfl

/-- The actual original algebraic presentation agrees with its genuine common-universe model. -/
def asSmallGrothendieckEquiv : Group W ≃+ Group W.asSmall where
  toFun := map W (AsSmall.up : C ⥤ AsSmall.{0} C) W.asSmall_up_exact
  invFun := map W.asSmall (AsSmall.down : AsSmall.{0} C ⥤ C) W.asSmall_down_exact
  left_inv := DFunLike.congr_fun (asSmall_down_comp_up W)
  right_inv := DFunLike.congr_fun (asSmall_up_comp_down W)
  map_add' := (map W AsSmall.up W.asSmall_up_exact).map_add

/-- The universe-lifting equivalence retains the original upward object class. -/
@[simp] theorem asSmallGrothendieckEquiv_objectClass (A : C) :
    asSmallGrothendieckEquiv W (objectClass W A) =
      objectClass W.asSmall (AsSmall.up.obj A) :=
  map_objectClass W AsSmall.up W.asSmall_up_exact A

/-- Its inverse retains the original downward object class. -/
@[simp] theorem asSmallGrothendieckEquiv_symm_objectClass (A : AsSmall.{0} C) :
    (asSmallGrothendieckEquiv W).symm (objectClass W.asSmall A) =
      objectClass W (AsSmall.down.obj A) :=
  map_objectClass W.asSmall AsSmall.down W.asSmall_down_exact A

variable {D : Type u} [Category.{v} D] (V : Structure D) (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The original universe-lifting algebraic equivalence respects every original exact functor. -/
theorem asSmallGrothendieckEquiv_natural (a : Group W) :
    asSmallGrothendieckEquiv V (map W F hF a) =
      map W.asSmall (asSmallFunctor F) hF.asSmall
        (asSmallGrothendieckEquiv W a) := by
  have h : (asSmallGrothendieckEquiv V : Group V →+ Group V.asSmall).comp (map W F hF) =
      (map W.asSmall (asSmallFunctor F) hF.asSmall).comp
        (asSmallGrothendieckEquiv W : Group W →+ Group W.asSmall) := by
    apply hom_ext W
    intro A
    simp only [AddMonoidHom.comp_apply, map_objectClass,
      AddMonoidHom.coe_ofClass, asSmallGrothendieckEquiv_objectClass]
    rfl
  exact DFunLike.congr_fun h a

end CategoryTheory.Waldhausen.AlgebraicGrothendieck
