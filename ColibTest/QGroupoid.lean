/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.GrothendieckGroup.QGroupoid

/-!
# Algebraic Q-groupoid comparison regression tests

These use the actual localization at all arrows and its canonical cocycle lift.
No identification with a realized fundamental group or Quillen K-group is asserted.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

universe u v w z

noncomputable section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

example {X Y : C} (s : Span E.deflation E.inflation X Y) :
    E.qSpanGrothendieckWeight s = E.grothendieckClass s.apex - E.grothendieckClass X := rfl

example {X Y : C} (s : Span E.deflation E.inflation X Y) :
    E.qGrothendieckWeight (QConstruction.mkHom E.deflation E.inflation s) =
      E.grothendieckClass s.apex - E.grothendieckClass X := rfl

example {X Y Z : E.QCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    E.qGrothendieckWeight (f ≫ g) = E.qGrothendieckWeight f + E.qGrothendieckWeight g :=
  E.qGrothendieckWeight_comp f g

example {X Y : E.QCategory} (f : X ⟶ Y) :
    E.qGrothendieckFunctor.map f = Multiplicative.ofAdd (E.qGrothendieckWeight f) := rfl

example {D : Type w} [Groupoid.{z} D] (F : E.QCategory ⥤ D)
    {X Y Z : E.QCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    E.qEdgeClass F (f ≫ g) = E.qEdgeClass F g * E.qEdgeClass F f :=
  E.qEdgeClass_comp F f g

example {D : Type w} [Groupoid.{z} D] (F : E.QCategory ⥤ D)
    {X Y : E.QCategory} (f : X ⟶ Y) : ∃ K : C, E.qEdgeClass F f = E.qObjectClass F K :=
  E.qEdgeClass_eq_objectClass F f

example : E.qGroupoid = (⊤ : MorphismProperty E.QCategory).Localization := rfl

example : E.toQGroupoid = (⊤ : MorphismProperty E.QCategory).Q := rfl

example : E.qGroupoidGrothendieckFunctor =
    Localization.Construction.lift E.qGrothendieckFunctor (fun _ _ _ _ => inferInstance) := rfl

example : E.toQGroupoid ⋙ E.qGroupoidGrothendieckFunctor = E.qGrothendieckFunctor :=
  E.toQGroupoid_comp_grothendieckFunctor

example : E.qGroupoidObjectSubgroup =
    Subgroup.closure (Set.range (E.qObjectClass E.toQGroupoid)) := rfl

example : E.qGroupoidGenerated = ⊤ := E.qGroupoidGenerated_eq_top

example : E.qGroupoidObjectSubgroup = ⊤ := E.qGroupoidObjectSubgroup_eq_top

example : CommGroup E.qGroupoidZeroGroup := inferInstance

example {X Y Z : E.qGroupoid} (f : X ⟶ Y) (g : Y ⟶ Z) :
    E.qGroupoidClosedArrow (f ≫ g) = E.qGroupoidClosedArrow g * E.qGroupoidClosedArrow f :=
  E.qGroupoidClosedArrow_comp f g

example (X : C) : E.qGroupoidToGrothendieck (E.qObjectClass E.toQGroupoid X) =
    Multiplicative.ofAdd (E.grothendieckClass X) := E.qGroupoidToGrothendieck_objectClass X

example (X : C) : E.grothendieckToQGroupoid (Multiplicative.ofAdd (E.grothendieckClass X)) =
    E.qObjectClass E.toQGroupoid X := E.grothendieckToQGroupoid_class X

example (a : Multiplicative E.GrothendieckGroup) :
    E.grothendieckQGroupoidEquiv a = E.grothendieckToQGroupoid a := rfl

example (a : E.qGroupoidZeroGroup) :
    E.grothendieckQGroupoidEquiv.symm a = E.qGroupoidToGrothendieck a := rfl

example (a : Multiplicative E.GrothendieckGroup) :
    E.qGroupoidToGrothendieck (E.grothendieckToQGroupoid a) = a :=
  E.grothendieckQGroupoidEquiv.symm_apply_apply a

example (a : E.qGroupoidZeroGroup) :
    E.grothendieckToQGroupoid (E.qGroupoidToGrothendieck a) = a :=
  E.grothendieckQGroupoidEquiv.apply_symm_apply a

example (X : C) : E.grothendieckQGroupoidEquiv (Multiplicative.ofAdd (E.grothendieckClass X)) =
    E.qObjectClass E.toQGroupoid X := E.grothendieckToQGroupoid_class X

example {G : Type w} [Group G] (f g : Multiplicative E.GrothendieckGroup →* G)
    (h : ∀ X, f (Multiplicative.ofAdd (E.grothendieckClass X)) =
      g (Multiplicative.ofAdd (E.grothendieckClass X))) : f = g :=
  E.grothendieck_mulHom_ext f g h

example {D T : Type w} [Groupoid.{z} D] [Groupoid.{z} T]
    (F : E.QCategory ⥤ D) (G : D ⥤ T) (X : C) :
    E.qObjectClass (F ⋙ G) X = G.map (E.qObjectClass F X) := E.qObjectClass_comp F G X
