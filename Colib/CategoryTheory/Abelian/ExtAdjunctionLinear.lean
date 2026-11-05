/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction

/-!
# Linear form of the native exact-adjunction map on Ext

The map and its bijectivity are the existing Stacks map. This file only records its linearity
and the triangle identity needed by scalar extension. It replaces the newer Mathlib adjunction
API used by `Aglib.Algebra.Homology.Koszul.Ext.BaseChange` without copying its construction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w w'

namespace Stacks.ExtAdjunction

variable {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
  {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [HasExt.{w} C] [HasExt.{w'} D]
  (R : Type*) [CommRing R] [Linear R C] [Linear R D] [L.Linear R]

/-- The existing adjunction map, bundled as a linear map. -/
def extMapLinear (X : C) (Y : D) (n : ℕ) :
    Ext.{w} X (G.obj Y) n →ₗ[R] Ext.{w'} (L.obj X) Y n :=
  ((Ext.mk₀ (adj.counit.app Y)).postcompOfLinear R (L.obj X) (add_zero n)).comp
    (L.mapExtLinearMap R X (G.obj Y) n)

/-- Linearity does not change the Stacks adjunction map. -/
lemma extMapLinear_apply (X : C) (Y : D) (n : ℕ) (x : Ext.{w} X (G.obj Y) n) :
    extMapLinear adj R X Y n x = extMap adj X Y n x := rfl

/-- Postcomposing with the unit and then applying the adjunction map is scalar extension. -/
lemma extMapLinear_comp_unit (X Y : C) (n : ℕ) :
    (extMapLinear adj R X (L.obj Y) n).comp
        ((Ext.mk₀ (adj.unit.app Y)).postcompOfLinear R X (add_zero n)) =
      L.mapExtLinearMap R X Y n := by
  ext x
  change ((x.comp (Ext.mk₀ (adj.unit.app Y)) (add_zero n)).mapExactFunctor L).comp
    (Ext.mk₀ (adj.counit.app (L.obj Y))) (add_zero n) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]
  erw [adj.left_triangle_components, Ext.comp_mk₀_id]
  rfl

variable [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [EnoughInjectives D]

/-- The existing Stacks bijection upgraded to a linear equivalence. -/
def extMapLinearEquiv (X : C) (Y : D) (n : ℕ) :
    Ext.{w} X (G.obj Y) n ≃ₗ[R] Ext.{w'} (L.obj X) Y n :=
  LinearEquiv.ofBijective (extMapLinear adj R X Y n) (extMap_bijective adj X Y n)

end Stacks.ExtAdjunction
