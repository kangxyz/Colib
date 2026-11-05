/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.GrothendieckGroup.AbelianNaturality

/-!
# Exact-functor and algebraic K₀ regression tests

Identity and composition are checked on whole groups, not only object classes.
The abelian comparison uses the actual Stacks map in both directions.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

universe v₁ v₂ v₃ u₁ u₂ u₃

section Exact

variable {C : Type u₁} {D : Type u₂} {B : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} B]
  [Preadditive C] [Preadditive D] [Preadditive B]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasFiniteBiproducts B]
  {E : ExactStructure C} {E' : ExactStructure D} {E'' : ExactStructure B}
  (F : ExactFunctor E E') (G : ExactFunctor E' E'')

example (S : ShortComplex C) (hS : E.conflation S) :
    E''.conflation (S.map (F.toFunctor ⋙ G.toFunctor)) :=
  (F.comp G).map_conflation S hS

example {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    E'.inflation (F.toFunctor.map i) := F.map_inflation i hi

example {X Y : C} (p : X ⟶ Y) (hp : E.deflation p) :
    E'.deflation (F.toFunctor.map p) := F.map_deflation p hp

example (X : C) : F.grothendieckMap (E.grothendieckClass X) =
    E'.grothendieckClass (F.toFunctor.obj X) := by
  simp

example (x : E.GrothendieckGroup) : (ExactFunctor.id E).grothendieckMap x = x := by
  simp

example (x : E.GrothendieckGroup) :
    (F.comp G).grothendieckMap x = G.grothendieckMap (F.grothendieckMap x) := by
  simp

end Exact

section Abelian

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]

attribute [local instance] Abelian.hasFiniteBiproducts

variable (F : ExactFunctor (abelianExactStructure C) (abelianExactStructure D))

example (x : (abelianExactStructure C).GrothendieckGroup) :
    abelianGrothendieckEquiv D (F.grothendieckMap x) =
      GrothendieckGroup.map F.toFunctor (fun S hS => F.map_conflation S hS)
        (abelianGrothendieckEquiv C x) :=
  DFunLike.congr_fun F.abelianGrothendieckEquiv_naturality x

example (x : GrothendieckGroup C) :
    F.grothendieckMap ((abelianGrothendieckEquiv C).symm x) =
      (abelianGrothendieckEquiv D).symm
        (GrothendieckGroup.map F.toFunctor (fun S hS => F.map_conflation S hS) x) :=
  DFunLike.congr_fun F.abelianGrothendieckEquiv_symm_naturality x

example (X : C) :
    GrothendieckGroup.map F.toFunctor (fun S hS => F.map_conflation S hS)
      (abelianGrothendieckEquiv C ((abelianExactStructure C).grothendieckClass X)) =
        GrothendieckGroup.of (F.toFunctor.obj X) := by
  rw [abelianGrothendieckEquiv_class]
  exact GrothendieckGroup.map_of F.toFunctor (fun S hS => F.map_conflation S hS) X

end Abelian
