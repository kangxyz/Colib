/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.KTheory.Quillen.Map.Basic

/-!
# Pointed homotopy maps and Quillen K-map identity regression tests

Topological source and target universes remain independent. The categorical
rebasing and exact-functor consumers retain their stated shared universes.
These tests do not assert composition of the rebased Quillen K-maps.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped Topology unitInterval ZeroObject

universe w v u

noncomputable section

section Topology

variable {N : Type w} {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
  (f : C(X, Y)) (h : f x = y)

example (p : GenLoop N X x) (t : N → unitInterval) :
    GenLoop.postcomp f h p t = f (p t) := rfl

example (p : GenLoop N X x) :
    HomotopyGroup.map f h (Quotient.mk' p) = Quotient.mk' (GenLoop.postcomp f h p) := rfl

example [DecidableEq N] (i : N) (p q : GenLoop N X x) :
    GenLoop.postcomp f h (GenLoop.transAt i q p) =
      GenLoop.transAt i (GenLoop.postcomp f h q) (GenLoop.postcomp f h p) :=
  GenLoop.postcomp_transAt f h i q p

example [DecidableEq N] [Nonempty N] (a b : HomotopyGroup N X x) :
    HomotopyGroup.mapHom f h (a * b) =
      HomotopyGroup.mapHom f h a * HomotopyGroup.mapHom f h b :=
  (HomotopyGroup.mapHom f h).map_mul a b

example [DecidableEq N] [Nonempty N] (a b : HomotopyGroup N X x)
    (p q : GenLoop N X x) (ha : a = Quotient.mk' p) (hb : b = Quotient.mk' q) (i : N) :
    HomotopyGroup.mapHom f h (a * b) =
      Quotient.mk' (GenLoop.transAt i (GenLoop.postcomp f h q) (GenLoop.postcomp f h p)) := by
  rw [map_mul]
  subst a
  subst b
  exact HomotopyGroup.mul_spec (i := i)

example (n : ℕ) : HomotopyGroup.Pi (n + 1) X x →* HomotopyGroup.Pi (n + 1) Y y :=
  HomotopyGroup.piMap n f h

example [DecidableEq N] [Nonempty N] :
    HomotopyGroup.mapHom (N := N) (x := x) (ContinuousMap.id X) rfl =
      MonoidHom.id (HomotopyGroup N X x) := HomotopyGroup.mapHom_id

end Topology

section Rebase

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d)

example : (rebaseFunctor F c d e).obj c = d := rebaseFunctor_obj_base F c d e

example {X Y : C} (f : X ⟶ Y) : (rebaseFunctor F c d e).map f =
    (rebaseObjIso F c d e X).inv ≫ F.map f ≫ (rebaseObjIso F c d e Y).hom := rfl

example : classifyingSpaceMap (rebaseFunctor F c d e) (classifyingSpacePoint c) =
    classifyingSpacePoint d := rebaseFunctor_map_point F c d e

example (n : ℕ) : pointedShiftedHomotopyGroupMap F c d e n =
    HomotopyGroup.piMap n (classifyingSpaceMap (rebaseFunctor F c d e)).hom
      (rebaseFunctor_map_point F c d e) := rfl

example (n : ℕ) : pointedShiftedHomotopyGroupMap (𝟭 C) c c (Iso.refl c) n =
    MonoidHom.id (ShiftedHomotopyGroup C c n) := pointedShiftedHomotopyGroupMap_id c n

end Rebase

section Exact

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')

example (n : ℕ) : F.KMap n =
    F.toQCompatibleFunctor.kMapWithZeroIso F.toFunctor.mapZeroObject n := rfl

example (n : ℕ) : F.KMap n =
    pointedShiftedHomotopyGroupMap F.mapQ
      (QConstruction.of E.deflation E.inflation (0 : C))
      (QConstruction.of E'.deflation E'.inflation (0 : D))
      (E'.qIsoOfIso F.toFunctor.mapZeroObject) n := rfl

example (n : ℕ) : (ExactFunctor.id E).KMap n = MonoidHom.id (E.K n) :=
  ExactFunctor.KMap_id E n

example (n : ℕ) (a : E.K n) : (ExactFunctor.id E).KMap n a = a := by
  rw [ExactFunctor.KMap_id]
  rfl

end Exact
