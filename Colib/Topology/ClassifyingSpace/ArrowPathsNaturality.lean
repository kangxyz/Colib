/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.ArrowPaths

/-!
# Naturality of realized arrow paths

Adapted from `Quillen/KTheory/GrothendieckComparison/Naturality.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, specified basepoint equalities and multiplication order are retained.
-/

@[expose] public noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits
open scoped Topology ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory

/-- Realizing a functor maps an arrow path to its image arrow path, with
both endpoints transported by the exact vertex equalities. -/
lemma classifyingSpacePath_map {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) {x y : C} (f : x ⟶ y) :
    ((classifyingSpacePath f).map (classifyingSpaceMap F).hom.continuous).cast
      (classifyingSpaceMap_point F x).symm (classifyingSpaceMap_point F y).symm =
      classifyingSpacePath (F.map f) := by
  ext t
  exact classifyingSpacePath_naturality F f t

/-- The canonical category-to-fundamental-groupoid functor is natural up to
the exact equality between mapped object vertices. -/
def classifyingFundamentalGroupoidNaturality
    {C D : Type u} [Category.{v} C] [Category.{v} D] (F : C ⥤ D) :
    classifyingFundamentalGroupoidFunctor C ⋙ FundamentalGroupoid.map (classifyingSpaceMap F).hom ≅
      F ⋙ classifyingFundamentalGroupoidFunctor D :=
  NatIso.ofComponents (fun x => eqToIso (congrArg FundamentalGroupoid.mk
      (classifyingSpaceMap_point F x))) (by
    intro x y f
    apply (cancel_epi (eqToHom (congrArg FundamentalGroupoid.mk
      (classifyingSpaceMap_point F x).symm))).1
    simp only [eqToIso, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [Category.assoc]
    change eqToHom (congrArg FundamentalGroupoid.mk (classifyingSpaceMap_point F x).symm) ≫
      (⟦(classifyingSpacePath f).map (classifyingSpaceMap F).hom.continuous⟧ :
        Path.Homotopic.Quotient _ _) ≫
      eqToHom (congrArg FundamentalGroupoid.mk (classifyingSpaceMap_point F y)) = _
    rw [FundamentalGroupoid.conj_eqToHom
      (classifyingSpaceMap_point F x).symm (classifyingSpaceMap_point F y).symm]
    exact congrArg Path.Homotopic.Quotient.mk (classifyingSpacePath_map F f))

end CategoryTheory
