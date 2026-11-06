/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.Adjunction

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.Interchange
public import Colib.Topology.ClassifyingSpace.Contraction
public import Mathlib.CategoryTheory.Widesubcategory

/-! # Relative-inner-S interchange on the actual fine-weak categories

The exact inverse transpositions restrict to the original fine weak maps.
The classifying-space equivalence keeps the original forward and inverse
maps. No change of weak class is made by this structural interchange.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/WeakInterchange.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- Fine-weak maps in the original S-construction of the actual relative category. -/
abbrev InnerSWeakRows (m n : SimplexCategory) :=
  WideSubcategory (QuotientRows.waldhausenStructure (waldhausenStructure N n) m).weq

/-- Fine-weak maps in the relative category of the original inner S-construction. -/
abbrev RelativeInnerSWeakRows (m n : SimplexCategory) :=
  WideSubcategory (waldhausenStructure (RowWeakEquivalences.nested N m) n).weq

/-- Restrict the literal forward transposition to the original fine weak maps. -/
def innerSWeakInterchange (m n : SimplexCategory) :
    InnerSWeakRows N m n ⥤ RelativeInnerSWeakRows N m n where
  obj X := ⟨(innerSInterchange N m n).obj X.obj⟩
  map f := ⟨(innerSInterchange N m n).map f.hom, innerSInterchange_weak N f.hom f.property⟩
  map_id X := WideSubcategory.hom_ext _ ((innerSInterchange N m n).map_id X.obj)
  map_comp f g := WideSubcategory.hom_ext _ ((innerSInterchange N m n).map_comp f.hom g.hom)

/-- Restrict the literal inverse transposition to the same fine weak class. -/
def innerSWeakInverse (m n : SimplexCategory) :
    RelativeInnerSWeakRows N m n ⥤ InnerSWeakRows N m n where
  obj X := ⟨(innerSInverse N m n).obj X.obj⟩
  map f := ⟨(innerSInverse N m n).map f.hom, (innerSInverse_exact N m n).weak _ f.property⟩
  map_id X := WideSubcategory.hom_ext _ ((innerSInverse N m n).map_id X.obj)
  map_comp f g := WideSubcategory.hom_ext _ ((innerSInverse N m n).map_comp f.hom g.hom)

@[simp] theorem innerSWeakInterchange_inverse (m n : SimplexCategory) :
    innerSWeakInterchange N m n ⋙ innerSWeakInverse N m n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

@[simp] theorem innerSWeakInverse_interchange (m n : SimplexCategory) :
    innerSWeakInverse N m n ⋙ innerSWeakInterchange N m n = 𝟭 _ := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

/-- A genuine equivalence of the two actual fine-weak categories. -/
def innerSWeakEquivalence (m n : SimplexCategory) :
    InnerSWeakRows N m n ≌ RelativeInnerSWeakRows N m n :=
  CategoryTheory.Equivalence.mk (innerSWeakInterchange N m n) (innerSWeakInverse N m n)
    (eqToIso (innerSWeakInterchange_inverse N m n).symm)
    (eqToIso (innerSWeakInverse_interchange N m n))

/-- The original classifying-space forward map has an actual continuous homotopy inverse. -/
def innerSWeakClassifyingHomotopyEquiv (m n : SimplexCategory) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (InnerSWeakRows N m n))
      (ClassifyingSpace (RelativeInnerSWeakRows N m n)) :=
  equivalenceClassifyingHomotopyEquiv (innerSWeakEquivalence N m n)

@[simp] theorem innerSWeakClassifyingHomotopyEquiv_toFun (m n : SimplexCategory) :
    (innerSWeakClassifyingHomotopyEquiv N m n).toFun =
      (classifyingSpaceMap (innerSWeakInterchange N m n)).hom := rfl

@[simp] theorem innerSWeakClassifyingHomotopyEquiv_invFun (m n : SimplexCategory) :
    (innerSWeakClassifyingHomotopyEquiv N m n).invFun =
      (classifyingSpaceMap (innerSWeakInverse N m n)).hom := rfl

/-- Every underlying forward component remains the original component with its indices exchanged. -/
@[simp] theorem innerSWeakInterchange_map_component {m n : SimplexCategory}
    {X Y : InnerSWeakRows N m n} (f : X ⟶ Y) (p : Interval (addInitial.obj n)) (q : Interval m) :
    (((innerSWeakInterchange N m n).map f).hom.hom.hom.app p).hom.app q =
      ((f.hom.hom.app q).hom.hom.app p) := rfl

end CategoryTheory.Waldhausen.Fibration.RelativeRows
