/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.Basic

/-! Regression coverage for the actual realized nerve, its chosen vertex,
independent object/hom universes, degree shift and positive-degree commutativity.
The group checks retain the anonymous consumers in the two source modules. -/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

section ClassifyingSpace

variable (C : Type u) [Category.{v} C]

example : ClassifyingSpace C = SSet.toTop.obj (CategoryTheory.nerve C) := rfl

example (c : C) :
    classifyingSpacePoint c = SSet.toTop.map (nerveVertexMap c) default := rfl

example (c : C) (n : ℕ) :
    ShiftedHomotopyGroup C c n =
      _root_.HomotopyGroup.Pi (n + 1) (ClassifyingSpace C) (classifyingSpacePoint c) := rfl

example (c : C) (n : ℕ) : Group (ShiftedHomotopyGroup C c n) := inferInstance

example (c : C) (n : ℕ) : CommGroup (ShiftedHomotopyGroup C c (n + 1)) :=
  inferInstance

example (c : C) (n : ℕ) (hn : 1 ≤ n) : CommGroup (ShiftedHomotopyGroup C c n) :=
  shiftedHomotopyGroupCommGroupOfPositive c n hn

variable {D : Type u} [Category.{v} D]

example (F : C ⥤ D) (c : C) :
    classifyingSpaceMap F (classifyingSpacePoint c) = classifyingSpacePoint (F.obj c) :=
  classifyingSpaceMap_point F c

end ClassifyingSpace

section RestrictedSpans

variable {C : Type u} [Category.{v} C] (d i : MorphismProperty C)
  [d.ContainsIdentities] [i.ContainsIdentities]
  [d.IsStableUnderComposition] [i.IsStableUnderComposition]
  [d.HasPullbacksAgainst i] [d.IsStableUnderBaseChangeAgainst i]
  [i.IsStableUnderBaseChangeAgainst d]

example : QConstruction.classifyingSpace d i =
    SSet.toTop.obj (CategoryTheory.nerve (QConstruction d i)) := rfl

example (c : C) (n : ℕ) : QConstruction.HomotopyGroup d i c n =
    _root_.HomotopyGroup.Pi (n + 1) (QConstruction.classifyingSpace d i)
      (classifyingSpacePoint (QConstruction.of d i c)) := rfl

example (c : C) (n : ℕ) : Group (QConstruction.HomotopyGroup d i c n) := inferInstance

example (c : C) (n : ℕ) : CommGroup (QConstruction.HomotopyGroup d i c (n + 1)) :=
  inferInstance

end RestrictedSpans

section ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactCategory.ExactStructure C)

example : E.kBasepoint =
    classifyingSpacePoint (QConstruction.of E.deflation E.inflation (0 : C)) := rfl

example : E.KSpace = SSet.toTop.obj (CategoryTheory.nerve E.QCategory) := rfl

example : E.kBasepoint = SSet.toTop.map
    (nerveVertexMap (QConstruction.of E.deflation E.inflation (0 : C))) default := rfl

example (n : ℕ) : E.K n = _root_.HomotopyGroup.Pi (n + 1) E.KSpace E.kBasepoint := rfl

example (n : ℕ) : Group (E.K n) := inferInstance

example (n : ℕ) : CommGroup (E.K (n + 1)) := inferInstance

example (n : ℕ) (hn : 1 ≤ n) : CommGroup (E.K n) :=
  shiftedHomotopyGroupCommGroupOfPositive
    (QConstruction.of E.deflation E.inflation (0 : C)) n hn

end ExactCategory
