/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.ExactCategory
public import Colib.CategoryTheory.Waldhausen.Rows.Basic
public import Colib.CategoryTheory.ExactCategory.CommonKernel
public import Colib.CategoryTheory.Limits.Shapes.ZeroPushoutCokernel

/-! # Conflations and pullbacks in the actual exact quotient rows

Every map is a component of the existing `QuotientRows.Obj` diagram. Zero-corner
pushouts give conflations, hence admissible quotient maps. Overlapping rectangles
are pullbacks, providing the composition law for the Q comparison.

Adapted from `Quillen/Waldhausen/QuillenComparison/ExactRectangles.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, directly on the native row category.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactCategory.ExactStructure C)
variable {n : SimplexCategory} (F : Obj (ofExactCategory E) n)

/-- The arrow in one row between comparable interval objects. -/
def rowMap {i j k l : Fin (n.len + 1)}
    (hij : i ≤ j) (hkl : k ≤ l) (hik : i ≤ k) (hjl : j ≤ l) :
    F.obj.obj (interval i j hij) ⟶ F.obj.obj (interval k l hkl) :=
  F.obj.map (homOfLE (show interval i j hij ≤ interval k l hkl from
    ⟨hik, hjl⟩))

@[simp]
theorem rowMap_id {i j : Fin (n.len + 1)} (hij : i ≤ j) :
    rowMap E F hij hij le_rfl le_rfl = 𝟙 _ := F.obj.map_id _

@[reassoc (attr := simp)]
theorem rowMap_comp {i j k l a b : Fin (n.len + 1)}
    (hij : i ≤ j) (hkl : k ≤ l) (hab : a ≤ b)
    (hik : i ≤ k) (hjl : j ≤ l) (hka : k ≤ a) (hlb : l ≤ b) :
    rowMap E F hij hkl hik hjl ≫ rowMap E F hkl hab hka hlb =
      rowMap E F hij hab (hik.trans hka) (hjl.trans hlb) :=
  (F.obj.map_comp _ _).symm


/-- The two consecutive quotient arrows in an S-row compose to zero. -/
theorem rowMap_zero (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    rowMap E F hij (hij.trans hjk) le_rfl hjk ≫
      rowMap E F (hij.trans hjk) hjk hij le_rfl = 0 := by
  have sq := F.property.quotient i j k hij hjk
  calc
    _ = rowMap E F hij le_rfl hij le_rfl ≫
        rowMap E F le_rfl hjk le_rfl hjk := sq.w
    _ = 0 := by
      have hz : rowMap E F (i := j) le_rfl hjk le_rfl hjk = 0 :=
        (F.property.zero j).eq_of_src _ _
      rw [hz, comp_zero]

/-- Every triple of ordered indices gives a conflation in the original
exact structure, with precisely the maps already present in the S-simplex. -/
theorem row_conflation (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    E.conflation (ShortComplex.mk
      (rowMap E F hij (hij.trans hjk) le_rfl hjk)
      (rowMap E F (hij.trans hjk) hjk hij le_rfl)
      (rowMap_zero E F i j k hij hjk)) := by
  exact E.conflation_of_inflation_of_isCokernel
    (F.property.cofibration i j k hij hjk)
    (cokernelOfZeroPushout (F.property.quotient i j k hij hjk) (F.property.zero j))

/-- Quotient maps in an S-row are admissible epimorphisms. -/
theorem row_deflation (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    E.deflation (rowMap E F (hij.trans hjk) hjk hij le_rfl) :=
  E.deflation_of_conflation (row_conflation E F i j k hij hjk)

/-- An overlapping rectangle of subquotients is a genuine pullback. -/
theorem row_isPullback (i j k l : Fin (n.len + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) :
    IsPullback
      (rowMap E F (hij.trans hjk) (hij.trans (hjk.trans hkl)) le_rfl hkl)
      (rowMap E F (hij.trans hjk) hjk hij le_rfl)
      (rowMap E F (hij.trans (hjk.trans hkl)) (hjk.trans hkl) hij le_rfl)
      (rowMap E F hjk (hjk.trans hkl) le_rfl hkl) := by
  apply E.isPullback_of_conflations_same_kernel
    (row_conflation E F i j k hij hjk)
    (row_conflation E F i j l hij (hjk.trans hkl))
  · simp
  · simp

end CategoryTheory.Waldhausen.QuotientRows
