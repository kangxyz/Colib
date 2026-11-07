/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.Exact
public import Colib.CategoryTheory.ExactCategory.QCategory

/-! # Canonical subquotient spans on native exact quotient rows

The interval-containment functor retains the actual subquotient objects and
arrows of `QuotientRows.Obj (ofExactCategory E)`. Its composition is the genuine
admissible pullback composition of `CategoryTheory.QConstruction`.

Adapted from `Quillen/Waldhausen/QuillenComparison/IntervalSpans.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. No separate row model is introduced.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u
namespace CategoryTheory.Waldhausen.QuotientRows

/-- Intervals ordered by containment: the left endpoint reverses direction. -/
def NestedInterval (n : SimplexCategory) :=
  { p : (Fin (n.len + 1))ᵒᵈ × Fin (n.len + 1) // OrderDual.ofDual p.1 ≤ p.2 }

instance (n : SimplexCategory) : PartialOrder (NestedInterval n) :=
  inferInstanceAs (PartialOrder { p : (Fin (n.len + 1))ᵒᵈ × Fin (n.len + 1) //
    OrderDual.ofDual p.1 ≤ p.2 })

namespace NestedInterval

variable {n : SimplexCategory}

/-- The left endpoint of a nested interval, converted from the order-dual coordinate used for
containment. -/
def left (p : NestedInterval n) : Fin (n.len + 1) := OrderDual.ofDual p.1.1

/-- The right endpoint of a nested interval in the original finite ordinal. -/
def right (p : NestedInterval n) : Fin (n.len + 1) := p.1.2

theorem endpoints (p : NestedInterval n) : p.left ≤ p.right := p.2

theorem left_anti {p q : NestedInterval n} (h : p ≤ q) : q.left ≤ p.left := h.1

theorem right_mono {p q : NestedInterval n} (h : p ≤ q) : p.right ≤ q.right := h.2

end NestedInterval

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)
variable {n : SimplexCategory} (F : Obj (ofExactCategory E) n)

/-- The object associated to an interval is its already specified quotient. -/
def rowObject (p : NestedInterval n) : C :=
  F.obj.obj (interval p.left p.right p.endpoints)

/-- The canonical admissible span associated to interval containment. -/
def intervalSpan {p q : NestedInterval n} (h : p ≤ q) :
    Span E.deflation E.inflation (rowObject E F p) (rowObject E F q) where
  apex := F.obj.obj (interval q.left p.right ((NestedInterval.left_anti h).trans p.endpoints))
  l := rowMap E F ((NestedInterval.left_anti h).trans p.endpoints) p.endpoints
    (NestedInterval.left_anti h) le_rfl
  r := rowMap E F ((NestedInterval.left_anti h).trans p.endpoints) q.endpoints le_rfl
    (NestedInterval.right_mono h)
  wl := row_deflation E F q.left p.left p.right (NestedInterval.left_anti h) p.endpoints
  wr := F.property.cofibration q.left p.right q.right
    ((NestedInterval.left_anti h).trans p.endpoints) (NestedInterval.right_mono h)

/-- The span of an identity containment represents the identity Q-morphism. -/
@[simp]
theorem intervalSpan_id (p : NestedInterval n) :
    QConstruction.mkHom E.deflation E.inflation (intervalSpan E F (le_refl p)) =
      𝟙 (QConstruction.of E.deflation E.inflation (rowObject E F p)) := by
  change QConstruction.mkHom _ _ _ = QConstruction.mkHom _ _ (Span.id _)
  refine QConstruction.mkHom_eq_of_apexIso E.deflation E.inflation
    (intervalSpan E F (le_refl p)) (Span.id _) (Iso.refl _) ?_ ?_
  · simp [intervalSpan, rowMap]
  · simp [intervalSpan, rowMap]

/-- The pullback defining composition of canonical spans is the intervening
subquotient. Therefore the represented Q-arrows compose exactly. -/
@[reassoc (attr := simp)]
theorem intervalSpan_comp {p q r : NestedInterval n}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    QConstruction.mkHom E.deflation E.inflation (intervalSpan E F hpq) ≫
      QConstruction.mkHom E.deflation E.inflation (intervalSpan E F hqr) =
        QConstruction.mkHom E.deflation E.inflation (intervalSpan E F (hpq.trans hqr)) := by
  let sq := (row_isPullback E F r.left q.left p.right q.right
    (NestedInterval.left_anti hqr) ((NestedInterval.left_anti hpq).trans p.endpoints)
      (NestedInterval.right_mono hpq)).flip
  let := sq.hasPullback
  symm
  apply QConstruction.mkHom_eq_of_apexIso _ _ _ _ sq.isoPullback
  · change sq.isoPullback.hom ≫ pullback.fst _ _ ≫ _ = _
    rw [← Category.assoc, sq.isoPullback_hom_fst]
    simp only [intervalSpan, rowMap, ← F.obj.map_comp]
    congr 1
  · change sq.isoPullback.hom ≫ pullback.snd _ _ ≫ _ = _
    rw [← Category.assoc, sq.isoPullback_hom_snd]
    simp only [intervalSpan, rowMap, ← F.obj.map_comp]
    congr 1

/-- A genuine S-row defines a functor from interval containment to the
existing Quillen category. Neither category is redefined for this comparison. -/
def intervalQFunctor : NestedInterval n ⥤ QConstruction E.deflation E.inflation where
  obj p := QConstruction.of E.deflation E.inflation (rowObject E F p)
  map f := QConstruction.mkHom E.deflation E.inflation (intervalSpan E F (leOfHom f))
  map_id p := intervalSpan_id E F p
  map_comp f g := (intervalSpan_comp E F (leOfHom f) (leOfHom g)).symm

end CategoryTheory.Waldhausen.QuotientRows
