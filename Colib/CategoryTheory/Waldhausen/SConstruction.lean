/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.MorphismProperty.Composition

/-!
# The diagonal Waldhausen S-construction

An n-simplex is an n-chain of pointwise weak equivalences between genuine
Waldhausen Sₙ diagrams. Such a diagram has zero diagonal, cofibration rows,
and the quotient pushout squares. Both simplex directions are reindexed
simultaneously. This builds the actual diagonal of N(wS•C); it does not replace
weak equivalences by isomorphisms or by arbitrary chain maps.

The construction itself only needs two morphism classes. The Waldhausen
axioms, and theorems such as additivity and localization, are separate.
Implementation provenance: adapted from `Quillen/Waldhausen/SConstruction.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This isolated draft has not been compiled.

-/
@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen

/-- The arrow poset of the ordinal [n], represented by pairs i ≤ j. -/
abbrev Interval (n : SimplexCategory) :=
  { p : Fin (n.len + 1) × Fin (n.len + 1) // p.1 ≤ p.2 }

/-- The object (i,j) of the arrow poset. -/
def interval {n : SimplexCategory} (i j : Fin (n.len + 1)) (h : i ≤ j) : Interval n :=
  ⟨(i, j), h⟩

/-- The indexing poset for a diagonal simplex: nerve index × arrow index. -/
def Grid (n : SimplexCategory) := Fin (n.len + 1) × Interval n

instance (n : SimplexCategory) : PartialOrder (Grid n) :=
  inferInstanceAs (PartialOrder (Fin (n.len + 1) × Interval n))

/-- The object with nerve index t and arrow index (i,j). -/
def grid {n : SimplexCategory} (t i j : Fin (n.len + 1)) (h : i ≤ j) : Grid n :=
  (t, interval i j h)

/-- Simultaneous restriction in the nerve and S-construction directions. -/
def gridMap {m n : SimplexCategory} (α : m ⟶ n) : Grid m ⥤ Grid n :=
  (show Monotone (fun p : Grid m ↦
      (α.toOrderHom p.1,
        interval (α.toOrderHom p.2.1.1) (α.toOrderHom p.2.1.2)
          (α.toOrderHom.monotone p.2.2))) from
    fun _ _ h ↦ ⟨α.toOrderHom.monotone h.1,
      α.toOrderHom.monotone h.2.1, α.toOrderHom.monotone h.2.2⟩).functor

variable {C : Type u} [Category.{v} C]

/-- The actual S-construction conditions on a chain of quotient diagrams. -/
structure IsSimplex (cof weq : MorphismProperty C) {n : SimplexCategory}
    (F : Grid n ⥤ C) : Prop where
  /-- Each diagonal object of each quotient diagram is zero. -/
  zero (t i) : IsZero (F.obj (grid t i i le_rfl))
  /-- Every horizontal inclusion in each quotient diagram is a cofibration. -/
  cofibration (t i j k) (hij : i ≤ j) (hjk : j ≤ k) :
    cof (F.map (homOfLE (show grid t i j hij ≤ grid t i k (hij.trans hjk) from
      ⟨le_rfl, le_rfl, hjk⟩)))
  /-- Quotients are specified by categorical pushout squares. -/
  quotient (t i j k) (hij : i ≤ j) (hjk : j ≤ k) :
    IsPushout
      (F.map (homOfLE (show grid t i j hij ≤ grid t i k (hij.trans hjk) from
        ⟨le_rfl, le_rfl, hjk⟩)))
      (F.map (homOfLE (show grid t i j hij ≤ grid t j j le_rfl from
        ⟨le_rfl, hij, le_rfl⟩)))
      (F.map (homOfLE (show grid t i k (hij.trans hjk) ≤ grid t j k hjk from
        ⟨le_rfl, hij, le_rfl⟩)))
      (F.map (homOfLE (show grid t j j le_rfl ≤ grid t j k hjk from
        ⟨le_rfl, le_rfl, hjk⟩)))
  /-- Morphisms in the nerve direction are pointwise weak equivalences. -/
  weak (s t i j) (hst : s ≤ t) (hij : i ≤ j) :
    weq (F.map (homOfLE (show grid s i j hij ≤ grid t i j hij from
      ⟨hst, le_rfl, le_rfl⟩)))

variable (cof weq : MorphismProperty C)

/-- Restriction preserves all S-construction and weak-equivalence conditions. -/
theorem IsSimplex.precomp {m n : SimplexCategory} {F : Grid n ⥤ C}
    (hF : IsSimplex cof weq F) (α : m ⟶ n) :
    IsSimplex cof weq (gridMap α ⋙ F) where
  zero t i := hF.zero (α.toOrderHom t) (α.toOrderHom i)
  cofibration t i j k hij hjk := hF.cofibration (α.toOrderHom t) (α.toOrderHom i)
    (α.toOrderHom j) (α.toOrderHom k)
    (α.toOrderHom.monotone hij) (α.toOrderHom.monotone hjk)
  quotient t i j k hij hjk := hF.quotient (α.toOrderHom t) (α.toOrderHom i)
    (α.toOrderHom j) (α.toOrderHom k)
    (α.toOrderHom.monotone hij) (α.toOrderHom.monotone hjk)
  weak s t i j hst hij := hF.weak (α.toOrderHom s) (α.toOrderHom t)
    (α.toOrderHom i) (α.toOrderHom j)
    (α.toOrderHom.monotone hst) (α.toOrderHom.monotone hij)

/-- The diagonal simplicial set of the nerve of the weak-equivalence
subcategory of the S-construction. Its simplices include the actual quotient
pushout data and weak-equivalence condition. -/
def sSet : SSet.{max u v} where
  obj n := { F : Grid n.unop ⥤ C // IsSimplex cof weq F }
  map α := ↾fun F ↦ ⟨gridMap α.unop ⋙ F.1, F.2.precomp cof weq α.unop⟩
  map_id n := by
    ext F
    rfl
  map_comp α β := by
    ext F
    rfl

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0146",
  colib_ref "Waldhausen1985" "Section 1.3, pp.328-329"
    "background" "Unnormalized zero-diagonal variant; no strict-model or nerve comparison"]
  CategoryTheory.Waldhausen.Interval
  CategoryTheory.Waldhausen.interval
  CategoryTheory.Waldhausen.Grid
  CategoryTheory.Waldhausen.grid
  CategoryTheory.Waldhausen.gridMap
  CategoryTheory.Waldhausen.IsSimplex
  CategoryTheory.Waldhausen.IsSimplex.precomp
  CategoryTheory.Waldhausen.sSet
