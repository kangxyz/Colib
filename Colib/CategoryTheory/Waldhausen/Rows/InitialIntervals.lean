/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.Basic

/-! # Initial intervals and their canonical quotient maps

The initial-interval inclusion and the quotient arrows depend only on the
original quotient row. Exact-category cokernel descent and general Waldhausen
pushout descent use these same maps.

Implementation provenance: `Quillen/Waldhausen/SConstruction/Rows/InitialFlag.lean`
and `Quillen/Waldhausen/QuillenComparison/InitialFlag.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The existing native initial-interval
inclusion is retained, and its quotient map is generalized from exact categories
to arbitrary Waldhausen structures without changing its definition.
-/
@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace CategoryTheory.Waldhausen.QuotientRows

/-- The initial intervals [0,i] in a simplex, including the zero vertex. -/
def initialIntervals (n : SimplexCategory) : Fin (n.len + 1) ⥤ Interval n :=
  (show Monotone (fun i : Fin (n.len + 1) ↦ interval 0 i (Fin.zero_le i)) from
    fun _ _ h ↦ ⟨le_rfl, h⟩).functor

variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The canonical quotient arrow from the initial interval to a row object. -/
def initialQuotient {n : SimplexCategory} (A : Obj W n) (p : Interval n) :
    A.obj.obj (interval 0 p.val.2 (Fin.zero_le _)) ⟶ A.obj.obj p :=
  A.obj.map (homOfLE ⟨Fin.zero_le _, le_rfl⟩)

end CategoryTheory.Waldhausen.QuotientRows
