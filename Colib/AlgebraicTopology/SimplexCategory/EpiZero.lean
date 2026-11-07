/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-! Source: Quillen/CategoryTheory/SimplexCategory.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-!
# The initial vertex under epimorphic simplex operators

Every epimorphism in the simplex category is surjective, so its monotone
underlying map sends the initial vertex to the initial vertex.
-/
@[expose] public section

open CategoryTheory

namespace SimplexCategory

/-- A surjective simplex operator preserves the initial vertex. -/
theorem epi_zero {p q : SimplexCategory} (f : p ⟶ q) [Epi f] :
    f.toOrderHom 0 = 0 := by
  obtain ⟨k, hk⟩ := (epi_iff_surjective.mp (inferInstance : Epi f)) 0
  exact le_antisymm ((f.toOrderHom.monotone (Fin.zero_le k)).trans_eq hk) (Fin.zero_le _)

end SimplexCategory
