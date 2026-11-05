/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# Simplex representatives of realization points

Every point in the actual geometric realization lies in the image of a realized
representable simplex. This uses the pointwise left Kan extension and joint surjectivity of
its colimit inclusions; no connectedness or exact-category assumption is needed.

## Implementation provenance

Adapted from `Quillen/Topology/Realization/Connectivity.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The selected declarations retain the source
constructions and mathematical universe parameters. Namespace and dependency ownership
are changed to the underlying Mathlib objects.
-/
@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace SSet

/-- Every point of geometric realization is represented by a point of a simplex. -/
theorem realization_exists_simplex {X : SSet.{u}} (x : |X|) :
    ∃ (n : SimplexCategory) (f : SSet.stdSimplex.obj n ⟶ X)
      (t : |SSet.stdSimplex.obj n|), SSet.toTop.map f t = x := by
  let e := SSet.stdSimplex.leftKanExtensionObjIsoColimit SimplexCategory.toTop X
  obtain ⟨j, t, ht⟩ := Concrete.colimit_exists_rep
    (CostructuredArrow.proj SSet.stdSimplex X ⋙ SimplexCategory.toTop) (e.hom x)
  refine ⟨j.left, j.hom, SSet.toTopSimplex.inv.app j.left t, ?_⟩
  have h := congrArg (fun y => e.inv y) ht
  have hx : e.inv (e.hom x) = x := by
    change (e.hom ≫ e.inv) x = x
    rw [e.hom_inv_id]
    rfl
  rw [hx] at h
  change (colimit.ι _ j ≫ e.inv) t = x at h
  change (colimit.ι _ j ≫ (SSet.stdSimplex.leftKanExtensionObjIsoColimit
    SimplexCategory.toTop X).inv) t = x at h
  rw [Functor.ι_leftKanExtensionObjIsoColimit_inv] at h
  exact h

end SSet

attribute [colib_tag "COL-0062",
  colib_ref "WeibelKBook" "IV, realization paragraph following Definition 3.1.4" "adaptation"
    "Existence of a simplex representative in the actual realization, without uniqueness"]
  SSet.realization_exists_simplex
