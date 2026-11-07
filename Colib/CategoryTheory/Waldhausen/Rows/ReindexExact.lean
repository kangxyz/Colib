/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Structure
public import Colib.CategoryTheory.Waldhausen.Rows.Reindex

/-! # Exact ordinal restriction of the original quotient rows

Implementation provenance: `Quillen/Waldhausen/SConstruction/Rows/Reindex.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`, exactness declarations.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The all-triples Reedy condition is preserved by every ordinal map,
including maps which do not preserve the first or final vertex. -/
theorem reindex_cof {m n : SimplexCategory} (α : m ⟶ n)
    {F G : Obj W n} {η : F ⟶ G} (hη : cof W n η) : cof W m ((reindex W α).map η) := by
  intro i j k hij hjk
  exact hη (α.toOrderHom i) (α.toOrderHom j) (α.toOrderHom k)
    (α.toOrderHom.monotone hij) (α.toOrderHom.monotone hjk)

/-- Every actual ordinal restriction is a genuine exact functor. -/
theorem reindex_exact {m n : SimplexCategory} (α : m ⟶ n) :
    IsExact (waldhausenStructure W n).cof (waldhausenStructure W n).weq
      (waldhausenStructure W m).cof (waldhausenStructure W m).weq (reindex W α) where
  zero h := isZero_of_components W _ (fun p ↦ evaluation_isZero W h ((indexMap α).obj p))
  cofibration _ h := reindex_cof W α h
  weak _ h p := h ((indexMap α).obj p)
  pushout hf h := isPushout_of_pointwise W _ _ _ _
    (fun p ↦ pointwise_of_isPushout W hf h ((indexMap α).obj p))

end CategoryTheory.Waldhausen.QuotientRows
