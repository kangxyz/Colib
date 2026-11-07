/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.SmallCategory
public import Colib.KTheory.Waldhausen.Functoriality
public import Mathlib.Algebra.Category.Grp.Basic

/-! # Small Waldhausen categories and their original homotopical K-functor

Morphisms are all original exact functors, with no strict preservation of the
chosen zero required. The actual existing KMap supplies the group-valued
functor, including its already-proved canonical zero rebasing.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u
namespace CategoryTheory.Waldhausen

namespace SmallWaldhausenCategory

/-- The existing genuine homotopical K-groups and canonical exact-functor maps. -/
def KFunctor (n : ℕ) : SmallWaldhausenCategory.{u} ⥤ GrpCat.{u} where
  obj C := GrpCat.of (C.waldhausen.K n)
  map F := GrpCat.ofHom (KMap F.isExact n)
  map_id C := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DFunLike.congr_fun (KMap_id C.waldhausen n) x
  map_comp F G := by
    apply ConcreteCategory.hom_ext
    intro x
    exact DFunLike.congr_fun (KMap_comp_KMap F.isExact G.isExact n).symm x

end SmallWaldhausenCategory
end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0158",
  colib_ref "Waldhausen1985" "Section 1.3, pp. 328-330" "background"
    "Exact functoriality background; canonical rebasing is explicit in the unnormalized model"]
  CategoryTheory.Waldhausen.SmallWaldhausenCategory.KFunctor
