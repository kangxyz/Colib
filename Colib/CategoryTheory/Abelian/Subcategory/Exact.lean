/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.CategoryTheory.Preadditive.LeftExact
/-!
# Exact inclusion of an abelian full subcategory

An object property containing zero and closed under subobjects, quotients, and
finite products gives an actual abelian full subcategory. The inclusion creates
kernels and cokernels, preserves finite limits and colimits, and is exact for
the standard abelian exact structures. No extension-closure premise is added.


## Implementation provenance

Adapted from `Aglib/CategoryTheory/Abelian/Subcategory/Exact.lean` at Aglib commit
`2c34f185fa859e862661f939cd216b07bcccfb26`. Actual maps and independent object/hom universes
are retained. No extension-closure assumption or Resolution structure is used.
Redundant source aliases are replaced by the native `P.FullSubcategory`, its
Mathlib abelian instance, and `abelianExactStructure P.FullSubcategory`.
-/
@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExactCategory
open scoped ZeroObject

namespace CategoryTheory.ObjectProperty

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

/-- Under subobject closure, the usual nonemptiness requirement is equivalent
to containing a zero object. -/
theorem containsZero_iff_nonempty [P.IsClosedUnderSubobjects] :
    P.ContainsZero ↔ P.Nonempty := by
  constructor
  · intro h
    let := h
    infer_instance
  · intro h
    let := h
    exact ⟨⟨0, isZero_zero C,
      P.prop_of_mono (0 : (0 : C) ⟶ P.arbitrary) P.prop_arbitrary⟩⟩

variable [P.ContainsZero] [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]
  [P.IsClosedUnderFiniteProducts]

/-- The full-subcategory inclusion preserves finite limits because it creates
kernels. -/
theorem inclusion_preservesFiniteLimits : PreservesFiniteLimits P.ι := by
  let : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
      PreservesLimit (parallelPair f 0) P.ι := fun f => P.preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels P.ι

/-- The full-subcategory inclusion preserves finite colimits because it creates
cokernels. -/
theorem inclusion_preservesFiniteColimits : PreservesFiniteColimits P.ι := by
  let : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
      PreservesColimit (parallelPair f 0) P.ι := fun f => P.preservesCokernels_ι f
  exact Functor.preservesFiniteColimits_of_preservesCokernels P.ι

/-- The actual inclusion is exact for the standard abelian exact structures. -/
def exactInclusion :
    ExactCategory.ExactFunctor (ExactCategory.abelianExactStructure P.FullSubcategory)
      (ExactCategory.abelianExactStructure C) where
  toFunctor := P.ι
  map_conflation S hS := by
    let := inclusion_preservesFiniteLimits P
    let := inclusion_preservesFiniteColimits P
    exact hS.map_of_exact P.ι

end CategoryTheory.ObjectProperty

attribute [colib_ref "WeibelKBook"
  "V, Devissage Theorem 4.1, exact abelian subcategory hypothesis, page 33"
  "ingredient" "The intrinsic abelian full subcategory and its actual exact inclusion"]
  CategoryTheory.ObjectProperty.exactInclusion
