/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Composition
public import Colib.CategoryTheory.ExactCategory.Isomorphisms

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/ExactCategory/KernelComposition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # The admissible inclusion between kernels of composable deflations -/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : ExactStructure C)

/-- The actual map from the kernel of a deflation into the kernel of a composite
of two deflations is an inflation. All kernel objects and maps are retained. -/
theorem inflation_kernelMap_comp {A B K X Y Z : C}
    {i : A ⟶ X} {p : X ⟶ Y} {j : B ⟶ Y} {q : Y ⟶ Z} {k : K ⟶ X}
    {zi : i ≫ p = 0} {zj : j ≫ q = 0} {zk : k ≫ (p ≫ q) = 0}
    (hi : E.conflation (ShortComplex.mk i p zi))
    (hj : E.conflation (ShortComplex.mk j q zj))
    (hk : E.conflation (ShortComplex.mk k (p ≫ q) zk))
    (a : A ⟶ K) (ha : a ≫ k = i) : E.inflation a := by
  let : HasPullback p j := E.deflation.hasPullback j (E.deflation_of_conflation hi)
  let hComp := E.composite_deflation_conflation hi hj
  let e := (E.kernel _ hComp).conePointUniqueUpToIso (E.kernel (ShortComplex.mk k (p ≫ q) zk) hk)
  have he : e.hom ≫ k = pullback.fst p j :=
    (E.kernel _ hComp).conePointUniqueUpToIso_hom_comp (E.kernel (ShortComplex.mk k (p ≫ q) zk) hk)
      WalkingParallelPair.zero
  let hBase := E.pullbackConflation_mem hi j
  let : Mono k := E.mono_of_inflation (E.inflation_of_conflation hk)
  have heq : (pullbackConflation B j (S := ShortComplex.mk i p zi)).f ≫ e.hom = a := by
    apply (cancel_mono k).1
    rw [Category.assoc, he, ha]
    exact pullback.lift_fst _ _ _
  rw [← heq]
  exact E.inflation_comp _ _ (E.inflation_of_conflation hBase) (E.inflation_of_iso e)

end CategoryTheory.ExactCategory.ExactStructure
