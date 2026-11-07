/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Abelian.Subcategory.Exact
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.KTheory.GrothendieckGroup.Filtration
public import Colib.CategoryTheory.Abelian.Devissage.Filtration
public import Colib.KTheory.Quillen.Map.Basic
public import Colib.CategoryTheory.Abelian.Devissage.QInclusion

/-!
# The exact inclusion in classical Quillen dévissage

Let `C` be abelian and let `P` be a property of its objects which contains zero
and is closed under subobjects, quotients, and finite products. The full
subcategory on `P` is genuinely abelian: its kernels and cokernels are created
by the inclusion. The inclusion is exact and therefore induces the actual
Q-construction functor and maps on Quillen K-groups.

The finite-filtration hypothesis says that every ambient object has an actual
finite admissible filtration whose successive quotients satisfy `P`. It implies
surjectivity of the inclusion on the algebraic Grothendieck groups.

There is deliberately no extension-closure hypothesis on `P`. Classical
Quillen dévissage allows the ambient category to contain nontrivial extensions
of objects of the smaller category. A homotopy equivalence and a comparison with homotopical `K₀`
  remain separate
theorems. Algebraic Grothendieck-group injectivity is proved in the subsequent
separate algebraic dévissage theorem.
-/
/-!
Implementation provenance: adapted from
`Quillen/Devissage/Setup.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Native Mathlib full subcategories, Colib exact structures,
restricted spans, actual realization maps and their universes are retained.
No extension-closure, uniform filtration bound, alternate K-model or Aglib import is added.
-/

@[expose] public section

open CategoryTheory.ExactCategory
open CategoryTheory.ObjectProperty





noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Abelian.Devissage

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C] (P : ObjectProperty C)

variable [P.ContainsZero] [P.IsClosedUnderSubobjects] [P.IsClosedUnderQuotients]
  [P.IsClosedUnderFiniteProducts]

/-- The homomorphism on the genuine zero-based Quillen K-groups. This definition
by itself does not assert that the homomorphism is an isomorphism. -/
def KMap (n : ℕ) :
    (abelianExactStructure P.FullSubcategory).K n →* (abelianExactStructure C).K n :=
  (exactInclusion P).KMap n

/-- The inclusion-induced map of algebraic Grothendieck groups. -/
def grothendieckMap :
    (abelianExactStructure P.FullSubcategory).GrothendieckGroup →+
      (abelianExactStructure C).GrothendieckGroup :=
  (exactInclusion P).grothendieckMap

@[simp]
lemma grothendieckMap_class (X : P.FullSubcategory) :
    grothendieckMap P ((abelianExactStructure P.FullSubcategory).grothendieckClass X) =
      (abelianExactStructure C).grothendieckClass X.obj :=
  (exactInclusion P).grothendieckMap_class X

/-- A finite filtration with factors in `P` puts the ambient object's class in
the image of the inclusion-induced algebraic Grothendieck-group map. -/
theorem class_mem_range {X : C} (F : (abelianExactStructure C).Filtration P X) :
    (abelianExactStructure C).grothendieckClass X ∈ (grothendieckMap P).range := by
  apply F.class_mem
  intro Y hY
  exact ⟨(abelianExactStructure P.FullSubcategory).grothendieckClass ⟨Y, hY⟩,
    grothendieckMap_class P ⟨Y, hY⟩⟩

/-- The filtration hypothesis proves surjectivity on algebraic Grothendieck
groups. This is not the homotopical dévissage theorem or the `K₀` comparison. -/
theorem grothendieckMap_surjective (h : FiltrationHypothesis P) :
    Function.Surjective (grothendieckMap P) := by
  apply AddMonoidHom.range_eq_top.mp
  apply CategoryTheory.ExactCategory.ExactStructure.grothendieckSubgroup_eq_top_of_classes
  intro X
  obtain ⟨F⟩ := h X
  exact class_mem_range P F

end CategoryTheory.Abelian.Devissage
