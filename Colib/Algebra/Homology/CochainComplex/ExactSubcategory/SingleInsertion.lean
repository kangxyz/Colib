/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.FiniteTermEvaluation

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks

/-!
# Actual single-complex insertion in bounded termwise subcategories

The original single functor is additive and exact for the inherited structures.
Its factorization through each allowed finite term interval retains the actual
single complex, source terms and chain maps, with the original universe bounds.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.SingleInsertion`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u
namespace CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type (max u v)} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]
local instance globalEulerReduction_termPropertyProducts : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The original single complex as an actual bounded termwise-P complex. -/
def boundedTermsSingleFunctor (n : ℤ) : P.FullSubcategory ⥤ (boundedTerms P).FullSubcategory :=
  (boundedTerms P).lift (P.ι ⋙ single A (ComplexShape.up ℤ) n)
    (fun X ↦ boundedTerms_single_mem P n X.obj X.property)

omit [(abelianExactStructure A).IsExtensionClosed P] in
@[simp] theorem boundedTermsSingleFunctor_map (n : ℤ) {X Y : P.FullSubcategory} (f : X ⟶ Y) :
    ((boundedTermsSingleFunctor P n).map f).hom = (single A (ComplexShape.up ℤ) n).map f.hom := rfl

instance boundedTermsSingleFunctor_additive (n : ℤ) : (boundedTermsSingleFunctor P n).Additive :=
  inferInstanceAs (Functor.Additive ((boundedTerms P).lift _ _))

/-- Original single insertion preserves the actual inherited conflations. -/
def boundedTermsSingleExactFunctor (n : ℤ) :
    ExactFunctor (ExactSubcategory.exactStructure (abelianExactStructure A) P)
      (boundedTermsExactStructure P) where
  toFunctor := boundedTermsSingleFunctor P n
  map_conflation S hS := singleTerm_shortExact (S.map P.ι) hS n

omit [(abelianExactStructure A).IsExtensionClosed P] in
/-- Any allowed stage insertion is the original global single functor after inclusion. -/
theorem finiteTermSingle_comp_inclusion (a b n : ℤ) (ha : a ≤ n) (hb : n ≤ b) :
    finiteTermSingle P a b n ha hb ⋙ (fixedTermsBounds P a b).ι = boundedTermsSingleFunctor P n
      := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end CochainComplex
