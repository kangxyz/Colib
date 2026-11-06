/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Resolution.Finite
public import Colib.CategoryTheory.ExactCategory.Subcategory
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Data.Int.Init
public import Colib.Algebra.Homology.CochainComplex.Cycles

/-!
# Actual cycle sequences and kernel-closed subcategories

For an upper-bounded acyclic cochain complex with all terms in a replete
kernel-closed full subcategory of an abelian category, all cycle objects
belong to that subcategory. The actual maps from cycles into a term and
from that term onto the next cycles form a short exact sequence.

This is the algebraic cycle-closure input used by the acyclic truncation
induction in Thomason–Trobaugh 1.11.7–1.11.8. No K-theory comparison,
additivity, or localization conclusion is assumed or asserted.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.AcyclicCycles`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

attribute [local instance] Abelian.hasFiniteBiproducts

variable (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]
  (K : CochainComplex A ℤ) (hterms : ∀ n, P (K.X n))
  (hK : K.Acyclic) (b : ℤ) (hb : ∀ n, b < n → IsZero (K.X n))

section FullSubcategory

variable [P.ContainsZero] [(abelianExactStructure A).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- The cycle sequence as an actual short complex in the full subcategory,
retaining the original ambient cycle and differential maps. -/
def subcategoryCycleSequence (n : ℤ) : ShortComplex P.FullSubcategory :=
  ShortComplex.mk
    (P.homMk (K.iCycles n) : (⟨K.cycles n, _root_.CochainComplex.cycles_mem P K hterms hK b hb
      n⟩ : P.FullSubcategory) ⟶
      ⟨K.X n, hterms n⟩)
    (P.homMk (K.toCycles n (n + 1)) : (⟨K.X n, hterms n⟩ : P.FullSubcategory) ⟶
      ⟨K.cycles (n + 1), _root_.CochainComplex.cycles_mem P K hterms hK b hb (n + 1)⟩)
    (ObjectProperty.hom_ext _ (_root_.CochainComplex.iCycles_toCycles K n))

/-- The lifted cycle sequence is a genuine conflation in the inherited
exact structure, not merely a relation in a derived category. -/
theorem subcategoryCycleSequence_conflation (n : ℤ) :
    (ExactSubcategory.exactStructure (abelianExactStructure A) P).conflation
      (subcategoryCycleSequence P K hterms hK b hb n) :=
  _root_.CochainComplex.cycleSequence_shortExact K n (hK (n + 1))

end FullSubcategory

end CochainComplex
