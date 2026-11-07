/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.DegreewiseSplitMono
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Degreewise split short exact sequences of cochain complexes

The actual splittings and short-exact/degreewise-split-mono implications retain
the original chain maps. No Waldhausen structure is needed for these results.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.ExactSequences`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CochainComplex


open CategoryTheory.ExactCategory


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe v u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A termwise retraction of the first map in a short exact sequence
extends to a full splitting of that sequence in each degree. -/
def degreewiseSplittingOfShortExact {S : ShortComplex (CochainComplex A ℤ)}
    (hS : S.ShortExact) (hf : degreewiseSplitMono S.f) (n : ℤ) :
    (S.map (eval A (ComplexShape.up ℤ) n)).Splitting := by
  let T := S.map (eval A (ComplexShape.up ℤ) n)
  have hT := (shortExact_iff_degreewise_shortExact S).1 hS n
  let : IsSplitMono T.f := hf n
  exact ShortComplex.Splitting.ofExactOfRetraction T hT.exact
    (retraction T.f) (IsSplitMono.id T.f) hT.epi_g

/-- Full degreewise splittings imply both actual short exactness and
termwise split-monomorphism of the first map. -/
theorem shortExact_and_degreewiseSplitMono_of_splittings
    {S : ShortComplex (CochainComplex A ℤ)}
    (h : ∀ n : ℤ, Nonempty (S.map (eval A (ComplexShape.up ℤ) n)).Splitting) :
    S.ShortExact ∧ degreewiseSplitMono S.f := by
  exact ⟨shortExact_of_degreewise_shortExact S (fun n ↦ (h n).some.shortExact),
    fun n ↦ (h n).some.isSplitMono_f⟩

end CochainComplex
