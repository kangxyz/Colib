/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.QuotientExact

/-!
# Actual smart-truncation inclusion and quotient transformations

The original canonical truncation and cokernel maps form a natural short
complex in the bounded acyclic category. Every actual map of acyclic complexes
is a quasi-isomorphism. No Waldhausen sequence structure is constructed here.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationTransformations`
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
variable {A : Type u} [Category.{v} A] [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The canonical inclusion, as an actual natural transformation. -/
def boundedAcyclicTruncationInclusion (n : ℤ) :
    boundedAcyclicTruncLEFunctor P n ⟶ 𝟭 (boundedAcyclic P).FullSubcategory where
  app K := ((acyclicTruncationSequenceFunctor P n).obj K).f
  naturality _ _ f := ((acyclicTruncationSequenceFunctor P n).map f).comm₁₂

/-- The canonical quotient projection, as an actual natural transformation. -/
def boundedAcyclicTruncationProjection (n : ℤ) :
    𝟭 (boundedAcyclic P).FullSubcategory ⟶ boundedAcyclicQuotientFunctor P n where
  app K := ((acyclicTruncationSequenceFunctor P n).obj K).g
  naturality _ _ f := ((acyclicTruncationSequenceFunctor P n).map f).comm₂₃

@[reassoc]
theorem boundedAcyclicTruncation_comp_zero (n : ℤ) :
    boundedAcyclicTruncationInclusion P n ≫ boundedAcyclicTruncationProjection P n = 0 := by
  apply NatTrans.ext
  funext K
  exact ((acyclicTruncationSequenceFunctor P n).obj K).zero

variable [(abelianExactStructure A).IsExtensionClosed P]

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsKernelClosed P]
    [(abelianExactStructure A).IsExtensionClosed P] in
/-- Every actual map of acyclic complexes is a genuine quasi-isomorphism. -/
theorem boundedAcyclic_map_quasiIso {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    QuasiIso f.hom := by
  rw [quasiIso_iff]
  intro i
  exact (quasiIsoAt_iff_exactAt' f.hom i (L.property.2.2 i)).2 (K.property.2.2 i)

end CochainComplex
