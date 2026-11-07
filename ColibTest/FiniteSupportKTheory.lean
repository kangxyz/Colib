/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.FiniteSupport.Decomposition

/-! # Original coordinates and upper-universe finite-support regressions -/

@[expose] public noncomputable section

namespace ColibTest.FiniteSupportKTheory

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory CategoryTheory.Pi
open scoped DirectSum

attribute [local instance] Abelian.hasFiniteBiproducts Classical.propDecidable

universe u
variable {I : Type u} (C : I → Type (u + 1))
  [∀ i, Category.{u + 1} (C i)] [∀ i, Abelian (C i)]

-- The actual stage equivalence also covers arbitrary off-support zero objects.
example (s : Finset I) : FiniteStage C s ≌ (∀ i : s, C i.1) :=
  stageProductEquivalence C s

-- The full decomposition retains a genuinely smaller index universe.
example (n : ℕ) : Additive ((finiteCategoryExactStructure C).K (n + 1)) ≃+
    ⨁ i, Additive ((abelianExactStructure (C i)).K (n + 1)) :=
  FiniteSupport.decompositionKEquiv.{u, u + 1} C n

example (n : ℕ) (a : Additive ((finiteCategoryExactStructure C).K (n + 1))) (i : I) :
    FiniteSupport.decompositionKEquiv.{u, u + 1} C n a i =
      Additive.ofMul ((finiteCategoryEvaluation C i).KMap (n + 1) a.toMul) := rfl

example (i : I) (a : Additive ((abelianExactStructure (C i)).K 2)) :
    (FiniteSupport.K2DecompositionEquiv.{u, u + 1} C).symm (DirectSum.of _ i a) =
      Additive.ofMul ((singletonExactInclusion C i).KMap 2 a.toMul) :=
  FiniteSupport.decompositionKEquiv_symm_of.{u, u + 1} C 1 i a

example (M : FiniteStage C ∅) : IsZero M := emptyStage_isZero C M

example (n : ℕ) (a : (finiteCategoryExactStructure C).K n) :
    ∃ s : Finset I, ∃ b : (stageExactStructure C s).K n,
      (stageExactToFiniteFamily C s).KMap n b = a :=
  FiniteSupport.stageKMap_jointlySurjective.{u, u + 1} C n a

end ColibTest.FiniteSupportKTheory
