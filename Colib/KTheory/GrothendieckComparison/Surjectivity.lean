/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.KTheory.GrothendieckComparison.Factorization
public import Colib.Topology.ClassifyingSpace.CompletionSurjectivity

/-!
# Surjectivity onto the genuine homotopical K₀

The original completed-loop comparison is surjective at the original zero
vertex. Its exact factorization through the algebraic Grothendieck equivalence
therefore proves surjectivity of the existing `grothendieckToKZero` map onto all
of the actual homotopy group. No injectivity or comparison equivalence is asserted.
-/
@[expose] public noncomputable section

universe u v
open CategoryTheory
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Every genuine based K₀ class is represented by a completed Q-edge loop. -/
theorem qGroupoidToKZero_surjective : Function.Surjective E.qGroupoidToKZero :=
  E.kZeroFundamentalGroupEquiv.symm.surjective.comp
    (classifyingGroupoidCompletionMap_surjective E.QCategory E.qZero)

/-- The existing canonical Grothendieck comparison reaches every element of
actual homotopical Quillen K₀, not only its object-generated subgroup. -/
theorem grothendieckToKZero_surjective : Function.Surjective E.grothendieckToKZero :=
  E.grothendieckToKZero_surjective_iff.mpr E.qGroupoidToKZero_surjective

end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0162",
  colib_ref "WeibelKBook" "IV, Proposition 6.2 and proof, equations (6.2.1)-(6.2.2), page 54"
    "adaptation"
    "Only surjectivity of the canonical Grothendieck comparison onto homotopical K-zero"]
  CategoryTheory.ExactCategory.ExactStructure.grothendieckToKZero_factorization
  CategoryTheory.ExactCategory.ExactStructure.qGroupoidToKZero_surjective
  CategoryTheory.ExactCategory.ExactStructure.grothendieckToKZero_surjective
