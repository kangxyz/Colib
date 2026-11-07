/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.CompletionInjectivity
public import Colib.KTheory.GrothendieckComparison.Surjectivity

/-!
# Injectivity of the canonical Grothendieck-to-Quillen K-zero comparison

The topological completion comparison is injective on the original based loop
map. The already proved exact factorization therefore gives injectivity, and
then bijectivity, of the existing canonical Grothendieck comparison. No new
model for either K-zero and no replacement comparison map is introduced.
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Distinct completed Q-edge loops remain distinct in genuine homotopical K-zero. -/
theorem qGroupoidToKZero_injective : Function.Injective E.qGroupoidToKZero :=
  E.kZeroFundamentalGroupEquiv.symm.injective.comp
    (classifyingGroupoidCompletionMap_injective E.QCategory E.qZero)

/-- The existing canonical Grothendieck comparison is injective on actual K-zero. -/
theorem grothendieckToKZero_injective : Function.Injective E.grothendieckToKZero :=
  E.grothendieckToKZero_injective_iff.mpr E.qGroupoidToKZero_injective

/-- The canonical Grothendieck comparison is bijective onto actual Quillen K-zero. -/
theorem grothendieckToKZero_bijective : Function.Bijective E.grothendieckToKZero :=
  ⟨E.grothendieckToKZero_injective, E.grothendieckToKZero_surjective⟩

/-- The existing comparison, equipped with its proved inverse on group elements. -/
def grothendieckKZeroEquiv : Multiplicative E.GrothendieckGroup ≃* E.K 0 :=
  MulEquiv.ofBijective E.grothendieckToKZero E.grothendieckToKZero_bijective

@[simp]
theorem grothendieckKZeroEquiv_apply (x : Multiplicative E.GrothendieckGroup) :
    E.grothendieckKZeroEquiv x = E.grothendieckToKZero x := rfl

end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0240",
  colib_ref "WeibelKBook" "IV, Proposition 6.2 and proof, equations (6.2.1)-(6.2.2), page 54"
    "adaptation"
    "The canonical Grothendieck comparison with actual homotopical Quillen K-zero,
      with its original object classes"]
  CategoryTheory.ExactCategory.ExactStructure.qGroupoidToKZero_injective
  CategoryTheory.ExactCategory.ExactStructure.grothendieckToKZero_injective
  CategoryTheory.ExactCategory.ExactStructure.grothendieckToKZero_bijective
  CategoryTheory.ExactCategory.ExactStructure.grothendieckKZeroEquiv

attribute [colib_ref "Quillen1973"
    "Section 2, Theorem 1 and proof, pp. 102-103" "adaptation"
    "The canonical Grothendieck-group identification with fundamental-group K-zero"]
  CategoryTheory.ExactCategory.ExactStructure.grothendieckToKZero_bijective
  CategoryTheory.ExactCategory.ExactStructure.grothendieckKZeroEquiv
