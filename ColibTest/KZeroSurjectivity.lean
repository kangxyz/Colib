/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.KTheory.GrothendieckComparison.Surjectivity

@[expose] public noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

example (a : E.qGroupoidZeroGroup) :
    E.qGroupoidToKZero a = E.kZeroFundamentalGroupEquiv.symm
      (classifyingGroupoidCompletionMap E.QCategory E.qZero a) := rfl

example : E.kBasepoint = classifyingSpacePoint E.qZero := rfl

example (X : C) :
    E.qGroupoidToKZero (E.qObjectClass E.toQGroupoid X) = E.kZeroObjectClass X :=
  E.qGroupoidToKZero_objectClass X

example (a : Multiplicative E.GrothendieckGroup) :
    E.qGroupoidToKZero (E.grothendieckQGroupoidEquiv a) = E.grothendieckToKZero a :=
  DFunLike.congr_fun E.grothendieckToKZero_factorization a

example (a b : E.qGroupoidZeroGroup) :
    E.qGroupoidToKZero (a * b) = E.qGroupoidToKZero a * E.qGroupoidToKZero b :=
  E.qGroupoidToKZero.map_mul a b

example : E.grothendieckToKZero (Multiplicative.ofAdd (E.grothendieckClass (0 : C))) = 1 := by
  rw [E.grothendieckToKZero_class, E.kZeroObjectClass_zero]

example : Function.Surjective E.qGroupoidToKZero := E.qGroupoidToKZero_surjective
example (x : E.K 0) : ∃ a, E.grothendieckToKZero a = x :=
  E.grothendieckToKZero_surjective x

example : Function.Injective E.grothendieckToKZero ↔ Function.Injective E.qGroupoidToKZero :=
  E.grothendieckToKZero_injective_iff

end CategoryTheory.ExactCategory.ExactStructure

#print axioms CategoryTheory.ExactCategory.ExactStructure.qGroupoidToKZero_objectClass
#print axioms CategoryTheory.ExactCategory.ExactStructure.grothendieckToKZero_factorization
#print axioms CategoryTheory.ExactCategory.ExactStructure.qGroupoidToKZero_surjective
#print axioms CategoryTheory.ExactCategory.ExactStructure.grothendieckToKZero_surjective
#print axioms CategoryTheory.ExactCategory.ExactStructure.qGroupoidToKZero
#print axioms CategoryTheory.ExactCategory.ExactStructure.grothendieckToKZero_surjective_iff

#print axioms CategoryTheory.ExactCategory.ExactStructure.grothendieckToKZero_injective_iff
