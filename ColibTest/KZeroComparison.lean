/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.KTheory.GrothendieckComparison.Injectivity

@[expose] public section

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

example : Function.Injective E.qGroupoidToKZero := E.qGroupoidToKZero_injective
example : Function.Bijective E.grothendieckToKZero := E.grothendieckToKZero_bijective

example : E.grothendieckKZeroEquiv.toMonoidHom = E.grothendieckToKZero := rfl

example (x : Multiplicative E.GrothendieckGroup) :
    E.grothendieckKZeroEquiv x = E.kZeroFundamentalGroupEquiv.symm
      (classifyingGroupoidCompletionMap E.QCategory E.qZero (E.grothendieckQGroupoidEquiv x)) :=
  (DFunLike.congr_fun E.grothendieckToKZero_factorization x).symm

example (X : C) :
    E.grothendieckKZeroEquiv (Multiplicative.ofAdd (E.grothendieckClass X)) =
      E.kZeroObjectClass X := E.grothendieckToKZero_class X

example (X : C) : E.grothendieckKZeroEquiv.symm (E.kZeroObjectClass X) =
    Multiplicative.ofAdd (E.grothendieckClass X) := by
  apply E.grothendieckKZeroEquiv.injective
  rw [MulEquiv.apply_symm_apply]
  exact (E.grothendieckToKZero_class X).symm

example : E.grothendieckKZeroEquiv
    (Multiplicative.ofAdd (E.grothendieckClass (0 : C))) = 1 := by
  rw [E.grothendieckKZeroEquiv_apply, E.grothendieckToKZero_class, E.kZeroObjectClass_zero]

example (a b : Multiplicative E.GrothendieckGroup)
    (h : E.grothendieckToKZero a = E.grothendieckToKZero b) : a = b :=
  E.grothendieckToKZero_injective h

example (x : E.K 0) : E.grothendieckToKZero (E.grothendieckKZeroEquiv.symm x) = x :=
  E.grothendieckKZeroEquiv.apply_symm_apply x

example (a b : Multiplicative E.GrothendieckGroup) :
    E.grothendieckKZeroEquiv (a * b) = E.grothendieckKZeroEquiv a * E.grothendieckKZeroEquiv b :=
  E.grothendieckKZeroEquiv.map_mul a b

end CategoryTheory.ExactCategory.ExactStructure
