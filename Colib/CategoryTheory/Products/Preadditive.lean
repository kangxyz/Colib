/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Products.Limits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Preadditive binary product categories

The native binary product has componentwise addition and finite biproducts.
Adapted from `Quillen/Aglib/CategoryTheory/ExactCategory/Product.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section

open CategoryTheory.Limits
universe v₁ v₂ u₁ u₂
namespace CategoryTheory.Prod
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

variable [Preadditive C] [Preadditive D]

instance preadditive : Preadditive (C × D) where
  homGroup P Q := inferInstanceAs (AddCommGroup ((P.1 ⟶ Q.1) × (P.2 ⟶ Q.2)))
  add_comp _ _ _ _ _ _ := _root_.Prod.ext
    (Preadditive.add_comp _ _ _ _ _ _) (Preadditive.add_comp _ _ _ _ _ _)
  comp_add _ _ _ _ _ _ := _root_.Prod.ext
    (Preadditive.comp_add _ _ _ _ _ _) (Preadditive.comp_add _ _ _ _ _ _)

instance fst_additive : (fst C D).Additive where
  map_add := rfl

instance snd_additive : (snd C D).Additive where
  map_add := rfl

instance hasFiniteBiproducts [HasFiniteBiproducts C] [HasFiniteBiproducts D] :
    HasFiniteBiproducts (C × D) := by
  have : HasFiniteProducts (C × D) := ⟨fun _ => inferInstance⟩
  exact HasFiniteBiproducts.of_hasFiniteProducts

end CategoryTheory.Prod
