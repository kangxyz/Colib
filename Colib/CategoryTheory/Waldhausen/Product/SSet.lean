/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Product.Structure
public import Colib.KTheory.Waldhausen.ZeroFunctor

/-! # The actual S-construction of a product Waldhausen category

Pairing genuine quotient grids is inverse to the two original projection
S-maps. The simplicial isomorphism retains the chosen zero vertex exactly.
-/
/-! Source: `Quillen/Waldhausen/Product/SSet.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps and universes are retained.
The S-product isomorphism is not a normalized or strict S-model comparison. -/
@[expose] public section

open CategoryTheory.Waldhausen.Product

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial
universe u v

namespace CategoryTheory.Waldhausen.Product
open CategoryTheory.Waldhausen.Product
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D)

/-- Actual quotient grids pair componentwise, including their pushouts. -/
theorem isSimplex_pair {n : SimplexCategory} {F : Grid n ⥤ C} {G : Grid n ⥤ D}
    (hF : IsSimplex V.cof V.weq F) (hG : IsSimplex W.cof W.weq G) :
    IsSimplex (productStructure V W).cof (productStructure V W).weq (F.prod' G) where
  zero t i := product_isZero (hF.zero t i) (hG.zero t i)
  cofibration t i j k hij hjk := ⟨hF.cofibration t i j k hij hjk, hG.cofibration t i j k hij hjk⟩
  quotient t i j k hij hjk := product_isPushout _ _ _ _
    (hF.quotient t i j k hij hjk) (hG.quotient t i j k hij hjk)
  weak s t i j hst hij := ⟨hF.weak s t i j hst hij, hG.weak s t i j hst hij⟩

/-- Pair the two actual S-grids. -/
def pair : sSet V.cof V.weq ⊗ sSet W.cof W.weq ⟶
    sSet (productStructure V W).cof (productStructure V W).weq where
  app _ := ↾fun p ↦ ⟨p.1.1.prod' p.2.1, isSimplex_pair V W p.1.2 p.2.2⟩
  naturality _ _ _ := by ext p; rfl

/-- The canonical map uses the two unchanged projection S-maps. -/
def comparison : sSet (productStructure V W).cof (productStructure V W).weq ⟶
    sSet V.cof V.weq ⊗ sSet W.cof W.weq :=
  CartesianMonoidalCategory.lift (sSetMap (fst_exact V W)) (sSetMap (snd_exact V W))

@[simp] theorem comparison_pair : comparison V W ≫ pair V W = 𝟙 _ := by
  ext n F
  rfl

@[simp] theorem pair_comparison : pair V W ≫ comparison V W = 𝟙 _ := by
  ext n F <;> rfl

/-- A strict identification with the actual simplicial product. -/
def sSetIso : sSet (productStructure V W).cof (productStructure V W).weq ≅
    sSet V.cof V.weq ⊗ sSet W.cof W.weq where
  hom := comparison V W
  inv := pair V W
  hom_inv_id := comparison_pair V W
  inv_hom_id := pair_comparison V W

@[reassoc (attr := simp)] theorem comparison_fst :
    comparison V W ≫ CartesianMonoidalCategory.fst _ _ = sSetMap (fst_exact V W) := by
  simp [comparison]

@[reassoc (attr := simp)] theorem comparison_snd :
    comparison V W ≫ CartesianMonoidalCategory.snd _ _ = sSetMap (snd_exact V W) := by
  simp [comparison]

/-- The product comparison preserves zero in the canonical product simplex type. -/
@[simp] theorem comparison_app_hom_zero (n : SimplexCategoryᵒᵖ) :
    TypeCat.Hom.hom (Y := (sSet V.cof V.weq).obj n × (sSet W.cof W.weq).obj n)
      ((comparison V W).app n) (zeroSimplex (productStructure V W).cof
      (productStructure V W).weq (V.zero, W.zero) (productStructure V W).isZero n) =
      (zeroSimplex V.cof V.weq V.zero V.isZero n,
        zeroSimplex W.cof W.weq W.zero W.isZero n) := rfl

end CategoryTheory.Waldhausen.Product
