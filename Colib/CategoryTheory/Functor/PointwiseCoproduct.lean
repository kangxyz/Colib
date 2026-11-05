/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-! # Pointwise binary coproducts and their canonical inclusions

Implementation provenance: `Quillen/Aglib/CategoryTheory/Functor/PointwiseCoproduct.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable [HasBinaryCoproducts D]

/-- Pointwise binary coproduct of two functors, in quotient/subobject order. -/
def sumFunctor (H F : C ⥤ D) : C ⥤ D where
  obj X := H.obj X ⨿ F.obj X
  map f := coprod.map (H.map f) (F.map f)
  map_id _ := by apply coprod.hom_ext <;> simp
  map_comp _ _ := by apply coprod.hom_ext <;> simp [Category.assoc]

/-- First summand inclusion. -/
def sumInl (H F : C ⥤ D) : H ⟶ sumFunctor H F where
  app _ := coprod.inl
  naturality _ _ _ := by simp [sumFunctor]

/-- Second summand inclusion. -/
def sumInr (H F : C ⥤ D) : F ⟶ sumFunctor H F where
  app _ := coprod.inr
  naturality _ _ _ := by simp [sumFunctor]

/-- The actual split endpoint, quotient at the first object and subobject
at the second object. -/
def splitEndpoint (H F : C ⥤ D) : C × C ⥤ D where
  obj X := H.obj X.1 ⨿ F.obj X.2
  map f := coprod.map (H.map f.1) (F.map f.2)
  map_id X := by apply coprod.hom_ext <;> simp
  map_comp f g := by apply coprod.hom_ext <;> simp [Category.assoc]

section Coproduct
variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C]
/-- The actual binary coproduct functor. -/
def coproductFunctor : C × C ⥤ C :=
  sumFunctor (CategoryTheory.Prod.fst C C) (CategoryTheory.Prod.snd C C)

end Coproduct
section Transformation
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable [HasBinaryCoproducts D]
variable {H H' F F' : C ⥤ D} (ηF : F ⟶ F') (ηH : H ⟶ H')
/-- The actual quotient-first pair-sum transformation. -/
def splitEndpointTransformation : splitEndpoint H F ⟶ splitEndpoint H' F' where
  app X := coprod.map (ηH.app X.1) (ηF.app X.2)
  naturality X Y f := by
    apply coprod.hom_ext <;>
      simp [splitEndpoint, ηH.naturality, ηF.naturality]

end Transformation
end CategoryTheory
