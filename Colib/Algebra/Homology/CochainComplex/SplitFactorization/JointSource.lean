/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.JointSubcategory
public import Colib.CategoryTheory.Functor.PointwiseCoproduct

/-!
# Ordinary endpoint coproduct functors in full complex subcategories

The actual biproduct of the two arrow endpoints is functorial, with its two
natural inclusions, coproduct universal property, and original sum comparison.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.JointSource`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v

namespace CochainComplex.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  (P : ObjectProperty (CochainComplex A ℤ))
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]

/-- The actual ambient endpoint biproduct, functorial by the literal biproduct map. -/
def subcategoryJointSourceFunctor : Arrow P.FullSubcategory ⥤ P.FullSubcategory where
  obj f := subcategoryJointSource P f
  map α := P.homMk (biprod.map α.left.hom α.right.hom)
  map_id f := by apply ObjectProperty.hom_ext; apply biprod.hom_ext <;> simp
  map_comp α β := by apply ObjectProperty.hom_ext; apply biprod.hom_ext <;> simp

@[simp] theorem subcategoryJointSourceFunctor_obj (f : Arrow P.FullSubcategory) :
    (subcategoryJointSourceFunctor P).obj f = subcategoryJointSource P f := rfl

@[simp] theorem subcategoryJointSourceFunctor_map {f g : Arrow P.FullSubcategory} (α : f ⟶ g) :
    ((subcategoryJointSourceFunctor P).map α).hom = biprod.map α.left.hom α.right.hom := rfl

/-- The first actual endpoint inclusion. -/
def subcategoryJointSourceInl : Arrow.leftFunc ⟶ subcategoryJointSourceFunctor P where
  app _ := P.homMk biprod.inl
  naturality f g α := by apply ObjectProperty.hom_ext; simp [subcategoryJointSourceFunctor]

/-- The second actual endpoint inclusion. -/
def subcategoryJointSourceInr : Arrow.rightFunc ⟶ subcategoryJointSourceFunctor P where
  app _ := P.homMk biprod.inr
  naturality f g α := by apply ObjectProperty.hom_ext; simp [subcategoryJointSourceFunctor]

/-- The ambient biproduct is an actual coproduct in the full subcategory. -/
def subcategoryJointSourceCofanIsColimit (f : Arrow P.FullSubcategory) :
    IsColimit (BinaryCofan.mk ((subcategoryJointSourceInl P).app f)
      ((subcategoryJointSourceInr P).app f)) := by
  refine BinaryCofan.IsColimit.mk _ (fun a b ↦ P.homMk (biprod.desc a.hom b.hom)) ?_ ?_ ?_
  · intro T a b
    apply ObjectProperty.hom_ext
    exact biprod.inl_desc _ _
  · intro T a b
    apply ObjectProperty.hom_ext
    exact biprod.inr_desc _ _
  · intro T a b m hm hn
    apply ObjectProperty.hom_ext
    apply biprod.hom_ext'
    · simpa [subcategoryJointSourceInl] using congrArg (fun k ↦ k.hom) hm
    · simpa [subcategoryJointSourceInr] using congrArg (fun k ↦ k.hom) hn

variable [P.IsClosedUnderFiniteProducts]

/-- The canonical chosen-coproduct to actual ambient biproduct isomorphism. -/
def subcategoryJointSourceCoproductIso (f : Arrow P.FullSubcategory) :
    f.left ⨿ f.right ≅ subcategoryJointSource P f :=
  (coprodIsCoprod _ _).coconePointUniqueUpToIso (subcategoryJointSourceCofanIsColimit P f)

@[reassoc (attr := simp)] theorem subcategoryJointSourceCoproductIso_inl (f : Arrow
    P.FullSubcategory) :
    coprod.inl ≫ (subcategoryJointSourceCoproductIso P f).hom = (subcategoryJointSourceInl
      P).app f :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod f.left f.right)
    (subcategoryJointSourceCofanIsColimit P f) (Discrete.mk WalkingPair.left)

@[reassoc (attr := simp)] theorem subcategoryJointSourceCoproductIso_inr (f : Arrow
    P.FullSubcategory) :
    coprod.inr ≫ (subcategoryJointSourceCoproductIso P f).hom = (subcategoryJointSourceInr
      P).app f :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coprodIsCoprod f.left f.right)
    (subcategoryJointSourceCofanIsColimit P f) (Discrete.mk WalkingPair.right)

/-- The actual ambient biproduct functor is naturally the sum of the actual evaluations. -/
def subcategoryJointSourceSumIso :
    CategoryTheory.sumFunctor Arrow.leftFunc Arrow.rightFunc ≅ subcategoryJointSourceFunctor P :=
  NatIso.ofComponents (subcategoryJointSourceCoproductIso P) (by
    intro X Y f
    apply coprod.hom_ext
    · simp only [CategoryTheory.sumFunctor, coprod.inl_map_assoc]
      have h := (subcategoryJointSourceInl P).naturality f
      rw [← subcategoryJointSourceCoproductIso_inl P X,
        ← subcategoryJointSourceCoproductIso_inl P Y] at h
      simpa only [Category.assoc] using! h
    · simp only [CategoryTheory.sumFunctor, coprod.inr_map_assoc]
      have h := (subcategoryJointSourceInr P).naturality f
      rw [← subcategoryJointSourceCoproductIso_inr P X,
        ← subcategoryJointSourceCoproductIso_inr P Y] at h
      simpa only [Category.assoc] using! h)

end CochainComplex.SplitFactorization
