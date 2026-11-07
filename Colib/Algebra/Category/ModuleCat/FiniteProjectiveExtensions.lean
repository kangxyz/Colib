/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveMonoidal
public import Colib.CategoryTheory.ExactCategory.Extensions.Product
public import Colib.CategoryTheory.ExactCategory.Extensions.Pullback
public import Colib.CategoryTheory.ExactCategory.Isomorphisms

/-!
Implementation provenance:
`Quillen/Aglib/Algebra/Category/ModuleCat/FiniteProjectiveExtensions.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Original finite-projective extension and coproduct maps

Middle-term maps detect arrows in the extension groupoid. Actual kernels
retain their finite-projective core objects; pullback/product maps keep
their original projections, and an unchanged coproduct summand preserves
admissible monomorphisms. Rings need not be commutative.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
attribute [local instance] directSumMonoidal directSumSymmetric

/-- Equality of extension isomorphisms is detected on their middle-term maps. -/
theorem extensionFiber_hom_ext {C : Category.{u, u} R}
    {p q : (exactStructure R).ExtensionFiber C} {f g : p ⟶ q}
    (h : f.iso.hom.hom.left = g.iso.hom.hom.left) : f = g := by
  apply Core.hom_ext
  apply ObjectProperty.hom_ext
  exact Over.OverMorphism.ext h

/-- The kernel, with the finite-projective structure provided by the original
exact category, is an actual acting object. -/
def extensionKernelIsoObject {C : Category.{u, u} R}
    (p : (exactStructure R).ExtensionFiber C) : IsoCategory R :=
  ⟨((exactStructure R).extensionKernelData p.of).obj⟩

/-- Adding an unchanged first summand preserves admissible monomorphisms. -/
theorem inflation_coprod_map_id {A B : Category.{u, u} R} (S : Category.{u, u} R)
    (f : A ⟶ B) (hf : (exactStructure R).inflation f) :
    (exactStructure R).inflation (coprod.map (𝟙 S) f) := by
  have sq : IsPushout (coprod.inr : A ⟶ S ⨿ A) f
      (coprod.map (𝟙 S) f) (coprod.inr : B ⟶ S ⨿ B) := by
    refine IsPushout.mk' (by simp) ?_ ?_
    · intro T a b hab hfb
      apply coprod.hom_ext
      · simpa using congrArg (fun m => coprod.inl ≫ m) hab
      · exact hfb
    · intro T a b hab
      refine ⟨coprod.desc (coprod.inl ≫ a) b, ?_, by simp⟩
      apply coprod.hom_ext
      · simp
      · simpa using hab.symm
  exact (exactStructure R).inflation.of_isPushout sq hf

/-- The first projection of a product map is the original first map. -/
@[reassoc (attr := simp)]
theorem extensionFiberProduct_map_fst {C : Category.{u, u} R}
    {p p' q q' : (exactStructure R).ExtensionFiber C} (f : p ⟶ p') (g : q ⟶ q') :
    (((exactStructure R).extensionFiberProduct C).map (Prod.mkHom f g)).iso.hom.hom.left ≫
      pullback.fst p'.of.obj.hom q'.of.obj.hom =
    pullback.fst p.of.obj.hom q.of.obj.hom ≫ f.iso.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- The second projection of a product map is the original second map. -/
@[reassoc (attr := simp)]
theorem extensionFiberProduct_map_snd {C : Category.{u, u} R}
    {p p' q q' : (exactStructure R).ExtensionFiber C} (f : p ⟶ p') (g : q ⟶ q') :
    (((exactStructure R).extensionFiberProduct C).map (Prod.mkHom f g)).iso.hom.hom.left ≫
      pullback.snd p'.of.obj.hom q'.of.obj.hom =
    pullback.snd p.of.obj.hom q.of.obj.hom ≫ g.iso.hom.hom.left :=
  pullback.lift_snd _ _ _

local instance pullbackLinearExists {X Y : Category.{u, u} R} (f : X ⟶ Y)
    (p : (exactStructure R).ExtensionOver Y) : HasPullback p.obj.hom f :=
  (exactStructure R).deflation.hasPullback f p.property

/-- The genuine pullback functor preserves the first projection square. -/
@[reassoc (attr := simp)]
theorem extensionFiberPullback_map_fst {X Y : Category.{u, u} R} (f : X ⟶ Y)
    {p q : (exactStructure R).ExtensionFiber Y} (g : p ⟶ q) :
    (((exactStructure R).extensionFiberPullback f).map g).iso.hom.hom.left ≫
      pullback.fst q.of.obj.hom f = pullback.fst p.of.obj.hom f ≫ g.iso.hom.hom.left :=
  pullback.lift_fst _ _ _

/-- The genuine pullback functor fixes the projection to the new quotient. -/
@[reassoc (attr := simp)]
theorem extensionFiberPullback_map_snd {X Y : Category.{u, u} R} (f : X ⟶ Y)
    {p q : (exactStructure R).ExtensionFiber Y} (g : p ⟶ q) :
    (((exactStructure R).extensionFiberPullback f).map g).iso.hom.hom.left ≫
      pullback.snd q.of.obj.hom f = pullback.snd p.of.obj.hom f :=
  pullback.lift_snd _ _ _

end ModuleCat.FiniteProjective
