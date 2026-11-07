/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.MappingCone.Identity
public import Colib.CategoryTheory.Limits.BiproductPushout
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Actual pushout preservation of the complex cylinder functor

The identity cone is termwise the sum of the two neighboring evaluations.
This gives preservation of every displayed pushout, and then the original
middle functor preserves every componentwise pushout square of arrows.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.Pushout`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CochainComplex








noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
universe u v
namespace CochainComplex.SplitFactorization
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The original cylinder middle functor preserves actual componentwise
pushouts of arrow squares, with no cofibration or weak-equivalence assumption. -/
theorem middleFunctor_map_isPushout
    {K L M N : Arrow (CochainComplex A ℤ)} {f : K ⟶ L} {g : K ⟶ M}
    {i : L ⟶ N} {j : M ⟶ N}
    (hL : IsPushout f.left g.left i.left j.left)
    (hR : IsPushout f.right g.right i.right j.right) :
    IsPushout (middleFunctor.map f) (middleFunctor.map g)
      (middleFunctor.map i) (middleFunctor.map j) :=
  CategoryTheory.Limits.IsPushout.biprod_map (identityConeFunctor_map_isPushout hL) hR

end CochainComplex.SplitFactorization
