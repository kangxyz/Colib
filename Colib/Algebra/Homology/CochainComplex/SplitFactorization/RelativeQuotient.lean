/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.RelativeComplex

/-!
# The actual quotient of a relative endpoint map

For a map of short complexes, the cokernel of the map on quotient objects
is also the cokernel of the relative middle map. The proof uses the actual
cokernel universal properties and does not assume closure of an object
subcategory under arbitrary quotients.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.RelativeQuotient`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
  {S T : ShortComplex C} (φ : S ⟶ T) [Epi S.g]
  (hT : IsColimit (CokernelCofork.ofπ T.g T.zero))
  {P Q : C} {g : S.X₂ ⟶ P} {j : T.X₁ ⟶ P}
  (k : P ⟶ T.X₂) (hg : g ≫ k = φ.τ₂) (hj : j ≫ k = T.f)
  (p : T.X₃ ⟶ Q) (hp : φ.τ₃ ≫ p = 0)
  (hc : IsColimit (CokernelCofork.ofπ p hp))
  (hk : k ≫ T.g ≫ p = 0)

/-- The displayed composite gives the actual relative cokernel universal property.
No pushout hypothesis is needed once the displayed relative maps commute. -/
def relativeMiddleCokernelIsColimit : IsColimit (CokernelCofork.ofπ (T.g ≫ p) hk) := by
  let first {W : C} (a : T.X₂ ⟶ W) (ha : k ≫ a = 0) : T.X₃ ⟶ W :=
    hT.desc (CokernelCofork.ofπ a (by rw [← hj, Category.assoc, ha, comp_zero]))
  have first_fac {W : C} (a : T.X₂ ⟶ W) (ha : k ≫ a = 0) :
      T.g ≫ first a ha = a := hT.fac _ WalkingParallelPair.one
  have first_zero {W : C} (a : T.X₂ ⟶ W) (ha : k ≫ a = 0) :
      φ.τ₃ ≫ first a ha = 0 := by
    apply (cancel_epi S.g).1
    rw [← Category.assoc, ← φ.comm₂₃, Category.assoc, first_fac a ha,
      ← hg, Category.assoc, ha, comp_zero, comp_zero]
  have second_fac {W : C} (a : T.X₂ ⟶ W) (ha : k ≫ a = 0) :
      p ≫ hc.desc (CokernelCofork.ofπ (first a ha) (first_zero a ha)) = first a ha :=
    hc.fac _ WalkingParallelPair.one
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun a ha ↦ hc.desc (CokernelCofork.ofπ (first a ha) (first_zero a ha))) ?_ ?_
  · intro W a ha
    rw [Category.assoc, second_fac a ha, first_fac a ha]
  · intro W a ha m hm
    apply Cofork.IsColimit.hom_ext hc
    apply Cofork.IsColimit.hom_ext hT
    change T.g ≫ p ≫ m = T.g ≫ p ≫
      hc.desc (CokernelCofork.ofπ (first a ha) (first_zero a ha))
    rw [second_fac a ha, first_fac a ha]
    simpa only [Category.assoc] using hm

end CochainComplex
