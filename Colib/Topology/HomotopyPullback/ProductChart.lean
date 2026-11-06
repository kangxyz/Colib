/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.RetractionBaseChange

/-! Actual strict pullbacks in a product chart. The inverse is constructed
from the chart homeomorphism; no quotient base-change assertion is used. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyPullback/ProductChart.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology

/-- Covering-homotopy lifting is unchanged by an actual homeomorphism of
the base, with the specified projection map retained exactly. -/
theorem HomotopyLiftingProperty.of_targetHomeomorph
    {E B C : Type u} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace C]
    {p : C(E, B)} (hp : HomotopyLiftingProperty p) (q : C(E, C)) (e : C ≃ₜ B)
    (he : (e : C(C, B)).comp q = p) : HomotopyLiftingProperty q := by
  intro A _ a H hzero
  obtain ⟨L, hL0, hL⟩ := hp A a ((e : C(C, B)).comp H) (fun x ↦ by
    change e (H (0, x)) = p (a x)
    rw [hzero]
    exact ContinuousMap.congr_fun he (a x))
  refine ⟨L, hL0, ?_⟩
  intro t x
  apply e.injective
  exact (ContinuousMap.congr_fun he (L (t, x))).trans (hL t x)

namespace HomotopyPullback
variable {E A B X : Type u} {K : Type v} [TopologicalSpace E] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace K]
  (p : C(E, B)) (f : C(A, B)) (r : C(X, B))
  (e : A × K ≃ₜ X) (he : ∀ a k, r (e (a, k)) = f a)

/-- A pullback over a product chart with parameter-independent base map is
literally a product of the smaller pullback with the same parameter. -/
def strictProductChartHomeomorph :
    {z : A × E // p z.2 = f z.1} × K ≃ₜ {z : X × E // p z.2 = r z.1} where
  toFun z := ⟨(e (z.1.1.1, z.2), z.1.1.2), z.1.2.trans (he z.1.1.1 z.2).symm⟩
  invFun z := (⟨((e.symm z.1.1).1, z.1.2), z.2.trans
    (by simpa only [e.apply_symm_apply] using he (e.symm z.1.1).1 (e.symm z.1.1).2)⟩,
    (e.symm z.1.1).2)
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z : A × K ↦ z.1) (e.symm_apply_apply (z.1.1.1, z.2))
      · rfl
    · exact congrArg (fun z : A × K ↦ z.2) (e.symm_apply_apply (z.1.1.1, z.2))
  right_inv z := by
    apply Subtype.ext
    exact Prod.ext (e.apply_symm_apply z.1.1) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp] theorem strictProductChartHomeomorph_apply
    (z : {z : A × E // p z.2 = f z.1}) (k : K) :
    (strictProductChartHomeomorph p f r e he (z, k)).1 = (e (z.1.1, k), z.1.2) := rfl

/-- Restricting the actual strict pullback to a base subspace is exactly
the strict pullback over that subspace, by reassociating subtypes. -/
def strictRestrictionHomeomorph (S : Set X) :
    {z : {z : X × E // p z.2 = r z.1} // z.1.1 ∈ S} ≃ₜ
      {z : S × E // p z.2 = r z.1.1} where
  toFun z := ⟨(⟨z.1.1.1, z.2⟩, z.1.1.2), z.1.2⟩
  invFun z := ⟨⟨(z.1.1.1, z.1.2), z.2⟩, z.1.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end HomotopyPullback
end Topology
