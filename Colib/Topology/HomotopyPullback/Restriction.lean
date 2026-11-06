/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Pasting

/-!
# Restriction of path-space homotopy pullbacks

The restriction comparison and its homotopy equivalence retain the original base-change and
    pushout hypotheses.
-/
/-! Implementation source: `Quillen/Topology/HomotopyPullback/Restriction.lean` and the
coordinate congruence from `Pushout.lean` at c561118b7795eb9780be9ed391c3251d6a4d0afd.
The actual compact-open path coordinates are unchanged. -/
@[expose] public section


noncomputable section
open scoped Topology unitInterval
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.HomotopyPullback
/-- Equal base maps identify their path-space pullbacks without changing
any actual coordinate. -/
def baseMapCongr {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    (f : C(X, B)) (g g' : C(A, B)) (h : g = g') : HomotopyPullback f g ≃ₜ HomotopyPullback f g'
      where
  toFun z := ⟨z.1, z.2.1, z.2.2.trans (ContinuousMap.congr_fun h z.1.1)⟩
  invFun z := ⟨z.1, z.2.1, z.2.2.trans (ContinuousMap.congr_fun h z.1.1).symm⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {E X B A : Type u} [TopologicalSpace E] [TopologicalSpace X]
  [TopologicalSpace B] [TopologicalSpace A]
  (f : C(E, B)) (g : C(X, B)) (S : Set X)

/-- Restrict the parameter map `g : X → B` to the subspace `S ⊆ X`. -/
def restrictedParameter : C(S, B) := ⟨fun x ↦ g x.1, by fun_prop⟩

/-- Restricting the homotopy pullback to a base subspace is exactly the
homotopy pullback along the restricted parameter map. -/
def restrictionHomeomorph :
    {z : HomotopyPullback f g // baseProjection f g z ∈ S} ≃ₜ
      HomotopyPullback f (restrictedParameter g S) where
  toFun z := ⟨(⟨z.1.1.1, z.2⟩, z.1.1.2), z.1.2⟩
  invFun z := ⟨⟨(z.1.1.1, z.1.2), z.2⟩, z.1.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A factorization of the parameter map through a retraction gives an
actual strict-pullback chart of its homotopy pullback. -/
def retractionChartHomeomorph (r : C(S, A)) (a : C(A, B))
    (hr : restrictedParameter g S = a.comp r) :
    {z : HomotopyPullback f g // baseProjection f g z ∈ S} ≃ₜ
      {z : S × HomotopyPullback f a // baseProjection f a z.2 = r z.1} :=
  (restrictionHomeomorph f g S).trans
    ((baseMapCongr f _ _ hr).trans (pastingStrictHomeomorph f r a))

@[simp] theorem retractionChartHomeomorph_apply (r : C(S, A)) (a : C(A, B))
    (hr : restrictedParameter g S = a.comp r)
    (z : {z : HomotopyPullback f g // baseProjection f g z ∈ S}) :
    (retractionChartHomeomorph f g S r a hr z).1.1.1 = z.1.1.1 := rfl

@[simp] theorem retractionChartHomeomorph_source (r : C(S, A)) (a : C(A, B))
    (hr : restrictedParameter g S = a.comp r)
    (z : {z : HomotopyPullback f g // baseProjection f g z ∈ S}) :
    (retractionChartHomeomorph f g S r a hr z).1.2.1.2 = z.1.1.2 := rfl

/-- Homotopy pullbacks in an actual product parameter chart split off
the unchanged parameter whenever the base map is independent of it. -/
def parameterProductHomeomorph {K : Type v} [TopologicalSpace K]
    (a : C(A, B)) (e : A × K ≃ₜ X) (he : ∀ x t, g (e (x, t)) = a x) :
    HomotopyPullback f a × K ≃ₜ HomotopyPullback f g where
  toFun z := ⟨(e (z.1.1.1, z.2), z.1.1.2), z.1.2.1,
    z.1.2.2.trans (he z.1.1.1 z.2).symm⟩
  invFun z := (⟨((e.symm z.1.1).1, z.1.2), z.2.1, z.2.2.trans
    (by simpa only [e.apply_symm_apply] using he (e.symm z.1.1).1 (e.symm z.1.1).2)⟩,
    (e.symm z.1.1).2)
  left_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (congrArg (fun z : A × K ↦ z.1) (e.symm_apply_apply (z.1.1.1, z.2))) rfl
    · exact congrArg (fun z : A × K ↦ z.2) (e.symm_apply_apply (z.1.1.1, z.2))
  right_inv z := by
    apply Subtype.ext
    exact Prod.ext (e.apply_symm_apply z.1.1) rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

end Topology.HomotopyPullback

end
