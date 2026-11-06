/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.SourceEquivalence
public import Colib.Topology.HomotopyPullback.Pasting
public import Colib.Topology.HomotopyPullback.Products

/-!
# Symmetry of path-space homotopy pullbacks

Path reversal supplies the symmetry homeomorphism and parameter equivalence, retaining the
    original continuous maps.
-/
/-! Implementation source: `Quillen/Topology/HomotopyPullback/Symmetry.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual compact-open path topology,
parameter spaces and canonical forward maps are retained. -/
@[expose] public section


noncomputable section
universe u
open scoped Topology unitInterval
namespace Topology.HomotopyPullback
variable {X A B C : Type u} [TopologicalSpace X] [TopologicalSpace A]
  [TopologicalSpace B] [TopologicalSpace C]
  (f : C(X, B)) (g : C(A, B))

/-- The homeomorphism interchanging the two homotopy-pullback coordinates and reversing the
stored path. -/
def symmetryHomeomorph : HomotopyPullback f g ≃ₜ HomotopyPullback g f where
  toFun z := ⟨(z.1.2.1, z.1.1, ⟨fun t ↦ z.1.2.2 (unitInterval.symm t), by fun_prop⟩),
    by simpa using z.2.2, by simpa using z.2.1⟩
  invFun z := ⟨(z.1.2.1, z.1.1, ⟨fun t ↦ z.1.2.2 (unitInterval.symm t), by fun_prop⟩),
    by simpa using z.2.2, by simpa using z.2.1⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · ext t; simp
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · ext t; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : HomotopyPullback f g × unitInterval ↦ z.1.1.2.2
      (unitInterval.symm z.2))
    fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : HomotopyPullback g f × unitInterval ↦ z.1.1.2.2
      (unitInterval.symm z.2))
    fun_prop

/-- The map of homotopy pullbacks induced by `k : C ⟶ A` on the parameter coordinate, leaving
the source coordinate and stored path fixed. -/
def parameterMap (k : C(C, A)) : C(HomotopyPullback f (g.comp k), HomotopyPullback f g) where
  toFun z := ⟨(k z.1.1, z.1.2), z.2⟩
  continuous_toFun := by fun_prop

/-- The homotopy equivalence of homotopy pullbacks induced by a homotopy equivalence of the
parameter spaces, with forward map `parameterMap`. -/
def parameterEquiv (e : ContinuousMap.HomotopyEquiv C A) :
    ContinuousMap.HomotopyEquiv (HomotopyPullback f (g.comp e.toFun)) (HomotopyPullback f g) := by
  let E := (symmetryHomeomorph f (g.comp e.toFun)).toHomotopyEquiv.trans
    ((sourceEquiv f g e).trans (symmetryHomeomorph g f).toHomotopyEquiv)
  have he : E.toFun = parameterMap f g e.toFun := by
    apply ContinuousMap.ext
    intro z
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply ContinuousMap.ext
        intro t
        change z.1.2.2 (unitInterval.symm (unitInterval.symm t)) = z.1.2.2 t
        simp
  exact { E with toFun := parameterMap f g e.toFun
                 left_inv := by simpa only [he] using E.left_inv
                 right_inv := by simpa only [he] using E.right_inv }

@[simp] theorem parameterEquiv_toFun (e : ContinuousMap.HomotopyEquiv C A) :
    (parameterEquiv f g e).toFun = parameterMap f g e.toFun := rfl

/-- If the parameter map is an actual HE, the canonical source projection
from its homotopy pullback is an actual HE. -/
def sourceProjectionEquivOfParameterEquiv (e : ContinuousMap.HomotopyEquiv A B)
    (he : e.toFun = g) : ContinuousMap.HomotopyEquiv (HomotopyPullback f g) X := by
  let E₀ : ContinuousMap.HomotopyEquiv A B := {
    e with toFun := g
           left_inv := by simpa only [he] using e.left_inv
           right_inv := by simpa only [he] using e.right_inv }
  let E := (symmetryHomeomorph f g).toHomotopyEquiv.trans
    ((sourceEquiv f (ContinuousMap.id B) E₀).trans (identityHomotopyEquiv f).symm)
  have hE : E.toFun = sourceProjection f g := by
    apply ContinuousMap.ext
    intro z
    rfl
  exact { E with toFun := sourceProjection f g
                 left_inv := by simpa only [hE] using E.left_inv
                 right_inv := by simpa only [hE] using E.right_inv }

@[simp] theorem sourceProjectionEquivOfParameterEquiv_toFun
    (e : ContinuousMap.HomotopyEquiv A B) (he : e.toFun = g) :
    (sourceProjectionEquivOfParameterEquiv f g e he).toFun = sourceProjection f g := rfl

end Topology.HomotopyPullback

end
