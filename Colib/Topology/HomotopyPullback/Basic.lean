/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.Basic
public import Mathlib.Topology.Constructions.SumProd

/-!
# Path-space homotopy pullbacks

The compact-open path-space model has base and source projections and a constant-path comparison
    for strictly commuting squares. Discrete-base fiber coordinates and source homeomorphisms
    give explicit homeomorphisms.
-/
/-! Implementation source: `Quillen/Topology/HomotopyPullback/Basic.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual path-space model and prescribed
constant-path comparisons are retained in their native topological namespace. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology

/-- The actual path-space homotopy pullback of `f` along `g`. Its topology is
inherited from the product with the compact-open path space. -/
def HomotopyPullback {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A]
    [TopologicalSpace B] (f : C(X, B)) (g : C(A, B)) :=
  {z : A × (X × C(I, B)) // z.2.2 0 = f z.2.1 ∧ z.2.2 1 = g z.1}

namespace HomotopyPullback

variable {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A]
  [TopologicalSpace B] (f : C(X, B)) (g : C(A, B))

instance : TopologicalSpace (HomotopyPullback f g) := inferInstanceAs
  (TopologicalSpace {z : A × (X × C(I, B)) // z.2.2 0 = f z.2.1 ∧ z.2.2 1 = g z.1})

/-- Projection to the space along which the homotopy pullback was taken. -/
def baseProjection : C(HomotopyPullback f g, A) where
  toFun z := z.1.1
  continuous_toFun := by fun_prop

/-- Projection to the original source. -/
def sourceProjection : C(HomotopyPullback f g, X) where
  toFun z := z.1.2.1
  continuous_toFun := by fun_prop

/-- A strictly commuting square has its canonical constant-path comparison. -/
def comparison {W : Type u} [TopologicalSpace W] (a : C(W, A)) (h : C(W, X))
    (comm : f.comp h = g.comp a) : C(W, HomotopyPullback f g) where
  toFun w := ⟨(a w, h w, ContinuousMap.const I (g (a w))),
    (ContinuousMap.congr_fun comm w).symm, rfl⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact a.continuous.prodMk (h.continuous.prodMk (by fun_prop))

@[simp]
theorem comparison_baseProjection {W : Type u} [TopologicalSpace W]
    (a : C(W, A)) (h : C(W, X)) (comm : f.comp h = g.comp a) :
    (baseProjection f g).comp (comparison f g a h comm) = a := rfl

@[simp]
theorem comparison_sourceProjection {W : Type u} [TopologicalSpace W]
    (a : C(W, A)) (h : C(W, X)) (comm : f.comp h = g.comp a) :
    (sourceProjection f g).comp (comparison f g a h comm) = h := rfl

/-- The coproduct of point fibers maps into the actual homotopy pullback. -/
def sigmaFibersMap : C((Σ a : A, HomotopyFiber f (g a)), HomotopyPullback f g) where
  toFun z := ⟨(z.1, z.2.1), z.2.2⟩
  continuous_toFun := continuous_sigma fun _a ↦
    (continuous_const.prodMk continuous_subtype_val).subtype_mk _

/-- Over a discrete parameter space, the coproduct-of-fibers topology is
exactly the topology of the genuine homotopy pullback. -/
def sigmaFibersHomeomorph [DiscreteTopology A] :
    (Σ a : A, HomotopyFiber f (g a)) ≃ₜ HomotopyPullback f g := by
  have hind : Topology.IsInducing (sigmaFibersMap f g) := by
    apply inducing_sigma.mpr
    constructor
    · intro a
      exact ((isInducing_prodMkRight (Y := X × C(I, B)) a).comp
        (show Topology.IsInducing (Subtype.val : HomotopyFiber f (g a) → X × C(I, B))
          from Topology.IsInducing.subtypeVal)).codRestrict
        (s := ({z | z.2.2 0 = f z.2.1 ∧ z.2.2 1 = g z.1} : Set (A × (X × C(I, B)))))
        (fun z ↦ z.2)
    · intro a
      refine ⟨(baseProjection f g) ⁻¹' {a},
        (isOpen_discrete {a}).preimage (baseProjection f g).continuous, ?_⟩
      intro z
      rfl
  have hinj : Function.Injective (sigmaFibersMap f g) := by
    rintro ⟨a, x⟩ ⟨b, y⟩ h
    have hab : a = b := congrArg (fun z : HomotopyPullback f g ↦ z.1.1) h
    subst b
    have hxy : x = y := Subtype.ext (congrArg (fun z : HomotopyPullback f g ↦ z.1.2) h)
    subst y
    rfl
  apply (Topology.IsEmbedding.mk hind hinj).toHomeomorphOfSurjective
  intro z
  exact ⟨⟨z.1.1, ⟨z.1.2, z.2⟩⟩, rfl⟩

@[simp]
theorem sigmaFibersHomeomorph_apply [DiscreteTopology A]
    (z : Σ a : A, HomotopyFiber f (g a)) :
    sigmaFibersHomeomorph f g z = sigmaFibersMap f g z := rfl

/-- A homeomorphism in the source induces a homeomorphism of actual
homotopy pullbacks, leaving the base point and target path unchanged. -/
def sourceHomeomorph {Y : Type u} [TopologicalSpace Y] (e : Y ≃ₜ X) :
    HomotopyPullback (f.comp (e : C(Y, X))) g ≃ₜ HomotopyPullback f g where
  toFun z := ⟨(z.1.1, e z.1.2.1, z.1.2.2), z.2⟩
  invFun z := ⟨(z.1.1, e.symm z.1.2.1, z.1.2.2), by simpa using z.2⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (by fun_prop : Continuous fun z : HomotopyPullback (f.comp (e : C(Y, X))) g ↦
      (z.1.1, e z.1.2.1, z.1.2.2))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (by fun_prop : Continuous fun z : HomotopyPullback f g ↦
      (z.1.1, e.symm z.1.2.1, z.1.2.2))

end HomotopyPullback

end Topology

end
