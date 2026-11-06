/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Homotopy fibers over a discrete base

The actual compact-open path-space homotopy fiber of a map to a discrete
space is homeomorphic to its strict fiber. In particular, the homotopy fiber
of a coproduct projection is its chosen summand. The inverse homeomorphisms
are the usual inclusions by constant paths.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/DiscreteBase.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual comma categories, nerves and
path-space maps are retained; no fiber-equivalence conclusion is assumed. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval
open unitInterval

universe u v

namespace Topology.HomotopyFiber

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable [DiscreteTopology Y] (f : C(X, Y)) (y : Y)

/-- A path in a discrete space is constant, including when it is carried by
an actual point of the homotopy fiber. -/
theorem path_eq_const (z : HomotopyFiber f y) : z.1.2 = ContinuousMap.const I y := by
  ext t
  exact (TotallyDisconnectedSpace.eq_of_continuous z.1.2 z.1.2.continuous t 1).trans z.2.2

/-- Over a discrete base the homotopy-fiber projection lands in the strict fiber. -/
theorem projection_mem_strictFiber (z : HomotopyFiber f y) : f (projection f y z) = y := by
  exact z.2.1.symm.trans ((congrArg (fun p : C(I, Y) => p 0) (path_eq_const f y z)))

/-- The actual homotopy fiber over a discrete space is homeomorphic to the
strict fiber. Its inverse includes each point with the constant path. -/
def strictFiberHomeomorph : HomotopyFiber f y ≃ₜ {x : X // f x = y} where
  toFun z := ⟨projection f y z, projection_mem_strictFiber f y z⟩
  invFun := strictFiberInclusion f y
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (path_eq_const f y z).symm
  right_inv z := by
    apply Subtype.ext
    rfl
  continuous_toFun := (projection f y).continuous.subtype_mk _
  continuous_invFun := (strictFiberInclusion f y).continuous

@[simp]
theorem strictFiberHomeomorph_apply_val (z : HomotopyFiber f y) :
    (strictFiberHomeomorph f y z).1 = projection f y z := rfl

@[simp]
theorem strictFiberHomeomorph_symm_apply (z : {x : X // f x = y}) :
    (strictFiberHomeomorph f y).symm z = strictFiberInclusion f y z := rfl

@[simp]
theorem strictFiberHomeomorph_strictFiberInclusion (z : {x : X // f x = y}) :
    strictFiberHomeomorph f y (strictFiberInclusion f y z) = z :=
  (strictFiberHomeomorph f y).apply_symm_apply z

end Topology.HomotopyFiber

namespace Topology

variable {A : Type u} (X : A → Type v) [TopologicalSpace A] [DiscreteTopology A]
variable [∀ a, TopologicalSpace (X a)]

/-- The continuous projection from a topological coproduct to its discrete index space. -/
def sigmaProjection : C((a : A) × X a, A) where
  toFun := Sigma.fst
  continuous_toFun := continuous_sigma fun _ => continuous_const

/-- A point in the strict fiber of a coproduct projection, viewed in its chosen summand. -/
def sigmaStrictFiberValue (a : A) (z : {x : (a : A) × X a // sigmaProjection X x = a}) :
    X a := z.2 ▸ z.1.2

omit [DiscreteTopology A] in
@[simp]
theorem sigmaMk_sigmaStrictFiberValue (a : A)
    (z : {x : (a : A) × X a // sigmaProjection X x = a}) :
    Sigma.mk a (sigmaStrictFiberValue X a z) = z.1 := by
  rcases z with ⟨⟨b, x⟩, h⟩
  change b = a at h
  subst a
  rfl

/-- The strict fiber of a coproduct projection is its chosen summand,
with the actual subspace and coproduct topologies. -/
def sigmaStrictFiberHomeomorph (a : A) :
    {x : (a : A) × X a // sigmaProjection X x = a} ≃ₜ X a where
  toFun := sigmaStrictFiberValue X a
  invFun x := ⟨⟨a, x⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    exact sigmaMk_sigmaStrictFiberValue X a z
  right_inv x := rfl
  continuous_toFun := by
    apply Topology.IsEmbedding.sigmaMk.continuous_iff.mpr
    simpa only [Function.comp_def, sigmaMk_sigmaStrictFiberValue] using
      (continuous_subtype_val : Continuous
        (fun z : {x : (a : A) × X a // sigmaProjection X x = a} => z.1))
  continuous_invFun := continuous_sigmaMk.subtype_mk _

/-- The actual homotopy fiber of a coproduct projection is homeomorphic to
its chosen summand. No homotopy-fiber equivalence is assumed. -/
def sigmaProjectionFiberHomeomorph (a : A) : HomotopyFiber (sigmaProjection X) a ≃ₜ X a :=
  (HomotopyFiber.strictFiberHomeomorph (sigmaProjection X) a).trans
    (sigmaStrictFiberHomeomorph X a)

/-- The standard comparison into the homotopy fiber, with constant path. -/
def sigmaFiberInclusion (a : A) : C(X a, HomotopyFiber (sigmaProjection X) a) where
  toFun x := HomotopyFiber.basepoint (sigmaProjection X) a ⟨a, x⟩ rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_sigmaMk.prodMk continuous_const

@[simp]
theorem sigmaProjectionFiberHomeomorph_symm_apply (a : A) (x : X a) :
    (sigmaProjectionFiberHomeomorph X a).symm x = sigmaFiberInclusion X a x := rfl

/-- The standard constant-path comparison is exactly the inverse homeomorphism. -/
theorem sigmaFiberInclusion_eq_homeomorph (a : A) :
    sigmaFiberInclusion X a =
      ((sigmaProjectionFiberHomeomorph X a).symm : C(X a, HomotopyFiber (sigmaProjection X) a))
        := rfl

@[simp]
theorem sigmaProjectionFiberHomeomorph_inclusion (a : A) (x : X a) :
    sigmaProjectionFiberHomeomorph X a (sigmaFiberInclusion X a x) = x :=
  (sigmaProjectionFiberHomeomorph X a).apply_symm_apply x

@[simp]
theorem sigmaFiberInclusion_homeomorph (a : A) (z : HomotopyFiber (sigmaProjection X) a) :
    sigmaFiberInclusion X a (sigmaProjectionFiberHomeomorph X a z) = z :=
  (sigmaProjectionFiberHomeomorph X a).symm_apply_apply z

/-- The homeomorphism identifies the projection with the summand embedding. -/
@[simp]
theorem sigmaProjectionFiberHomeomorph_projection (a : A) (z : HomotopyFiber (sigmaProjection X)
    a) :
    Sigma.mk a (sigmaProjectionFiberHomeomorph X a z) = HomotopyFiber.projection
      (sigmaProjection X) a z :=
  sigmaMk_sigmaStrictFiberValue X a _

end Topology
