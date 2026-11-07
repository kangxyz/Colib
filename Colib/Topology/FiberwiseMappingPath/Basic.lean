/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.MappingPath.Basic

/-! # Vertical mapping paths

The stored path lies in one actual fiber of the displayed target projection.
The topology is the induced compact-open topology. Literal path scaling
contracts this space onto the original source, without a lifting hypothesis.


Implementation provenance:
`Quillen/Topology/FiberwiseMappingPath/Basic.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open scoped Topology unitInterval
open unitInterval
universe u v w
namespace Topology.FiberwiseMappingPath
variable {E : Type u} {F : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B]

/-- The original source coordinate and an entire vertical path starting at its image. -/
def Space (q : C(F, B)) (f : C(E, F)) :=
  {z : E × C(I,F) // z.2 0 = f z.1 ∧ ∀ t,q (z.2 t) = q (f z.1)}

instance (q : C(F, B)) (f : C(E, F)) : TopologicalSpace (Space q f) :=
  inferInstanceAs (TopologicalSpace {z : E × C(I,F) //
    z.2 0 = f z.1 ∧ ∀ t,q (z.2 t) = q (f z.1)})

variable (q : C(F, B)) (f : C(E, F))

/-- The continuous projection from a vertical mapping-path point to its original source
coordinate in `E`. -/
def source : C(Space q f,E) where
  toFun z := z.1.1
  continuous_toFun := by fun_prop

/-- Evaluate the stored vertical path at time `1` to obtain a point of `F`. -/
def endpoint : C(Space q f,F) where
  toFun z := z.1.2 1
  continuous_toFun := by fun_prop

/-- Embed `E` into the vertical mapping-path space by constant paths at `f x`. -/
def inclusion : C(E,Space q f) where
  toFun x := ⟨(x,ContinuousMap.const I (f x)),rfl,fun _ ↦ rfl⟩
  continuous_toFun := by fun_prop

@[simp] theorem source_inclusion : (source q f).comp (inclusion q f) = ContinuousMap.id E := rfl
@[simp] theorem endpoint_inclusion : (endpoint q f).comp (inclusion q f) = f := rfl

theorem endpoint_base : q.comp (endpoint q f) = (q.comp f).comp (source q f) := by
  ext z
  exact z.2.2 1

/-- The contraction retains the whole path, precomposed with literal interval scaling. -/
def contraction : (ContinuousMap.id (Space q f)).Homotopy
    ((inclusion q f).comp (source q f)) where
  toFun z := ⟨(z.2.1.1,⟨fun s ↦ z.2.1.2 (σ z.1 * s),by fun_prop⟩),
    by simpa using z.2.2.1,fun s ↦ z.2.2.2 (σ z.1 * s)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (I × Space q f) × I ↦ z.1.2.1.2 (σ z.1.1 * z.2))
      fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext s
      simp
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext s
      change z.1.2 (σ 1 * s) = f z.1.1
      simpa using z.2.1

@[simp] theorem contraction_source (t : I) (z : Space q f) :
    source q f (contraction q f (t,z)) = source q f z := rfl

theorem contraction_path (t s : I) (z : Space q f) :
    (contraction q f (t,z)).1.2 s = z.1.2 (σ t * s) := rfl

@[simp] theorem contraction_inclusion (t : I) (x : E) :
    contraction q f (t,inclusion q f x) = inclusion q f x := rfl

theorem contraction_base (t : I) (z : Space q f) :
    q (endpoint q f (contraction q f (t,z))) = q (endpoint q f z) :=
  (z.2.2 _).trans (z.2.2 1).symm

/-- The original constant-path inclusion, with the literal source projection as inverse. -/
def inclusionHomotopyEquiv : ContinuousMap.HomotopyEquiv E (Space q f) where
  toFun := inclusion q f
  invFun := source q f
  left_inv := ContinuousMap.Homotopic.refl _
  right_inv := ⟨(contraction q f).symm⟩

@[simp] theorem inclusionHomotopyEquiv_toFun :
    (inclusionHomotopyEquiv q f).toFun = inclusion q f := rfl
@[simp] theorem inclusionHomotopyEquiv_invFun :
    (inclusionHomotopyEquiv q f).invFun = source q f := rfl

end Topology.FiberwiseMappingPath
