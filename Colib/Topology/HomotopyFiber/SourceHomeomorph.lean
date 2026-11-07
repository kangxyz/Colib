/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.SourceEquivalence

/-! Source: the source-homeomorphism section of
`Quillen/CategoryTheory/TheoremB/RealizedRowFibers.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The target path is retained exactly. -/
@[expose] public noncomputable section
open scoped Topology

namespace Topology.HomotopyFiber

/-- A homeomorphism of sources gives a homeomorphism of actual homotopy fibers,
with source change and its inverse leaving the target path unchanged. -/
def sourceHomeomorph {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (e : Z ≃ₜ X) (y : Y) :
    HomotopyFiber (f.comp (e : C(Z, X))) y ≃ₜ HomotopyFiber f y where
  toFun := sourceMap f (e : C(Z, X)) y
  invFun z := ⟨(e.symm z.1.1, z.1.2), by simpa using z.2.1, z.2.2⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact e.symm_apply_apply _
    · rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact e.apply_symm_apply _
    · rfl
  continuous_toFun := (sourceMap f (e : C(Z, X)) y).continuous
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (e.symm.continuous.comp (projection f y).continuous).prodMk (by fun_prop)

@[simp]
theorem sourceHomeomorph_apply {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (e : Z ≃ₜ X) (y : Y)
    (z : HomotopyFiber (f.comp (e : C(Z, X))) y) :
    sourceHomeomorph f e y z = sourceMap f (e : C(Z, X)) y z := rfl

end Topology.HomotopyFiber
