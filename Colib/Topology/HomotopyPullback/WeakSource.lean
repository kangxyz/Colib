/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.WeakSourceEquivalence
public import Colib.Topology.HomotopyPullback.SourceEquivalence
public import Colib.Topology.HomotopyPullback.Symmetry

/-! # Uniform weak source change for actual homotopy pullbacks

The original parameter/path-retaining source map is the strict pullback of
the original weak source map along a genuine projection fibration. This
proves the complete weak property without selecting inverse maps in fibers.


Implementation provenance:
`Quillen/Topology/HomotopyPullback/WeakSource.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Topology.HomotopyPullback
variable {X Y A Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace Z]
  (q : C(A, Y)) (f : C(X, Y)) (k : C(Z, X))

/-- The actual source projection is a genuine fibration, by the exact path
reversal homeomorphism and the known base-projection fibration. -/
theorem sourceProjection_homotopyLiftingProperty :
    HomotopyLiftingProperty (sourceProjection f q) :=
  HomotopyLiftingProperty.comp_homeomorph (baseProjection q f)
    (baseProjection_homotopyLiftingProperty q f) (symmetryHomeomorph f q)

/-- The original source-changed pullback is exactly the strict pullback of
the original source map along the original source projection. -/
def sourceMapPullbackHomeomorph : HomotopyPullback (f.comp k) q ≃ₜ
    {z : Z × HomotopyPullback f q // sourceProjection f q z.2 = k z.1} where
  toFun z := ⟨(z.1.2.1, sourceMap q f k z), rfl⟩
  invFun z := ⟨(z.1.2.1.1, z.1.1, z.1.2.1.2.2),
    z.1.2.2.1.trans (congrArg f z.2), z.1.2.2.2⟩
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · exact z.2.symm
        · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- A weak source change induces the complete weak equivalence on the actual
total homotopy pullbacks, retaining parameter and path literally. -/
theorem sourceMap_isWeakHomotopyEquivalence (hk : IsWeakHomotopyEquivalence k) :
    IsWeakHomotopyEquivalence (sourceMap q f k) :=
  (strictSourceProjection_isWeakHomotopyEquivalence (sourceProjection f q) k
    (sourceProjection_homotopyLiftingProperty q f) hk).comp
      (isWeakHomotopyEquivalence_of_homotopyEquiv (sourceMapPullbackHomeomorph q f
        k).toHomotopyEquiv)

@[simp] theorem sourceMap_source (z : HomotopyPullback (f.comp k) q) :
    (sourceMap q f k z).1.2.1 = k z.1.2.1 := rfl

@[simp] theorem sourceMap_path (z : HomotopyPullback (f.comp k) q) :
    (sourceMap q f k z).1.2.2 = z.1.2.2 := rfl

end Topology.HomotopyPullback
