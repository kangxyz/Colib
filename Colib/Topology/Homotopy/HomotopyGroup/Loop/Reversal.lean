/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift

/-!
# Reversal of the actual based loop space

Loop reversal is a continuous involution, preserves the constant loop exactly,
and commutes strictly with based loop maps. It maps paths and homotopies
pointwise. Concatenation is reversed in order, without any commutativity
assumption on the fundamental group.

Under the original loop-degree shift, reversal reflects the first cube
coordinate and therefore induces the genuine homotopy-group inverse. The
set-valued statement includes outer degree zero. In positive outer degree the
existing group structure on the homotopy groups of the loop space also
identifies this action with inversion.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/Loop/Reversal.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual maps, endpoint paths,
universes and signs are retained, with native Colib dependencies.
The reversal homeomorphism is extracted unchanged from
`Quillen/Topology/HomotopyGroups/Loop/LeftComponentTranslation.lean` at the same revision. -/
@[expose] public section

noncomputable section
open scoped Topology unitInterval

universe u v
namespace Topology

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Reversing the actual loop parameter is an involutive homeomorphism. -/
def loopReversalHomeomorph (x : X) : Path x x ≃ₜ Path x x where
  toFun := Path.symm
  invFun := Path.symm
  left_inv := Path.symm_symm
  right_inv := Path.symm_symm
  continuous_toFun := Path.continuous_symm
  continuous_invFun := Path.continuous_symm

/-- Reverse the parameter of each actual based loop. -/
def loopReversal : C(Path x x, Path x x) :=
  ⟨Path.symm, Path.continuous_symm⟩

@[simp]
theorem loopReversal_apply (γ : Path x x) : loopReversal γ = γ.symm := rfl

theorem loopReversal_apply_apply (γ : Path x x) (t : unitInterval) :
    loopReversal γ t = γ (unitInterval.symm t) := rfl

/-- The constant loop is preserved as an equality of paths. -/
@[simp]
theorem loopReversal_refl : loopReversal (Path.refl x) = Path.refl x := rfl

/-- Reversing a loop twice is the identity. -/
theorem loopReversal_involutive : Function.Involutive (loopReversal (x := x)) :=
  Path.symm_symm

@[simp]
theorem loopReversalHomeomorph_apply (γ : Path x x) :
    loopReversalHomeomorph x γ = loopReversal γ := rfl

/-- Reversal reverses the order of concatenation on an arbitrary loop space. -/
theorem loopReversal_trans (γ δ : Path x x) :
    loopReversal (γ.trans δ) = (loopReversal δ).trans (loopReversal γ) :=
  Path.trans_symm γ δ

section Naturality
variable {Y : Type v} [TopologicalSpace Y] {y : Y}

/-- Based loop maps commute with reversal, including their endpoint casts. -/
theorem basedLoopMap_loopReversal (f : C(X, Y)) (hf : f x = y) (γ : Path x x) :
    basedLoopMap f hf (loopReversal γ) = loopReversal (basedLoopMap f hf γ) := by
  ext t
  rfl

/-- Strict naturality of reversal as an equality of continuous maps. -/
theorem loopReversal_natural (f : C(X, Y)) (hf : f x = y) :
    (basedLoopMap f hf).comp loopReversal = loopReversal.comp (basedLoopMap f hf) := by
  ext γ t
  rfl

end Naturality

/-- Map a path of loops pointwise by loop reversal. -/
def loopReversalPath {γ δ : Path x x} (p : Path γ δ) :
    Path (loopReversal γ) (loopReversal δ) :=
  p.map loopReversal.continuous

@[simp]
theorem loopReversalPath_apply {γ δ : Path x x} (p : Path γ δ)
    (s t : unitInterval) :
    loopReversalPath p s t = p s (unitInterval.symm t) := rfl

/-- Map a homotopy of loop-valued maps by reversing only the loop parameter. -/
def loopReversalHomotopy {Z : Type v} [TopologicalSpace Z]
    {f g : C(Z, Path x x)} (H : f.Homotopy g) :
    (loopReversal.comp f).Homotopy (loopReversal.comp g) :=
  (ContinuousMap.Homotopy.refl loopReversal).comp H

@[simp]
theorem loopReversalHomotopy_apply {Z : Type v} [TopologicalSpace Z]
    {f g : C(Z, Path x x)} (H : f.Homotopy g) (s : unitInterval) (z : Z)
    (t : unitInterval) :
    loopReversalHomotopy H (s, z) t = H (s, z) (unitInterval.symm t) := rfl

/-- Pointwise reversal preserves the relative condition of a loop-valued homotopy. -/
def loopReversalHomotopyRel {Z : Type v} [TopologicalSpace Z]
    {f g : C(Z, Path x x)} {S : Set Z} (H : f.HomotopyRel g S) :
    (loopReversal.comp f).HomotopyRel (loopReversal.comp g) S :=
  H.compContinuousMap loopReversal

@[simp]
theorem loopReversalHomotopyRel_apply {Z : Type v} [TopologicalSpace Z]
    {f g : C(Z, Path x x)} {S : Set Z} (H : f.HomotopyRel g S)
    (s : unitInterval) (z : Z) (t : unitInterval) :
    loopReversalHomotopyRel H (s, z) t = H (s, z) (unitInterval.symm t) := rfl

/-- The loop parameter becomes coordinate zero under the original uncurrying,
so actual loop reversal is precisely reflection in that coordinate. -/
theorem loopUncurry_loopReversal {n : ℕ}
    (p : GenLoop (Fin n) (Path x x) (Path.refl x)) :
    loopUncurry (GenLoop.postcomp loopReversal loopReversal_refl p) =
      GenLoop.symmAt 0 (loopUncurry p) := by
  ext z
  change p (Fin.tail z) (unitInterval.symm (z 0)) =
    p (Fin.tail (fun j : Fin (n + 1) ↦ if j = 0 then unitInterval.symm (z 0) else z j))
      (if (0 : Fin (n + 1)) = 0 then unitInterval.symm (z 0) else z 0)
  congr 1

set_option backward.isDefEq.respectTransparency.types false in
/-- The original degree-shift inverse identifies reversal with group inversion.
This statement includes outer degree zero without giving its homotopy set a
spurious generic commutative group structure. -/
theorem loopShiftEquiv_symm_loopReversal (n : ℕ)
    (a : HomotopyGroup.Pi n (Path x x) (Path.refl x)) :
    (loopShiftEquiv (x := x) n).symm
      (HomotopyGroup.map loopReversal loopReversal_refl a) =
      ((loopShiftEquiv (x := x) n).symm a)⁻¹ := by
  refine Quotient.inductionOn a (fun p ↦ ?_)
  change (Quotient.mk' (loopUncurry
      (GenLoop.postcomp loopReversal loopReversal_refl p)) : HomotopyGroup.Pi (n + 1) X x) =
    ((Quotient.mk' (loopUncurry p))⁻¹ : HomotopyGroup.Pi (n + 1) X x)
  rw [loopUncurry_loopReversal]
  exact (HomotopyGroup.inv_spec (i := (0 : Fin (n + 1))) (p := loopUncurry p)).symm

/-- Equivalent forward form, including the zeroth homotopy set of the loop space. -/
theorem homotopyGroupMap_loopReversal_loopShiftEquiv (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) X x) :
    HomotopyGroup.map loopReversal loopReversal_refl (loopShiftEquiv n a) =
      loopShiftEquiv n a⁻¹ := by
  apply (loopShiftEquiv (x := x) n).symm.injective
  rw [loopShiftEquiv_symm_loopReversal, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- In positive outer degree, reversal induces inversion on the loop space's
existing homotopy group. Its group law is not redefined. -/
theorem homotopyGroupMap_loopReversal (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) (Path x x) (Path.refl x)) :
    HomotopyGroup.map loopReversal loopReversal_refl a = a⁻¹ := by
  apply (loopShiftMulEquiv (x := x) n).symm.injective
  exact (loopShiftEquiv_symm_loopReversal (n + 1) a).trans
    (map_inv (loopShiftMulEquiv (x := x) n).symm a).symm

end Topology
