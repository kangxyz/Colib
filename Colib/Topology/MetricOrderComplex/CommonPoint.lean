/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.MetricOrderComplex.CommonMass

/-!
# The normalized common-support point

Normalize the coordinatewise minimum on its positive-mass domain. The resulting
point has support exactly the intersection of the original chain supports and
is the original point on the diagonal. The union of the supports is never
required to be a chain. Continuity of this normalization remains a separate
L1 estimate, rather than a coordinatewise continuity inference.
-/

/-! Implementation source: `Quillen/Topology/MetricOrderComplex/CommonPoint.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual finitely supported
coordinate model, L1 topology and universe parameters are retained. -/
@[expose] public section
noncomputable section

universe u
namespace Topology.MetricOrderComplex

variable {P : Type u} [PartialOrder P]

/-- Classical equality is used only to enumerate finite supports. -/
local instance instDecidableEqCommonPoint : DecidableEq P := Classical.decEq P

/-- The common point is supported in each of the original simplices. -/
def commonPoint (x y : MetricOrderComplex P) (h : 0 < commonMass x y) :
    MetricOrderComplex P := by
  refine ⟨⟨(commonMass x y)⁻¹ • commonWeights x y, ?_, ?_⟩, ?_⟩
  · intro v
    exact mul_nonneg (inv_nonneg.mpr h.le) (commonWeights_nonneg x y v)
  · rw [Finsupp.sum_smul_index (fun _ ↦ rfl)]
    change (∑ v ∈ (commonWeights x y).support,
      (commonMass x y)⁻¹ * commonWeights x y v) = 1
    rw [← Finset.mul_sum]
    exact inv_mul_cancel₀ (ne_of_gt h)
  · refine IsChain.mono ?_ x.support_chain
    intro v hv
    have hc := Finsupp.support_smul hv
    rw [commonWeights_support] at hc
    exact (Finset.mem_inter.mp hc).1

@[simp]
theorem commonPoint_weights (x y : MetricOrderComplex P) (h : 0 < commonMass x y) (v : P) :
    (commonPoint x y h).weights v = min (x.weights v) (y.weights v) / commonMass x y := by
  change (commonMass x y)⁻¹ * commonWeights x y v = _
  simp only [commonWeights_apply, div_eq_mul_inv, mul_comm]

/-- Normalization changes no surviving coordinates in the support intersection. -/
theorem commonPoint_support (x y : MetricOrderComplex P) (h : 0 < commonMass x y) :
    (commonPoint x y h).weights.support = x.weights.support ∩ y.weights.support := by
  change ((commonMass x y)⁻¹ • commonWeights x y).support = _
  rw [Finsupp.support_smul_eq (inv_ne_zero (ne_of_gt h)), commonWeights_support]

/-- The common-support construction fixes the whole diagonal, not just vertices. -/
@[simp]
theorem commonPoint_self (x : MetricOrderComplex P) (h : 0 < commonMass x x) :
    commonPoint x x h = x := by
  ext v
  simp

end Topology.MetricOrderComplex
