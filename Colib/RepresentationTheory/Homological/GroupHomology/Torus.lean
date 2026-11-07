/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.RepresentationTheory.Homological.GroupHomology.CentralEvaluation
public import Colib.GroupTheory.MonoidHom.CentralKernel

/-!
# Central-extension evaluation on the ordered native bar torus

The literal ordered chain `[g|h] - [h|g]` is a cycle when `g` and `h` commute.
Evaluating its native homology class gives the commutator of any chosen lifts.
The negative evaluation therefore sends the negative ordered torus class to the
same positive commutator. This records the sign needed when a geometric torus
comparison has negative orientation, without assuming such a comparison.

The torus cycle is adapted from
`Quillen/Aglib/RepresentationTheory/Homological/GroupHomology/Torus.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, omitting the unused perfectness
hypothesis and using Mathlib's native homology throughout.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open Finsupp
open scoped commutatorElement IsMulCommutative

namespace groupHomology

variable (k G : Type u) [CommRing k] [Group G]

/-- The ordered bar torus is a cycle in the native complex with trivial coefficients. -/
def torusCycle (g h : G) (hgh : Commute g h) : cycles₂ (Rep.trivial k G k) :=
  ⟨single (g, h) 1 - single (h, g) 1, by
    change d₂₁ (Rep.trivial k G k) _ = 0
    rw [map_sub, d₂₁_single, d₂₁_single]
    change (single h 1 - single (g * h) 1 + single g 1) -
      (single g 1 - single (h * g) 1 + single h 1) = 0
    rw [hgh.eq]
    abel⟩

variable {G} {H : Type v} [Group H]
  (p : H →* G) (hp : Function.Surjective p) (hc : p.ker ≤ Subgroup.center H)

/-- Evaluation on the ordered torus equals the commutator of its normalized section lifts. -/
theorem centralHomologyEvaluation_torusCycle (g h : G) (hgh : Commute g h) :
    (centralHomologyEvaluation p hp hc
      (H2π (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ))
        (torusCycle (ULift.{u} ℤ) G g h hgh))).toMul.val =
      ⁅centralSection p hp g, centralSection p hp h⁆ := by
  rw [centralHomologyEvaluation, H2Desc_pi]
  change (defectEvaluation p hp hc (single (g, h) 1 - single (h, g) 1)).toMul.val = _
  rw [map_sub, defectEvaluation_single_one, defectEvaluation_single_one]
  simp only [toMul_sub, toMul_ofMul, div_eq_mul_inv]
  change (centralSection p hp g * centralSection p hp h * (centralSection p hp (g * h))⁻¹) *
    (centralSection p hp h * centralSection p hp g * (centralSection p hp (h * g))⁻¹)⁻¹ = _
  rw [hgh.eq, commutatorElement_def]
  group

/-- The ordered torus evaluates to the commutator of any actual lifts of its two elements. -/
theorem centralHomologyEvaluation_torusCycle_of_lifts (g h : G) (hgh : Commute g h)
    (x y : H) (hx : p x = g) (hy : p y = h) :
    (centralHomologyEvaluation p hp hc
      (H2π (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ))
        (torusCycle (ULift.{u} ℤ) G g h hgh))).toMul.val = ⁅x, y⁆ := by
  rw [centralHomologyEvaluation_torusCycle]
  exact MonoidHom.CentralKernel.commutator_eq_of_projection_eq p hc
    ((centralSection_projection p hp g).trans hx.symm)
    ((centralSection_projection p hp h).trans hy.symm)

/-- Sign-corrected evaluation, for geometric comparisons with negative ordered torus class. -/
def negativeCentralHomologyEvaluation :
    H2 (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) →ₗ[ULift.{u} ℤ]
      Additive (Subgroup.center H) :=
  -centralHomologyEvaluation p hp hc

/-- The sign-corrected evaluation still takes values in the actual projection kernel. -/
theorem negativeCentralHomologyEvaluation_projection
    (a : H2 (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ))) :
    p (negativeCentralHomologyEvaluation p hp hc a).toMul.val = 1 := by
  change p (-centralHomologyEvaluation p hp hc a).toMul.val = 1
  rw [← map_neg]
  exact centralHomologyEvaluation_projection p hp hc (-a)

/-- The sign-corrected native H-two homomorphism corestricted to the actual kernel. -/
def negativeCentralHomologyEvaluationToKernel :
    Multiplicative (H2 (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ))) →* p.ker where
  toFun a := ⟨(negativeCentralHomologyEvaluation p hp hc a.toAdd).toMul.val,
    negativeCentralHomologyEvaluation_projection p hp hc a.toAdd⟩
  map_one' := Subtype.ext (by
    change (negativeCentralHomologyEvaluation p hp hc 0).toMul.val = 1
    rw [map_zero]
    rfl)
  map_mul' a b := Subtype.ext (by
    change (negativeCentralHomologyEvaluation p hp hc (a.toAdd + b.toAdd)).toMul.val = _
    rw [map_add]
    rfl)

/-- Negative evaluation of the negative ordered class recovers the positive lift commutator. -/
theorem negativeCentralHomologyEvaluation_neg_torusCycle (g h : G) (hgh : Commute g h)
    (x y : H) (hx : p x = g) (hy : p y = h) :
    (negativeCentralHomologyEvaluation p hp hc
      (-H2π (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ))
        (torusCycle (ULift.{u} ℤ) G g h hgh))).toMul.val = ⁅x, y⁆ := by
  simpa only [negativeCentralHomologyEvaluation, LinearMap.neg_apply, map_neg, neg_neg] using
    centralHomologyEvaluation_torusCycle_of_lifts p hp hc g h hgh x y hx hy

/-- The actual kernel-valued detector has the same positive commutator normalization. -/
theorem negativeCentralHomologyEvaluationToKernel_neg_torusCycle
    (g h : G) (hgh : Commute g h) (x y : H) (hx : p x = g) (hy : p y = h) :
    (negativeCentralHomologyEvaluationToKernel p hp hc
      (Multiplicative.ofAdd (-H2π (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ))
        (torusCycle (ULift.{u} ℤ) G g h hgh)))).val = ⁅x, y⁆ :=
  negativeCentralHomologyEvaluation_neg_torusCycle p hp hc g h hgh x y hx hy

/-- An explicit native three-chain comparing both simultaneously inverted torus axes. -/
def torusInverseFiller (g h : G) : G × G × G →₀ ULift.{u} ℤ :=
  single (g, h, h⁻¹) 1 - single (h, g, h⁻¹) 1 + single (h, h⁻¹, g) 1 +
    (single (h⁻¹, g, g⁻¹) 1 - single (g, h⁻¹, g⁻¹) 1 + single (g, g⁻¹, h⁻¹) 1) +
      single (1, 1, g) 1 + single (g, 1, 1) 1 +
        single (1, 1, h⁻¹) 1 + single (h⁻¹, 1, 1) 1

/-- Its actual native boundary is the difference of the two ordered torus chains. -/
theorem torusInverseFiller_boundary (g h : G) (hgh : Commute g h) :
    d₃₂ (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ)) (torusInverseFiller g h) =
      (torusCycle (ULift.{u} ℤ) G g⁻¹ h⁻¹ hgh.inv_inv).val -
        (torusCycle (ULift.{u} ℤ) G g h hgh).val := by
  simp only [torusInverseFiller, map_add, map_sub]
  erw [d₃₂_single, d₃₂_single, d₃₂_single, d₃₂_single, d₃₂_single,
    d₃₂_single, d₃₂_single, d₃₂_single, d₃₂_single, d₃₂_single]
  change (single (h, h⁻¹) 1 - single (g * h, h⁻¹) 1 + single (g, h * h⁻¹) 1 -
      single (g, h) 1) -
    (single (g, h⁻¹) 1 - single (h * g, h⁻¹) 1 + single (h, g * h⁻¹) 1 -
      single (h, g) 1) +
    (single (h⁻¹, g) 1 - single (h * h⁻¹, g) 1 + single (h, h⁻¹ * g) 1 -
      single (h, h⁻¹) 1) +
    ((single (g, g⁻¹) 1 - single (h⁻¹ * g, g⁻¹) 1 + single (h⁻¹, g * g⁻¹) 1 -
        single (h⁻¹, g) 1) -
      (single (h⁻¹, g⁻¹) 1 - single (g * h⁻¹, g⁻¹) 1 + single (g, h⁻¹ * g⁻¹) 1 -
        single (g, h⁻¹) 1) +
      (single (g⁻¹, h⁻¹) 1 - single (g * g⁻¹, h⁻¹) 1 + single (g, g⁻¹ * h⁻¹) 1 -
        single (g, g⁻¹) 1)) +
    (single (1, g) 1 - single (1 * 1, g) 1 + single (1, 1 * g) 1 - single (1, 1) 1) +
    (single (1, 1) 1 - single (g * 1, 1) 1 + single (g, 1 * 1) 1 - single (g, 1) 1) +
    (single (1, h⁻¹) 1 - single (1 * 1, h⁻¹) 1 + single (1, 1 * h⁻¹) 1 - single (1, 1) 1) +
    (single (1, 1) 1 - single (h⁻¹ * 1, 1) 1 + single (h⁻¹, 1 * 1) 1 -
      single (h⁻¹, 1) 1) = _
  simp only [mul_inv_cancel, mul_one, one_mul, hgh.eq,
    hgh.inv_right.eq, hgh.inv_inv.eq, torusCycle]
  abel

/-- Simultaneous inversion preserves the ordered torus class in actual native H-two. -/
theorem H2π_torusCycle_inv_inv (g h : G) (hgh : Commute g h) :
    H2π (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ))
      (torusCycle (ULift.{u} ℤ) G g⁻¹ h⁻¹ hgh.inv_inv) =
    H2π (Rep.trivial (ULift.{u} ℤ) G (ULift.{u} ℤ))
      (torusCycle (ULift.{u} ℤ) G g h hgh) := by
  apply (H2π_eq_iff _ _).mpr
  exact ⟨torusInverseFiller g h, torusInverseFiller_boundary g h hgh⟩

end groupHomology
