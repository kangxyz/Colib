/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.LocalCoefficients.PeriodicSquare
public import Colib.Topology.LocalCoefficients.SingularBar
public import Colib.RepresentationTheory.Homological.GroupHomology.Torus

/-!
# Calibration of the oriented periodic square in original integral bar homology

Adapted from `Quillen/Topology/LocalCoefficients/SingularBarCalibration.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original chains, signs,
maps, basepoints and stated hypotheses are retained, using Mathlib's actual
standard simplex and native second group homology.
-/
@[expose] public section

section

open groupHomology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory Limits
open scoped Simplicial commutatorElement
namespace FundamentalGroupoid.LocalCoefficients.SingularBar
variable {P : Type u} [TopologicalSpace P]
open groupHomology

variable [PathConnectedSpace P]

/-- The first consecutive lower label is the inverse original horizontal axis class. -/
theorem lower_label01 (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) :
    label (σ (0, 0)) (lowerTriangle σ) 0 1 = (firstAxisClass σ hFirst)⁻¹ :=
  label_of_forwardPath _ _ _ _ (firstAxis σ hFirst) (lowerTriangle_edge01 σ)

/-- The second consecutive lower label is the inverse original vertical axis class. -/
theorem lower_label12 (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    label (σ (0, 0)) (lowerTriangle σ) 1 2 = (secondAxisClass σ hSecond)⁻¹ :=
  label_of_forwardPath _ _ _ _ (secondAxis σ hSecond)
    (fun t ↦ (lowerTriangle_edge12 σ t).trans (hFirst t).symm)

/-- The first consecutive upper label is the inverse original vertical axis class. -/
theorem upper_label01 (σ : C(unitInterval × unitInterval, P))
    (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    label (σ (0, 0)) (upperTriangle σ) 0 1 = (secondAxisClass σ hSecond)⁻¹ :=
  label_of_forwardPath _ _ _ _ (secondAxis σ hSecond) (upperTriangle_edge01 σ)

/-- The second consecutive upper label is the inverse original horizontal axis class. -/
theorem upper_label12 (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    label (σ (0, 0)) (upperTriangle σ) 1 2 = (firstAxisClass σ hFirst)⁻¹ :=
  label_of_forwardPath _ _ _ _ (firstAxis σ hFirst)
    (fun t ↦ (upperTriangle_edge12 σ t).trans (hSecond t).symm)

/-- Both diagonal labels are the inverse class of the same original diagonal path. -/
theorem diagonal_labels_eq (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    label (σ (0, 0)) (lowerTriangle σ) 0 2 = label (σ (0, 0)) (upperTriangle σ) 0 2 := by
  rw [label_of_forwardPath (σ (0, 0)) (lowerTriangle σ) 0 2
      (diagonalPath σ hFirst hSecond) (lowerTriangle_edge02 σ),
    label_of_forwardPath (σ (0, 0)) (upperTriangle σ) 0 2
      (diagonalPath σ hFirst hSecond) (upperTriangle_edge02 σ)]

/-- The original two axis classes commute, by their actual common simplex diagonal. -/
theorem axisClasses_commute (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    Commute (firstAxisClass σ hFirst) (secondAxisClass σ hSecond) := by
  have hl := label_mul (σ (0, 0)) (lowerTriangle σ) 0 1 2
  have hu := label_mul (σ (0, 0)) (upperTriangle σ) 0 1 2
  rw [lower_label01 σ hFirst, lower_label12 σ hFirst hSecond] at hl
  rw [upper_label01 σ hSecond, upper_label12 σ hFirst hSecond] at hu
  have hi : Commute (firstAxisClass σ hFirst)⁻¹ (secondAxisClass σ hSecond)⁻¹ :=
    hl.trans ((diagonal_labels_eq σ hFirst hSecond).trans hu.symm)
  simpa only [inv_inv] using hi.inv_inv

/-- The literal oriented chain maps to the simultaneous-inverse bar torus, with positive sign. -/
theorem twoMap_squareTwoChain (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    twoMap (σ (0, 0)) (squareTwoChain σ) =
      (torusCycle (ULift.{u} ℤ) (HomotopyGroup.Pi 1 P (σ (0, 0)))
        (firstAxisClass σ hFirst)⁻¹ (secondAxisClass σ hSecond)⁻¹
          (axisClasses_commute σ hFirst hSecond).inv_inv).val := by
  rw [squareTwoChain, map_sub, twoMap_inclusion, twoMap_inclusion,
    lower_label01 σ hFirst, lower_label12 σ hFirst hSecond,
    upper_label01 σ hSecond, upper_label12 σ hFirst hSecond]
  simp only [one_smul, torusCycle]

/-- The exact original square class maps to the positive original bar torus class of its axes. -/
theorem hTwoMap_squareTwoCycle (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1)) :
    hTwoMap (σ (0, 0))
      ((singularChainComplex (constant P integralCoefficients.{u})).homologyπ 2
        (squareTwoCycle σ hFirst hSecond)) =
      H2π (Rep.trivial (ULift.{u} ℤ) (HomotopyGroup.Pi 1 P (σ (0, 0))) (ULift.{u} ℤ))
        (torusCycle (ULift.{u} ℤ) (HomotopyGroup.Pi 1 P (σ (0, 0)))
          (firstAxisClass σ hFirst) (secondAxisClass σ hSecond)
            (axisClasses_commute σ hFirst hSecond)) := by
  rw [← H2π_torusCycle_inv_inv, hTwoMap_class]
  congr 1
  apply Subtype.ext
  rw [hTwoMap_cycle_val, iCycles_squareTwoCycle, twoMap_squareTwoChain]

/-- Negative central evaluation of the negative geometric square class recovers the
positive commutator of actual lifts of its ordered axes. -/
theorem negativeCentralEvaluation_neg_squareTwoCycle
    (σ : C(unitInterval × unitInterval, P))
    (hFirst : ∀ t, σ (0, t) = σ (1, t)) (hSecond : ∀ t, σ (t, 0) = σ (t, 1))
    {H : Type v} [Group H] (p : H →* HomotopyGroup.Pi 1 P (σ (0, 0)))
    (hp : Function.Surjective p) (hc : p.ker ≤ Subgroup.center H)
    (x y : H) (hx : p x = firstAxisClass σ hFirst) (hy : p y = secondAxisClass σ hSecond) :
    (negativeCentralHomologyEvaluationToKernel p hp hc
      (Multiplicative.ofAdd (hTwoMap (σ (0, 0))
        (-((singularChainComplex (constant P integralCoefficients.{u})).homologyπ 2
          (squareTwoCycle σ hFirst hSecond)))))).val = ⁅x, y⁆ := by
  rw [map_neg, hTwoMap_squareTwoCycle]
  exact negativeCentralHomologyEvaluationToKernel_neg_torusCycle p hp hc
    (firstAxisClass σ hFirst) (secondAxisClass σ hSecond)
      (axisClasses_commute σ hFirst hSecond) x y hx hy

end FundamentalGroupoid.LocalCoefficients.SingularBar

end
