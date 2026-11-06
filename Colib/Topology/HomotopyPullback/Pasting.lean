/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.SourceEquivalence
public import Colib.Topology.HomotopyPullback.Fibration

/-!
# Pasting path-space homotopy pullbacks

The explicit comparison for pasted path-space homotopy pullbacks is a homotopy equivalence under
    the stated hypotheses.
-/
/-! Implementation source: `Quillen/Topology/HomotopyPullback/Pasting.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual compact-open path topology,
parameter spaces and canonical forward maps are retained. -/
@[expose] public section


noncomputable section
universe u
open scoped Topology unitInterval
namespace Topology.HomotopyPullback
variable {X₀ X₁ X₂ B₀ B₁ B₂ : Type u}
  [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
  [TopologicalSpace B₀] [TopologicalSpace B₁] [TopologicalSpace B₂]
  (p₀ : C(X₀, B₀)) (p₁ : C(X₁, B₁)) (p₂ : C(X₂, B₂))
  (a : C(X₀, X₁)) (a' : C(X₁, X₂)) (b : C(B₀, B₁)) (b' : C(B₁, B₂))
  (w : p₁.comp a = b.comp p₀) (w' : p₂.comp a' = b'.comp p₁)

include w w' in
theorem pasteSquare : p₂.comp (a'.comp a) = (b'.comp b).comp p₀ := by
  ext x
  exact (ContinuousMap.congr_fun w' (a x)).trans (congrArg b' (ContinuousMap.congr_fun w x))

/-- Pulling back the base projection of a homotopy pullback just composes
its base map, with its complete compact-open path coordinate unchanged. -/
def pastingStrictHomeomorph :
    HomotopyPullback p₂ (b'.comp b) ≃ₜ
      {z : B₀ × HomotopyPullback p₂ b' // baseProjection p₂ b' z.2 = b z.1} where
  toFun z := ⟨(z.1.1, ⟨(b z.1.1, z.1.2), z.2⟩), rfl⟩
  invFun z := ⟨(z.1.1, z.1.2.1.2), z.1.2.2.1,
    z.1.2.2.2.trans (congrArg b' z.2)⟩
  left_inv _ := rfl
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Prod.ext
      · exact z.2.symm
      · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The exact composite pullback embeds by constant outer paths into the
iterated homotopy pullback, and this map is an actual HE. -/
def pastingIntoNestedEquiv :
    ContinuousMap.HomotopyEquiv (HomotopyPullback p₂ (b'.comp b))
      (HomotopyPullback (baseProjection p₂ b') b) :=
  (pastingStrictHomeomorph p₂ b b').toHomotopyEquiv.trans
    (strictPullbackHomotopyEquivOfLifting (baseProjection p₂ b') b
      (baseProjection_homotopyLiftingProperty p₂ b'))

/-- Recover a homotopy equivalence with forward map `f` from its specified postcomposition. -/
def equivalenceOfPostcomposition {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (e : ContinuousMap.HomotopyEquiv Y Z) (t : ContinuousMap.HomotopyEquiv X Z)
    (f : C(X, Y)) (h : e.toFun.comp f = t.toFun) : ContinuousMap.HomotopyEquiv X Y :=
  HomotopyFiber.replaceForward (t.trans e.symm) f (by
    have H := e.left_inv.comp (ContinuousMap.Homotopic.refl f)
    rw [ContinuousMap.comp_assoc, h] at H
    exact H.symm)

/-- Two actual homotopy-cartesian squares paste to an actual
homotopy-cartesian square, with precisely the canonical comparison. -/
def pastingHomotopyEquiv
    (e : ContinuousMap.HomotopyEquiv X₀ (HomotopyPullback p₁ b))
    (he : e.toFun = comparison p₁ b p₀ a w)
    (e' : ContinuousMap.HomotopyEquiv X₁ (HomotopyPullback p₂ b'))
    (he' : e'.toFun = comparison p₂ b' p₁ a' w') :
    ContinuousMap.HomotopyEquiv X₀ (HomotopyPullback p₂ (b'.comp b)) := by
  let E' : ContinuousMap.HomotopyEquiv X₁ (HomotopyPullback p₂ b') := {
    e' with toFun := comparison p₂ b' p₁ a' w'
            left_inv := by simpa only [he'] using e'.left_inv
            right_inv := by simpa only [he'] using e'.right_inv }
  let S : ContinuousMap.HomotopyEquiv (HomotopyPullback p₁ b)
      (HomotopyPullback (baseProjection p₂ b') b) :=
    sourceEquiv b (baseProjection p₂ b') E'
  let J := pastingIntoNestedEquiv p₂ b b'
  let f := comparison p₂ (b'.comp b) p₀ (a'.comp a) (pasteSquare p₀ p₁ p₂ a a' b b' w w')
  apply equivalenceOfPostcomposition J (e.trans S) f
  apply ContinuousMap.ext
  intro x
  rw [ContinuousMap.comp_apply]
  change J.toFun (f x) = S.toFun (e.toFun x)
  rw [he]
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact (ContinuousMap.congr_fun w x).symm
      · apply Prod.ext
        · rfl
        · apply ContinuousMap.ext
          intro t
          exact congrArg b' (ContinuousMap.congr_fun w x).symm
    · rfl

@[simp] theorem pastingHomotopyEquiv_toFun
    (e : ContinuousMap.HomotopyEquiv X₀ (HomotopyPullback p₁ b))
    (he : e.toFun = comparison p₁ b p₀ a w)
    (e' : ContinuousMap.HomotopyEquiv X₁ (HomotopyPullback p₂ b'))
    (he' : e'.toFun = comparison p₂ b' p₁ a' w') :
    (pastingHomotopyEquiv p₀ p₁ p₂ a a' b b' w w' e he e' he').toFun =
      comparison p₂ (b'.comp b) p₀ (a'.comp a) (pasteSquare p₀ p₁ p₂ a a' b b' w w') := rfl

end Topology.HomotopyPullback

end
