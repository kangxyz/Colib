/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty
public import Colib.Topology.Homotopy.FreePath

/-!
# Homotopy invariance of empty-aware weak equivalences

An actual homotopy is curried into the compact-open free path space. Both endpoint
maps are actual homotopy equivalences. Cancelling the initial evaluation and
composing the final evaluation proves invariance on all finite homotopy sets,
including degree zero. Component surjectivity is transported by the same actual
pointwise paths. No homotopy-fiber criterion or nonempty-source assumption is used.
-/

@[expose] public noncomputable section

open scoped Topology unitInterval
universe u v

namespace Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- An arbitrary homotopy preserves bijectivity at a specified source point,
allowing the target basepoint to follow its actual endpoint values. -/
theorem homotopyGroupMap_bijective_of_homotopy {f g : C(X, Y)}
    (H : f.Homotopy g) (x : X) (n : ℕ)
    (hf : Function.Bijective (HomotopyGroup.map (N := Fin n) f (x := x) rfl)) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) g (x := x) rfl) := by
  let K : C(X, C(unitInterval, Y)) := ⟨fun a ↦ ⟨fun t ↦ H (t, a), by fun_prop⟩, by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : X × unitInterval ↦ H (z.2, z.1))
    fun_prop⟩
  let μ := HomotopyGroup.map (N := Fin n) K (x := x) rfl
  let ν₀ := HomotopyGroup.map (N := Fin n) (freePathEvaluation Y 0)
    (x := K x) (H.map_zero_left x)
  let ν₁ := HomotopyGroup.map (N := Fin n) (freePathEvaluation Y 1)
    (x := K x) (H.map_one_left x)
  have hν₀ : Function.Bijective ν₀ :=
    homotopyGroupMap_bijective_of_homotopyEquiv (freePathEvaluationHomotopyEquiv Y 0)
      (H.map_zero_left x) n
  have hν₁ : Function.Bijective ν₁ :=
    homotopyGroupMap_bijective_of_homotopyEquiv (freePathEvaluationHomotopyEquiv Y 1)
      (H.map_one_left x) n
  have h₀ : HomotopyGroup.map (N := Fin n) f (x := x) rfl = ν₀ ∘ μ := by
    funext a
    refine Quotient.inductionOn a (fun p ↦ ?_)
    apply congrArg Quotient.mk'
    apply GenLoop.ext
    intro t
    exact (H.map_zero_left (p t)).symm
  have h₁ : HomotopyGroup.map (N := Fin n) g (x := x) rfl = ν₁ ∘ μ := by
    funext a
    refine Quotient.inductionOn a (fun p ↦ ?_)
    apply congrArg Quotient.mk'
    apply GenLoop.ext
    intro t
    exact (H.map_one_left (p t)).symm
  have hμ : Function.Bijective μ := by
    constructor
    · intro a b hab
      apply hf.injective
      rw [h₀]
      exact congrArg ν₀ hab
    · intro b
      obtain ⟨a, ha⟩ := hf.surjective (ν₀ b)
      refine ⟨a, hν₀.injective ?_⟩
      exact (congrFun h₀ a).symm.trans ha
  rw [h₁]
  exact hν₁.comp hμ

/-- Unbased homotopies preserve the original empty-aware weak equivalence. -/
theorem IsWeakHomotopyEquivalence.of_homotopy {f g : C(X, Y)}
    (hf : IsWeakHomotopyEquivalence f) (H : f.Homotopy g) :
    IsWeakHomotopyEquivalence g where
  component_surjective y := by
    obtain ⟨x, hx⟩ := hf.component_surjective y
    exact ⟨x, (Joined.symm ⟨H.evalAt x⟩).trans hx⟩
  homotopy_bijective x n := homotopyGroupMap_bijective_of_homotopy H x n
    (hf.homotopy_bijective x n)

end Topology
