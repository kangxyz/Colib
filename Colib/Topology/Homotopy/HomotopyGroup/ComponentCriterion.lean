/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceCancellation

/-! # Actual component paths and the original zeroth homotopy map

Implementation provenance:
`Quillen/Topology/HomotopyGroups/ComponentCriterion.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
universe u v
namespace Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Surjectivity and reflection of actual component paths give precisely the
original finite-zero homotopy-set bijection, without a group on components. -/
theorem homotopyGroupMap_zero_bijective_of_components (f : C(X, Y))
    (hsurj : ∀ y, ∃ x, Joined (f x) y)
    (hinj : ∀ x₀ x₁, Joined (f x₀) (f x₁) → Joined x₀ x₁) (x : X) :
    Function.Bijective (HomotopyGroup.map (N := Fin 0) f (x := x) rfl) := by
  constructor
  · intro a b h
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        obtain ⟨H⟩ := Quotient.exact h
        let γ := (hinj (a 0) (b 0) ⟨H.toHomotopy.evalAt 0⟩).somePath
        apply Quotient.sound
        exact ⟨{
          toFun z := γ z.1
          continuous_toFun := by fun_prop
          map_zero_left s := γ.source.trans (congrArg a (Subsingleton.elim 0 s))
          map_one_left s := γ.target.trans (congrArg b (Subsingleton.elim 0 s))
          prop' := by rintro t s ⟨i, _⟩; exact Fin.elim0 i }⟩
  · intro b
    induction b using Quotient.inductionOn with | h b =>
      obtain ⟨a, ha⟩ := hsurj (b 0)
      let γ := ha.somePath
      let q : GenLoop (Fin 0) X x :=
        ⟨ContinuousMap.const _ a, by rintro t ⟨i, _⟩; exact Fin.elim0 i⟩
      refine ⟨Quotient.mk' q, Quotient.sound ⟨?_⟩⟩
      exact {
        toFun z := γ z.1
        continuous_toFun := by fun_prop
        map_zero_left _ := γ.source
        map_one_left s := γ.target.trans (congrArg b (Subsingleton.elim 0 s))
        prop' := by rintro t s ⟨i, _⟩; exact Fin.elim0 i }

end Topology
