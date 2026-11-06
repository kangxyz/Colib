/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransport

/-! # Two-of-three for the original empty-aware weak equivalences

The component clauses are proved with actual paths. Cancellation never
replaces them by vacuous based conditions on an empty source.


Implementation provenance:
`Quillen/Topology/HomotopyGroups/WeakEquivalenceCancellation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open scoped Topology unitInterval
universe u v w
namespace Topology
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Injectivity of the original zero-dimensional homotopy map reflects
actual path components at every pair of source points. -/
theorem joined_of_homotopyGroupMap_zero_injective (f : C(X, Y)) (x₀ x₁ : X)
    (hf : Function.Injective (HomotopyGroup.map (N := Fin 0) f (x := x₀) rfl))
    (h : Joined (f x₀) (f x₁)) : Joined x₀ x₁ := by
  let a : GenLoop (Fin 0) X x₀ := GenLoop.const
  let b : GenLoop (Fin 0) X x₀ :=
    ⟨ContinuousMap.const _ x₁, by rintro t ⟨i, _⟩; exact Fin.elim0 i⟩
  let γ := h.somePath
  have he : HomotopyGroup.map f (x := x₀) rfl (Quotient.mk' a) =
      HomotopyGroup.map f (x := x₀) rfl (Quotient.mk' b) := by
    apply Quotient.sound
    exact ⟨{
      toFun z := γ z.1
      continuous_toFun := by fun_prop
      map_zero_left _ := γ.source
      map_one_left _ := γ.target
      prop' := by rintro t s ⟨i, _⟩; exact Fin.elim0 i }⟩
  obtain ⟨H⟩ := Quotient.exact (hf he)
  exact ⟨H.toHomotopy.evalAt 0⟩

/-- Cancel the first map using its actual component surjectivity and all-degree
bijections. The result applies at every target-source point. -/
theorem IsWeakHomotopyEquivalence.of_comp_left {f : C(X, Y)} {g : C(Y, Z)}
    (hgf : IsWeakHomotopyEquivalence (g.comp f))
    (hf : IsWeakHomotopyEquivalence f) : IsWeakHomotopyEquivalence g where
  component_surjective z := by
    obtain ⟨x, hx⟩ := hgf.component_surjective z
    exact ⟨f x, hx⟩
  homotopy_bijective y n := by
    obtain ⟨x, hx⟩ := hf.component_surjective y
    apply (homotopyGroupMap_bijective_iff_of_joined g hx n).1
    have hcomp : Function.Bijective
        ((HomotopyGroup.map (N := Fin n) g (x := f x) rfl) ∘
          (HomotopyGroup.map (N := Fin n) f (x := x) rfl)) := by
      simpa only [Function.comp_def, ← HomotopyGroup.map_comp] using hgf.homotopy_bijective x n
    exact ⟨fun a b hab => by
      obtain ⟨a', rfl⟩ := (hf.homotopy_bijective x n).surjective a
      obtain ⟨b', rfl⟩ := (hf.homotopy_bijective x n).surjective b
      exact congrArg _ (hcomp.injective hab),
      fun z => by obtain ⟨a, ha⟩ := hcomp.surjective z; exact ⟨_, ha⟩⟩

/-- Cancel the second map. Its actual zero-dimensional injectivity supplies
the component-surjectivity clause for the first map. -/
theorem IsWeakHomotopyEquivalence.of_comp_right {f : C(X, Y)} {g : C(Y, Z)}
    (hgf : IsWeakHomotopyEquivalence (g.comp f))
    (hg : IsWeakHomotopyEquivalence g) : IsWeakHomotopyEquivalence f where
  component_surjective y := by
    obtain ⟨x, hx⟩ := hgf.component_surjective (g y)
    exact ⟨x, joined_of_homotopyGroupMap_zero_injective g (f x) y
      (hg.homotopy_bijective (f x) 0).injective hx⟩
  homotopy_bijective x n := by
    have hcomp : Function.Bijective
        ((HomotopyGroup.map (N := Fin n) g (x := f x) rfl) ∘
          (HomotopyGroup.map (N := Fin n) f (x := x) rfl)) := by
      simpa only [Function.comp_def, ← HomotopyGroup.map_comp] using hgf.homotopy_bijective x n
    exact ⟨fun _ _ hab => hcomp.injective (congrArg (HomotopyGroup.map (N := Fin n) g (x := f x)
      rfl) hab), fun y => by
      obtain ⟨a, ha⟩ := hcomp.surjective
        (HomotopyGroup.map (N := Fin n) g (x := f x) rfl y)
      exact ⟨a, (hg.homotopy_bijective (f x) n).injective ha⟩⟩

end Topology
