/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.RelativeCylinder
public import Mathlib.Topology.Homotopy.HSpaces
public import Mathlib.Topology.Homotopy.Path

/-! Correcting the restriction of a homotopy while preserving both global
endpoints, using the proved interval-square extension theorem. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyFiber/BoundaryCorrection.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps, homotopies,
hypotheses and universes are retained; imports use native lower owners. -/
@[expose] public section

noncomputable section
universe u
open TopCat Topology CategoryTheory
open scoped Topology unitInterval
open unitInterval
namespace TopCat
variable {A B Z : TopCat.{u}} {i : A ⟶ B}

/-- A relative deformation of the boundary homotopy extends to the entire
homotopy, with both original endpoint maps unchanged. -/
theorem homotopyExtensionProperty_correct_boundary
    (hi : TopCat.HomotopyExtensionProperty i) {f g : C(B, Z)}
    (K : f.Homotopy g) (L : (f.comp i.hom).Homotopy (g.comp i.hom))
    (Q : (K.compContinuousMap i.hom).toContinuousMap.HomotopyRel L.toContinuousMap
      {z : unitInterval × A | z.1 = 0 ∨ z.1 = 1}) :
    ∃ K' : f.Homotopy g, ∀ t a, K' (t, i a) = L (t, a) := by
  let F : C(B × unitInterval, Z) := K.toContinuousMap.comp ContinuousMap.prodSwap
  let R : C((A × unitInterval) × unitInterval, Z) :=
    ⟨fun z ↦ Q (z.2, (z.1.2, z.1.1)), by fun_prop⟩
  let R₀ : C(B × unitInterval, Z) := f.comp ContinuousMap.fst
  let R₁ : C(B × unitInterval, Z) := g.comp ContinuousMap.fst
  obtain ⟨S, hS, hSA, hS₀, hS₁⟩ := TopCat.homotopyExtensionProperty_interval_square_extension
    hi F R R₀ R₁ (fun a t ↦ Q.map_zero_left (t, a))
    (fun b ↦ (K.map_zero_left b).symm) (fun b ↦ (K.map_one_left b).symm)
    (fun a t ↦ (Q.prop t (0, a) (Or.inl rfl)).trans (K.map_zero_left (i a)))
    (fun a t ↦ (Q.prop t (1, a) (Or.inr rfl)).trans (K.map_one_left (i a)))
  refine ⟨{
    toFun z := S ((z.2, z.1), 1)
    continuous_toFun := by fun_prop
    map_zero_left := fun b ↦ hS₀ b 1
    map_one_left := fun b ↦ hS₁ b 1 }, ?_⟩
  intro t a
  exact (hSA a t 1).trans (Q.map_one_left (t,a))

/-- In particular, a constant prefix on the boundary may be removed exactly
without changing the two endpoint maps anywhere in the ambient space. -/
theorem homotopyExtensionProperty_unpad_boundary
    (hi : TopCat.HomotopyExtensionProperty i) {f g : C(B, Z)}
    (K : f.Homotopy g) (L : (f.comp i.hom).Homotopy (g.comp i.hom))
    (hK : ∀ t a, K (t, i a) = Path.delayReflLeft 0 (L.evalAt a) t) :
    ∃ K' : f.Homotopy g, ∀ t a, K' (t, i a) = L (t,a) := by
  apply TopCat.homotopyExtensionProperty_correct_boundary hi K L
  refine {
    toFun z := Path.delayReflLeft z.1 (L.evalAt z.2.2) z.2.1
    continuous_toFun := ?_
    map_zero_left := fun z ↦ (hK z.1 z.2).symm
    map_one_left := ?_
    prop' := ?_ }
  · change Continuous (fun z : unitInterval × (unitInterval × A) ↦
      L (unitInterval.symm (qRight (unitInterval.symm z.2.1, z.1)), z.2.2))
    fun_prop
  · intro z
    change Path.delayReflLeft 1 (L.evalAt z.2) z.1 = L (z.1,z.2)
    rw [Path.delayReflLeft_one]
    rfl
  · intro s z hz
    rcases z with ⟨t,a⟩
    rcases hz with ht | ht
    · change t = 0 at ht
      subst t
      change Path.delayReflLeft s (L.evalAt a) 0 = K (0,i a)
      exact (Path.source (Path.delayReflLeft s (L.evalAt a))).trans (K.map_zero_left (i a)).symm
    · change t = 1 at ht
      subst t
      change Path.delayReflLeft s (L.evalAt a) 1 = K (1,i a)
      exact (Path.target (Path.delayReflLeft s (L.evalAt a))).trans (K.map_one_left (i a)).symm

end TopCat
