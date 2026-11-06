/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.LESTail
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceProperty

/-! # Weakly contractible homotopy fibers from the actual long exact sequence

Both directions use the original projection and connecting maps. The first
lemma includes the zeroth pointed homotopy set, without introducing a group
structure on connected components.


Implementation provenance:
`Quillen/Topology/HomotopyFiber/WeakContractibility.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (y : Y) (x : X) (h : f x = y)

/-- Injectivity in degree n and surjectivity in degree n+1 make the actual
fiber's degree-n pointed homotopy set a singleton, including n = 0. -/
theorem subsingleton_homotopyGroup_of_adjacent (n : ℕ)
    (hinj : Function.Injective (HomotopyGroup.map (N := Fin n) f h))
    (hsurj : Function.Surjective (HomotopyGroup.map (N := Fin (n + 1)) f h)) :
    Subsingleton (HomotopyGroup.Pi n (HomotopyFiber f y) (basepoint f y x h)) := by
  have hall (a : HomotopyGroup.Pi n (HomotopyFiber f y) (basepoint f y x h)) :
      a = Quotient.mk' GenLoop.const := by
    have hp : HomotopyGroup.map (projection f y) (projection_basepoint f y x h) a =
        (Quotient.mk' GenLoop.const : HomotopyGroup.Pi n X x) := by
      apply hinj
      exact ((mem_range_projection_iff_constant f y x h _).1 ⟨a, rfl⟩).trans
        (congrArg Quotient.mk' (GenLoop.postcomp_const f h)).symm
    obtain ⟨b, hb⟩ := (mem_range_connectingMap_iff_constant f y x h n a).2 hp
    exact hb.symm.trans ((mem_range_piMap_iff_connectingMap_constant f y x h n b).1
      (hsurj b))
  exact ⟨fun a b => (hall a).trans (hall b).symm⟩

/-- A weak equivalence has singleton finite homotopy sets on the actual fiber
at its constant-path point. -/
theorem subsingleton_homotopyGroup_of_weakEquivalence
    (hf : IsWeakHomotopyEquivalence f) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi n (HomotopyFiber f (f x))
      (basepoint f (f x) x rfl)) :=
  subsingleton_homotopyGroup_of_adjacent f (f x) x rfl n
    (hf.homotopy_bijective x n).injective (hf.homotopy_bijective x (n + 1)).surjective

/-- The zero-degree conclusion gives genuine path connectedness of the
actual fiber, rather than only higher-group vanishing. -/
theorem pathConnectedSpace_of_adjacent
    (hinj : Function.Injective (HomotopyGroup.map (N := Fin 0) f h))
    (hsurj : Function.Surjective (HomotopyGroup.map (N := Fin 1) f h)) :
    PathConnectedSpace (HomotopyFiber f y) := by
  let := subsingleton_homotopyGroup_of_adjacent f y x h 0 hinj hsurj
  let : Subsingleton (ZerothHomotopy (HomotopyFiber f y)) :=
    (HomotopyGroup.pi0EquivZerothHomotopy
      (X := HomotopyFiber f y) (x := basepoint f y x h)).symm.injective.subsingleton
  exact pathConnectedSpace_iff_zerothHomotopy.2
    ⟨⟨ZerothHomotopy.mk (basepoint f y x h)⟩, inferInstance⟩

/-- The converse positive-degree test uses the two adjacent actual fiber
homotopy sets; its surjectivity argument includes the pointed-set LES tail. -/
theorem piMap_bijective_of_subsingleton_fiber (n : ℕ)
    [Subsingleton (HomotopyGroup.Pi (n + 1) (HomotopyFiber f y) (basepoint f y x h))]
    [Subsingleton (HomotopyGroup.Pi n (HomotopyFiber f y) (basepoint f y x h))] :
    Function.Bijective (HomotopyGroup.piMap n f h) := by
  constructor
  · apply (injective_iff_map_eq_one (HomotopyGroup.piMap n f h)).2
    intro a ha
    obtain ⟨b, hb⟩ := (mem_range_projection_iff f y x h a).2 ha
    have hbone : b = 1 := Subsingleton.elim _ _
    rw [hbone, map_one] at hb
    exact hb.symm
  · intro a
    exact (mem_range_piMap_iff_connectingMap_constant f y x h n a).2
      (Subsingleton.elim _ _)

end Topology.HomotopyFiber
