/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References

public import Colib.Topology.Homotopy.HomotopyGroup.Contractible
public import Colib.Topology.HomotopyFiber.LESTail

/-!
# Unbased homotopy equivalences induce canonical based isomorphisms

Only the forward map is required to preserve the stated points. The inverse
and its homotopies may move them. Contractibility of the concrete homotopy
fiber and exactness, including the pointed-set tail at degree one, prove
bijectivity of the canonical postcomposition map.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/Equivalence.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space models,
basepoint tracks, maps and universe parameters are retained. -/
@[expose] public section

noncomputable section
universe u v
namespace Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  {x : X} {y : Y}

/-- Contractibility of the actual fiber implies bijectivity of the canonical
map on every positive-dimensional homotopy group. -/
theorem piMap_bijective_of_contractible_fiber (f : C(X, Y)) (h : f x = y)
    [ContractibleSpace (HomotopyFiber f y)] (n : ℕ) :
    Function.Bijective (HomotopyGroup.piMap n f h) := by
  constructor
  · apply (injective_iff_map_eq_one (HomotopyGroup.piMap n f h)).mpr
    intro a ha
    obtain ⟨b, hb⟩ :=
      (HomotopyFiber.mem_range_projection_iff f y x h a).mpr ha
    rw [pi_eq_one_of_contractible (HomotopyFiber.basepoint f y x h) n b,
      map_one] at hb
    exact hb.symm
  · intro a
    apply (HomotopyFiber.mem_range_piMap_iff_connectingMap_constant f y x h n a).mpr
    let := subsingleton_pi_of_contractible n (HomotopyFiber f y)
      (HomotopyFiber.basepoint f y x h)
    exact Subsingleton.elim _ _

/-- An unbased homotopy equivalence induces a bijection by its actual forward
map, for any equality identifying the image of the source basepoint. -/
theorem piMap_bijective_of_homotopyEquiv (e : ContinuousMap.HomotopyEquiv X Y)
    (h : e.toFun x = y) (n : ℕ) : Function.Bijective (HomotopyGroup.piMap n e.toFun h) := by
  let := HomotopyFiber.contractibleSpace_homotopyEquiv e y
  exact piMap_bijective_of_contractible_fiber e.toFun h n

/-- The canonical based homotopy-group isomorphism of an unbased equivalence.
Its forward map is exactly postcomposition by the equivalence's forward map. -/
def homotopyEquivPiEquiv (e : ContinuousMap.HomotopyEquiv X Y)
    (h : e.toFun x = y) (n : ℕ) :
    HomotopyGroup.Pi (n + 1) X x ≃* HomotopyGroup.Pi (n + 1) Y y :=
  MulEquiv.ofBijective (HomotopyGroup.piMap n e.toFun h) (piMap_bijective_of_homotopyEquiv e h n)

@[simp]
theorem homotopyEquivPiEquiv_apply (e : ContinuousMap.HomotopyEquiv X Y)
    (h : e.toFun x = y) (n : ℕ) (a : HomotopyGroup.Pi (n + 1) X x) :
    homotopyEquivPiEquiv e h n a = HomotopyGroup.piMap n e.toFun h a := rfl

/-- The forward homomorphism is postcomposition by the equivalence. -/
@[simp] theorem homotopyEquivPiEquiv_coe (e : ContinuousMap.HomotopyEquiv X Y)
    (h : e.toFun x = y) (n : ℕ) :
    (homotopyEquivPiEquiv e h n : _ →* _) = HomotopyGroup.piMap n e.toFun h := rfl

end Topology

attribute [colib_tag "COL-0217",
  colib_ref "HatcherAT" "Section 4.1, Exercise 2, page 358"
    "adaptation"
    "Actual forward piMap of an unbased equivalence, with only its forward basepoint equality"]
  Topology.piMap_bijective_of_homotopyEquiv
  Topology.homotopyEquivPiEquiv
  Topology.homotopyEquivPiEquiv_coe
