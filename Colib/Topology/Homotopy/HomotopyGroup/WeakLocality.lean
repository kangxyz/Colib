/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.ControlledWeakCharts
public import Colib.Topology.CubicalSubdivision.LocalLifting
public import Colib.Topology.HELP.StrictFiniteCriterion

/-! # Ordinary weak equivalences from genuine open target charts

Weakness is required on every nonempty finite intersection of the target
charts. This includes the overlap in the two-open theorem. Ordinary mapping
paths are controlled throughout their complete tracks before finite face
pasting, so endpoint-only restriction is never used.


Implementation provenance:
`Quillen/Topology/HomotopyGroups/WeakLocality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology
open CubicalSubdivision
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B]

/-- Removing the vacuous source constraints identifies the actual controlled
chart map with the original pullback restriction, retaining its forward map. -/
theorem controlledChartMap_univ_isWeakHomotopyEquivalence (p : C(E, B))
    {J : Type v} (W : J → Set B) (S : Finset J)
    (h : IsWeakHomotopyEquivalence (restriction p {b | ∀ j ∈ S,b ∈ W j})) :
    IsWeakHomotopyEquivalence (controlledChartMap p (fun _ ↦ Set.univ) W S) := by
  let e : {x : E // ∀ j ∈ S,x ∈ (Set.univ : Set E) ∧ p x ∈ W j} ≃ₜ
      {x : E // p x ∈ {b | ∀ j ∈ S,b ∈ W j}} := {
    toFun x := ⟨x.val,fun j hj ↦ (x.property j hj).2⟩
    invFun x := ⟨x.val,fun j hj ↦ ⟨Set.mem_univ _,x.property j hj⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  exact h.comp (isWeakHomotopyEquivalence_of_homotopyEquiv e.toHomotopyEquiv)

/-- The original map is a complete weak homotopy equivalence when its literal
pullback restrictions are weak on all nonempty finite target-chart intersections.
Neither openness of source charts nor a global continuous inverse is assumed. -/
theorem isWeakHomotopyEquivalence_of_open_cover (p : C(E, B))
    {J : Type v} (W : J → Set B) (hW : ∀ j, IsOpen (W j))
    (hcover : ∀ b : B,∃ j,b ∈ W j)
    (hloc : ∀ S : Finset J,S.Nonempty →
      IsWeakHomotopyEquivalence (restriction p {b | ∀ j ∈ S,b ∈ W j})) :
    IsWeakHomotopyEquivalence p := by
  apply FiniteCubeStrictHELP.isWeakHomotopyEquivalence
  intro n a b hab
  let a' : C(Boundary n,E) := {
    toFun x := a ⟨⟨x.val⟩,x.property⟩
    continuous_toFun := by fun_prop }
  let b' : C(Cube n,B) := ⟨fun x ↦ b ⟨x⟩,by fun_prop⟩
  have hab' : ∀ x : Boundary n,p (a' x) = b' x.val :=
    fun x ↦ ContinuousMap.congr_fun hab ⟨⟨x.val⟩,x.property⟩
  obtain ⟨c,hc,⟨K⟩⟩ := exists_strictHELP_of_controlled_weak_chart_cover p
    (fun _ ↦ Set.univ) W
    (fun S hS ↦ controlledChartMap_univ_isWeakHomotopyEquivalence p W S (hloc S hS))
    n a' b' hab' (fun j ↦ b' ⁻¹' W j)
    (fun j ↦ (hW j).preimage b'.continuous) (fun x ↦ hcover (b' x))
    (fun _ _ hx ↦ hx) (fun _ _ _ ↦ Set.mem_univ _)
  let c' : C(CubicalTests.cube.{u} n,E) := ⟨fun x ↦ c x.down,by fun_prop⟩
  refine ⟨c',?_,⟨{ toHomotopy := {
    toFun z := K (z.1,z.2.down)
    continuous_toFun := by fun_prop
    map_zero_left x := K.toHomotopy.map_zero_left x.down
    map_one_left x := K.toHomotopy.map_one_left x.down },prop' := ?_ }⟩⟩
  · ext x
    exact hc ⟨x.val.down,x.property⟩
  · rintro t x ⟨z,rfl⟩
    exact K.prop t z.val.down z.property

/-- Two genuine open target charts glue ordinary weak equivalences when the
literal overlap restriction is also weak. The overlap may be empty. -/
theorem isWeakHomotopyEquivalence_of_two_open (p : C(E, B))
    (U V : Set B) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ)
    (h0 : IsWeakHomotopyEquivalence (restriction p U))
    (h1 : IsWeakHomotopyEquivalence (restriction p V))
    (h01 : IsWeakHomotopyEquivalence (restriction p (U ∩ V))) :
    IsWeakHomotopyEquivalence p := by
  let W : Bool → Set B := fun j ↦ if j then U else V
  apply isWeakHomotopyEquivalence_of_open_cover p W
    (fun j ↦ by
      cases j with
      | false => exact hV
      | true => exact hU)
  · intro b
    have hb : b ∈ U ∪ V := by rw [hcover]; trivial
    rcases hb with hb | hb
    · exact ⟨true,hb⟩
    · exact ⟨false,hb⟩
  · intro S hS
    by_cases ht : true ∈ S
    · by_cases hf : false ∈ S
      · have hset : {b : B | ∀ j ∈ S,b ∈ W j} = U ∩ V := by
          ext b
          constructor
          · intro h
            exact ⟨h true ht,h false hf⟩
          · intro h j hj
            cases j
            · exact h.2
            · exact h.1
        rw [hset]
        exact h01
      · have hset : {b : B | ∀ j ∈ S,b ∈ W j} = U := by
          ext b
          constructor
          · exact fun h ↦ h true ht
          · intro h j hj
            cases j
            · exact False.elim (hf hj)
            · exact h
        rw [hset]
        exact h0
    · have hf : false ∈ S := by
        obtain ⟨j,hj⟩ := hS
        cases j
        · exact hj
        · exact False.elim (ht hj)
      have hset : {b : B | ∀ j ∈ S,b ∈ W j} = V := by
        ext b
        constructor
        · exact fun h ↦ h false hf
        · intro h j hj
          cases j
          · exact h
          · exact False.elim (ht hj)
      rw [hset]
      exact h1

end Topology
