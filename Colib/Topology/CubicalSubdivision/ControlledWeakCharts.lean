/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.ControlledChartLifting
public import Colib.Topology.HELP.WeakFinite

/-! # Finite controlled HELP from ordinary weak chart maps

Every incident source constraint and every value of each stored comparison
path is retained. Local weak equivalences are used only through their proved
finite mapping-path endpoint lifting. The resulting comparison homotopy is
ordinary, with the complete original boundary fixed; it is not asserted vertical.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/ControlledWeakCharts.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
namespace Topology.CubicalSubdivision
universe u v
variable {E B : Type u} {J : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- A chart of ordinary mapping paths retains the source constraint and
membership of the entire stored path, not only its terminal endpoint. -/
def mappingPathChartSet (p : C(E, B)) (R : J → Set E) (W : J → Set B)
    (j : J) : Set (MappingPath p) :=
  {z | z.val.1 ∈ R j ∧ ∀ t : unitInterval,z.val.2 t ∈ W j}

/-- The genuine endpoint of the original weak restricted map fills every
finite boundary test with all original path coordinates unchanged. -/
theorem controlled_mappingPath_chart_boundaryLifting (p : C(E, B))
    (R : J → Set E) (W : J → Set B) (S : Finset J)
    (hf : IsWeakHomotopyEquivalence (controlledChartMap p R W S)) :
    BoundaryLifting (controlledChartMap (MappingPath.endpoint p)
      (mappingPathChartSet p R W) W S) := by
  intro n a b hab
  let q := controlledChartMap p R W S
  let a' : C(Boundary n,MappingPath q) := {
    toFun x :=
      ⟨(⟨(a x).val.val.1,fun j hj ↦ ⟨((a x).property j hj).1.1,by
          rw [← (a x).val.property]
          exact ((a x).property j hj).1.2 0⟩⟩,
        ⟨fun t ↦ ⟨(a x).val.val.2 t,fun j hj ↦ ((a x).property j hj).1.2 t⟩,
          by fun_prop⟩),Subtype.ext (a x).val.property⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk
      · fun_prop
      · apply ContinuousMap.continuous_of_continuous_uncurry
        apply Continuous.subtype_mk
        change Continuous (fun z : Boundary n × unitInterval ↦ (a z.1).val.val.2 z.2)
        fun_prop }
  have hab' : ∀ x : Boundary n,MappingPath.endpoint q (a' x) = b x.val := by
    intro x
    exact Subtype.ext (congrArg Subtype.val (hab x))
  obtain ⟨l,hl,hb⟩ := hf.mappingPath_endpoint_boundaryLifting n a' b hab'
  let c : C(Cube n,{z : MappingPath p //
      ∀ j ∈ S,z ∈ mappingPathChartSet p R W j ∧ MappingPath.endpoint p z ∈ W j}) := {
    toFun x :=
      ⟨⟨((l x).val.1.val,⟨fun t ↦ ((l x).val.2 t).val,by fun_prop⟩),
        congrArg Subtype.val (l x).property⟩,
        fun j hj ↦ ⟨⟨((l x).val.1.property j hj).1,
          fun t ↦ ((l x).val.2 t).property j hj⟩,
          ((l x).val.2 1).property j hj⟩⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.subtype_mk
      apply Continuous.prodMk
      · fun_prop
      · apply ContinuousMap.continuous_of_continuous_uncurry
        change Continuous (fun z : Cube n × unitInterval ↦ ((l z.1).val.2 z.2).val)
        fun_prop }
  refine ⟨c,?_,?_⟩
  · intro x
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun z : MappingPath q ↦ z.val.1.val) (hl x)
    · apply ContinuousMap.ext
      intro t
      exact congrArg (fun z : MappingPath q ↦ (z.val.2 t).val) (hl x)
  · apply ContinuousMap.ext
    intro x
    exact Subtype.ext (congrArg Subtype.val (ContinuousMap.congr_fun hb x))

/-- Ordinary strict HELP on the original cube follows from weak maps on all
nonempty finite chart intersections and a genuine controlling parameter cover.
The source chart sets need not be open. -/
theorem exists_strictHELP_of_controlled_weak_chart_cover (p : C(E, B))
    (R : J → Set E) (W : J → Set B)
    (hloc : ∀ S : Finset J,S.Nonempty →
      IsWeakHomotopyEquivalence (controlledChartMap p R W S))
    (n : ℕ) (a : C(Boundary n,E)) (b : C(Cube n,B))
    (hab : ∀ x : Boundary n,p (a x) = b x.val)
    (U : J → Set (Cube n)) (hU : ∀ j,IsOpen (U j))
    (hcover : ∀ x : Cube n,∃ j,x ∈ U j)
    (hb : ∀ j (x : Cube n),x ∈ U j → b x ∈ W j)
    (ha : ∀ j (x : Boundary n),x.val ∈ U j → a x ∈ R j) :
    ∃ c : C(Cube n,E),(∀ x : Boundary n,c x.val = a x) ∧
      Nonempty ((p.comp c).HomotopyRel b (_root_.Cube.boundary (Fin n))) := by
  let a' := (MappingPath.inclusion p).comp a
  have hab' : ∀ x : Boundary n,MappingPath.endpoint p (a' x) = b x.val := hab
  have ha' : ∀ j (x : Boundary n),x.val ∈ U j →
      a' x ∈ mappingPathChartSet p R W j := by
    intro j x hx
    refine ⟨ha j x hx,?_⟩
    intro t
    change p (a x) ∈ W j
    rw [hab x]
    exact hb j x.val hx
  obtain ⟨l,hl,he⟩ := exists_lift_of_controlled_chart_cover
    (MappingPath.endpoint p) (mappingPathChartSet p R W) W
    (fun S hS ↦ controlled_mappingPath_chart_boundaryLifting p R W S (hloc S hS))
    n a' b hab' U hU hcover hb ha'
  let c := (MappingPath.source p).comp l
  let H : (p.comp c).Homotopy b := {
    toFun z := (l z.2).val.2 z.1
    continuous_toFun := by fun_prop
    map_zero_left x := (l x).property
    map_one_left x := ContinuousMap.congr_fun he x }
  refine ⟨c,fun x ↦ congrArg (fun z : MappingPath p ↦ z.val.1) (hl x),⟨?_⟩⟩
  refine { toHomotopy := H,prop' := ?_ }
  intro t x hx
  change (l x).val.2 t = p ((l x).val.1)
  rw [hl ⟨x,hx⟩]
  rfl

end Topology.CubicalSubdivision
