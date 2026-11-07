/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.CubicalSubdivision.ControlledLifting
public import Colib.Topology.CubicalSubdivision.BoundaryLifting
public import Colib.Topology.CubicalSubdivision.FaceCover

/-! # Finite chart lifting with complete source-side constraints

Local lifting maps remember both their target chart and their full source
chart. For a given cube test an actual open parameter cover controls the
prescribed boundary values. Finite intersections of incident charts then
give a genuine global lift by the controlled face induction.


Implementation provenance:
`Quillen/Topology/CubicalSubdivision/ControlledChartLifting.lean`
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
universe u v w
variable {E : Type u} {B : Type v} {J : Type w}
  [TopologicalSpace E] [TopologicalSpace B]

/-- Literal source and target restriction to a finite family of charts.
Source membership retains every chart condition, in addition to its image. -/
def controlledChartMap (p : C(E, B)) (R : J → Set E) (W : J → Set B) (S : Finset J) :
    C({e : E // ∀ j ∈ S,e ∈ R j ∧ p e ∈ W j}, {b : B // ∀ j ∈ S,b ∈ W j}) where
  toFun e := ⟨p e.val,fun j hj ↦ (e.2 j hj).2⟩
  continuous_toFun := by fun_prop

@[simp] theorem controlledChartMap_val (p : C(E, B)) (R : J → Set E) (W : J → Set B)
    (S : Finset J) (e : {e : E // ∀ j ∈ S,e ∈ R j ∧ p e ∈ W j}) :
    (controlledChartMap p R W S e).val = p e.val := rfl

/-- A full finite cube test lifts when an actual open cover of its parameter
space controls the original target and boundary maps, and the original
restricted maps have finite boundary lifting on all nonempty intersections.
The source sets need not be open. -/
theorem exists_lift_of_controlled_chart_cover (p : C(E, B))
    (R : J → Set E) (W : J → Set B)
    (hloc : ∀ S : Finset J,S.Nonempty → BoundaryLifting (controlledChartMap p R W S))
    (n : ℕ) (a : C({x : Cube n // x ∈ _root_.Cube.boundary (Fin n)},E))
    (b : C(Cube n,B)) (hab : ∀ x,p (a x) = b x.val)
    (U : J → Set (Cube n)) (hU : ∀ j,IsOpen (U j))
    (hcover : ∀ x : Cube n,∃ j,x ∈ U j)
    (hb : ∀ j (x : Cube n),x ∈ U j → b x ∈ W j)
    (ha : ∀ j (x : {x : Cube n // x ∈ _root_.Cube.boundary (Fin n)}),
      x.val ∈ U j → a x ∈ R j) :
    ∃ l : C(Cube n,E),
      (∀ x : {x : Cube n // x ∈ _root_.Cube.boundary (Fin n)},l x.val = a x) ∧ p.comp l = b := by
  classical
  obtain ⟨m,hm⟩ := exists_grid_faces_subordinate n (ContinuousMap.id (Cube n)) U hU hcover
  choose chart hchart using hm
  have hparam (F : FaceIndex n m) (j : J) (hj : j ∈ incidentCharts chart F)
      (t : Active F → unitInterval) : face F t ∈ U j := by
    obtain ⟨G,hFG,hGj⟩ := (mem_incidentCharts_iff chart F j).1 hj
    obtain ⟨s,hs⟩ := hFG ⟨t,rfl⟩
    rw [← hs,← hGj]
    exact hchart G s
  have hboundary (F : FaceIndex n m)
      (x : {x : Cube n // x ∈ _root_.Cube.boundary (Fin n)})
      (hx : x.val ∈ faceSet F) : a x ∈ incidentChartSet chart R F := by
    intro j hj
    obtain ⟨t,ht⟩ := hx
    exact ha j x (ht ▸ hparam F j hj t)
  have hfill (F : FaceIndex n m)
      (c : C({t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)},E))
      (hc : ∀ t,c t ∈ incidentChartSet chart R F)
      (hp : ∀ t,p (c t) = b (face F t.val)) :
      ∃ d : C((Active F → unitInterval),E),
        (∀ t : {t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)},d t.val = c t) ∧
        (∀ t,p (d t) = b (face F t)) ∧ (∀ t,d t ∈ incidentChartSet chart R F) := by
    let S := incidentCharts chart F
    let c' : C({t : Active F → unitInterval // t ∈ _root_.Cube.boundary (Active F)},
        {e : E // ∀ j ∈ S,e ∈ R j ∧ p e ∈ W j}) := {
      toFun t := ⟨c t,fun j hj ↦ ⟨hc t j hj,by rw [hp]; exact hb j _ (hparam F j hj t.val)⟩⟩
      continuous_toFun := c.continuous.subtype_mk _ }
    let b' : C((Active F → unitInterval),{y : B // ∀ j ∈ S,y ∈ W j}) := {
      toFun t := ⟨b (face F t),fun j hj ↦ hb j _ (hparam F j hj t)⟩
      continuous_toFun := (b.continuous.comp (face F).continuous).subtype_mk _ }
    have hs : ∀ t,controlledChartMap p R W S (c' t) = b' t.val :=
      fun t ↦ Subtype.ext (hp t)
    obtain ⟨d',hd',hp'⟩ := (hloc S (incidentCharts_nonempty chart F)).face F c' b' hs
    let d : C((Active F → unitInterval),E) := ⟨fun t ↦ (d' t).val,by fun_prop⟩
    refine ⟨d,fun t ↦ congrArg Subtype.val (hd' t),?_,?_⟩
    · intro t
      exact congrArg Subtype.val (ContinuousMap.congr_fun hp' t)
    · intro t j hj
      exact ((d' t).2 j hj).1
  obtain ⟨l,hla,hlp,_⟩ := exists_controlled_grid_lift n m p a b hab
    (incidentChartSet chart R) (fun F G hFG ↦ incidentChartSet_mono chart R hFG)
    hboundary hfill
  exact ⟨l,hla,hlp⟩

end Topology.CubicalSubdivision
