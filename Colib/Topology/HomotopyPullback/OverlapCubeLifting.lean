/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyPullback.OverlapColumnContraction
public import Colib.Topology.CubicalSubdivision.TwoChartColumnNormalization

/-!
# Genuine finite cube lifting for the original overlap gap comparison

The actual finite bounds on the two overlap inclusions drive whole-grid normalization of a
family's stored paths. Continuous column selection and straight original-time contraction then
produce an overlap lift. The comparison is the existing constant-path map. Original boundary
points and their complete constant stored paths are fixed throughout. The bound is `d < p + q`
for a parameter cube of dimension `d`, including `d = 0`; no natural-number subtraction is used.
-/

/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyPullback/OverlapCubeLifting.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, finite bounds,
whole path families and universe parameters are retained in their native owners. -/
@[expose] public section

open Topology.CubicalSubdivision


noncomputable section
open Topology TopCat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u

namespace Topology.HomotopyPullback

open CubicalSubdivision

variable {Y : Type u} [TopologicalSpace Y] {U V : Set Y}

/-- Put the original path coordinate first, without transposing any parameter coordinate. -/
def overlapCubeFamily (d : ℕ)
    (b : C(Cube d, HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V))) :
    C(Cube (d + 1), Y) := ⟨fun z ↦ (b (Fin.tail z)).val.2.2 (z 0), by fun_prop⟩

/-- Strict cube lifting in the finite excision range for the original constant-path comparison.
The lift extends the actual supplied overlap-boundary map, and the homotopy fixes it pointwise. -/
theorem exists_overlap_cube_lift (d p q : ℕ) (hd : d < p + q)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q)
    (a : C({x : Cube d // x ∈ _root_.Cube.boundary (Fin d)}, ↥(U ∩ V)))
    (b : C(Cube d, HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)))
    (w : (overlapComparison U V).comp a =
      b.comp (ContinuousMap.subtypeVal (_root_.Cube.boundary (Fin d))))
    (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hbc : b₁ ≤ a₂) (hce : a₂ < b₂) :
    ∃ c : C(Cube d, ↥(U ∩ V)),
      c.comp (ContinuousMap.subtypeVal (_root_.Cube.boundary (Fin d))) = a ∧
        Nonempty (((overlapComparison U V).comp c).HomotopyRel b
          (_root_.Cube.boundary (Fin d))) := by
  have hfamilyCover (z : Cube (d + 1)) : overlapCubeFamily d b z ∈ U ∪ V := by
    rw [hcover]
    trivial
  have hleft (x : Cube d) : overlapCubeFamily d b (Fin.cons 0 x) ∈ U :=
    (b x).property.1 ▸ (b x).val.2.1.property
  have hright (x : Cube d) : overlapCubeFamily d b (Fin.cons 1 x) ∈ V :=
    (b x).property.2 ▸ (b x).val.1.property
  have hboundary (t : unitInterval) (x : Cube d) (hx : x ∈ _root_.Cube.boundary (Fin d)) :
      overlapCubeFamily d b (Fin.cons t x) = (a ⟨x, hx⟩).val :=
    (congrArg (fun z ↦ z.val.2.2 t) (ContinuousMap.congr_fun w ⟨x, hx⟩)).symm
  obtain ⟨v, K, hKleft, hKright, hKfix, hcolumn⟩ :=
    exists_relative_two_chart_column_normalization d (overlapCubeFamily d b) U V hU hV
      hfamilyCover hleft hright
      (fun t x hx ↦ hboundary t x hx ▸ (a ⟨x, hx⟩).property)
      a₁ b₁ a₂ b₂ hab hbc hce p q hd hUV hVU
  let paths (r : unitInterval) : C(unitInterval × Cube d, Y) :=
    ⟨fun z ↦ K (r, Fin.cons z.1 z.2), by fun_prop⟩
  let b' := ofOverlapColumns (paths 1) (hKleft 1) (hKright 1)
  let T : b.Homotopy b' := {
    toFun z := ofOverlapColumns (paths z.1) (hKleft z.1) (hKright z.1) z.2
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk (by
        apply Continuous.subtype_mk
        change Continuous (fun z : unitInterval × Cube d ↦ K (z.1, Fin.cons 1 z.2))
        fun_prop)
      apply Continuous.prodMk (by
        apply Continuous.subtype_mk
        change Continuous (fun z : unitInterval × Cube d ↦ K (z.1, Fin.cons 0 z.2))
        fun_prop)
      apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (unitInterval × Cube d) × unitInterval ↦
        K (z.1.1, Fin.cons z.2 z.1.2))
      fun_prop
    map_zero_left x := by
      apply overlap_path_ext
      apply ContinuousMap.ext
      intro t
      exact K.map_zero_left (Fin.cons t x)
    map_one_left _ := rfl }
  have hTfix (r : unitInterval) (x : Cube d) (hx : x ∈ _root_.Cube.boundary (Fin d)) :
      T (r, x) = b x := by
    apply overlap_path_ext
    exact ContinuousMap.ext (fun t ↦ hKfix r t x hx)
  have hcolumn' (x : Cube d) :
      (∀ t, (b' x).val.2.2 t ∈ U) ∨ ∀ t, (b' x).val.2.2 t ∈ V := by
    rcases hcolumn x with h | h
    · exact Or.inl (fun t ↦ (congrArg (fun y ↦ y ∈ U) (K.map_one_left (Fin.cons t x))).mpr (h t))
    · exact Or.inr (fun t ↦ (congrArg (fun y ↦ y ∈ V) (K.map_one_left (Fin.cons t x))).mpr (h t))
  obtain ⟨c, S, hSfix⟩ := exists_overlap_column_contraction b' hU hV hcolumn'
  have hconst (x : Cube d) (hx : x ∈ _root_.Cube.boundary (Fin d)) :
      ∀ t, (b' x).val.2.2 t = (b' x).val.2.2 0 := by
    intro t
    exact ((hKfix 1 t x hx).trans (hboundary t x hx)).trans
      ((hKfix 1 0 x hx).trans (hboundary 0 x hx)).symm
  have hcb (z : {x : Cube d // x ∈ _root_.Cube.boundary (Fin d)}) : c z.val = a z := by
    apply overlapComparison_injective U V
    exact (S.map_one_left z.val).symm.trans ((hSfix z.val (hconst z.val z.property) 1).trans
      ((hTfix 1 z.val z.property).trans (ContinuousMap.congr_fun w z).symm))
  let T' : b.HomotopyRel b' (_root_.Cube.boundary (Fin d)) := {
    toHomotopy := T
    prop' := hTfix }
  let S' : b'.HomotopyRel ((overlapComparison U V).comp c) (_root_.Cube.boundary (Fin d)) := {
    toHomotopy := S
    prop' := fun r x hx ↦ hSfix x (hconst x hx) r }
  exact ⟨c, ContinuousMap.ext hcb, ⟨(T'.trans S').symm⟩⟩

/-- The same actual finite lift on the universe-lifted cube-boundary tests used by HELP.
Only parameter coordinates are transported; the comparison and boundary data are unchanged. -/
theorem overlap_cube_strictHELP (d p q : ℕ) (hd : d < p + q)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q)
    (a : C(CubicalTests.boundary.{u} d, ↥(U ∩ V)))
    (b : C(CubicalTests.cube.{u} d,
      HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)))
    (w : (overlapComparison U V).comp a = b.comp (CubicalTests.boundaryInclusion d).hom)
    (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hbc : b₁ ≤ a₂) (hce : a₂ < b₂) :
    ∃ c : C(CubicalTests.cube.{u} d, ↥(U ∩ V)),
      c.comp (CubicalTests.boundaryInclusion d).hom = a ∧
        Nonempty (((overlapComparison U V).comp c).HomotopyRel b
          (Set.range (CubicalTests.boundaryInclusion d))) := by
  let a' : C({x : Cube d // x ∈ _root_.Cube.boundary (Fin d)}, ↥(U ∩ V)) :=
    ⟨fun z ↦ a ⟨ULift.up z.val, z.property⟩, by fun_prop⟩
  let b' : C(Cube d,
      HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)) :=
    ⟨fun x ↦ b (ULift.up x), by fun_prop⟩
  have w' : (overlapComparison U V).comp a' =
      b'.comp (ContinuousMap.subtypeVal (_root_.Cube.boundary (Fin d))) := by
    ext z
    exact ContinuousMap.congr_fun w ⟨ULift.up z.val, z.property⟩
  obtain ⟨c, hc, ⟨H⟩⟩ := exists_overlap_cube_lift d p q hd hU hV hcover hUV hVU a' b' w'
    a₁ b₁ a₂ b₂ hab hbc hce
  let c' : C(CubicalTests.cube.{u} d, ↥(U ∩ V)) := ⟨fun x ↦ c x.down, by fun_prop⟩
  refine ⟨c', ?_, ⟨{ toHomotopy := {
    toFun z := H (z.1, z.2.down)
    continuous_toFun := by fun_prop
    map_zero_left x := H.toHomotopy.map_zero_left x.down
    map_one_left x := H.toHomotopy.map_one_left x.down }, prop' := ?_ }⟩⟩
  · apply ContinuousMap.ext
    intro z
    exact ContinuousMap.congr_fun hc ⟨z.val.down, z.property⟩
  · rintro r _ ⟨z, rfl⟩
    exact H.prop r z.val.down z.property

/-- The true degree-zero excision consequence includes every target component. The strict
inequality excludes the false zero-plus-zero coverage conclusion. -/
theorem overlapComparison_component_surjective (p q : ℕ) (hpq : 0 < p + q)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q)
    (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hbc : b₁ ≤ a₂) (hce : a₂ < b₂)
    (y : HomotopyPullback (ContinuousMap.subtypeVal U) (ContinuousMap.subtypeVal V)) :
    ∃ x : ↥(U ∩ V), Joined (overlapComparison U V x) y := by
  let : IsEmpty {x : Cube 0 // x ∈ _root_.Cube.boundary (Fin 0)} := ⟨fun z ↦ by
    obtain ⟨i, _⟩ := z.property
    exact Fin.elim0 i⟩
  let a : C({x : Cube 0 // x ∈ _root_.Cube.boundary (Fin 0)}, ↥(U ∩ V)) :=
    ⟨isEmptyElim, continuous_of_discreteTopology⟩
  let b := ContinuousMap.const (Cube 0) y
  have w : (overlapComparison U V).comp a =
      b.comp (ContinuousMap.subtypeVal (_root_.Cube.boundary (Fin 0))) := by
    ext z
    exact isEmptyElim z
  obtain ⟨c, _, ⟨H⟩⟩ := exists_overlap_cube_lift 0 p q hpq hU hV hcover hUV hVU a b w
    a₁ b₁ a₂ b₂ hab hbc hce
  exact ⟨c (fun i ↦ Fin.elim0 i), ⟨H.toHomotopy.evalAt (fun i ↦ Fin.elim0 i)⟩⟩

end Topology.HomotopyPullback
