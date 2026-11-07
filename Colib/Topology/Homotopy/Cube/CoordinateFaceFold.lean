/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Cube.FaceFold
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Coordinate insertion of the explicit lateral-face fold

The terminal fold preserves the actual codimension-two cube boundary. During
the homotopy, a fixed unaffected endpoint together with another endpoint still
maps into that boundary. These are precisely the distinct geometric facts
needed for the folded cube and for its unchanged-face relative homotopies.
-/

/-! Implementation source: `Quillen/Topology/Cube/CoordinateFaceFold.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual cubical maps,
relative homotopies, quotient multiplication, and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v

namespace Topology
variable {N : Type v} [DecidableEq N]

/-- The actual codimension-two cube boundary: two distinct endpoint coordinates. -/
def cubeCodimTwoBoundary (N : Type v) : Set (N → I) :=
  {x | ∃ i j, i ≠ j ∧ (x i = 0 ∨ x i = 1) ∧ (x j = 0 ∨ x j = 1)}

/-- Insert the square fold into the side/time coordinate pair `(j,i)`. -/
def cubeFaceFold (i j : N) (r : I) (x : N → I) : N → I :=
  fun k ↦ if k = j then (faceFold r (x j, x i)).1
    else if k = i then (faceFold r (x j, x i)).2 else x k

@[fun_prop] theorem continuous_cubeFaceFold (i j : N) :
    Continuous (fun p : I × (N → I) ↦ cubeFaceFold i j p.1 p.2) := by
  have h : Continuous (fun p : I × (N → I) ↦ faceFold p.1 (p.2 j, p.2 i)) :=
    continuous_faceFold.comp
      (continuous_fst.prodMk (((continuous_apply j).comp continuous_snd).prodMk
        ((continuous_apply i).comp continuous_snd)))
  apply continuous_pi
  intro k
  unfold cubeFaceFold
  split_ifs
  · exact h.fst
  · exact h.snd
  · exact (continuous_apply k).comp continuous_snd

@[simp] theorem cubeFaceFold_side (i j : N) (r : I) (x : N → I) :
    cubeFaceFold i j r x j = (faceFold r (x j, x i)).1 := by simp [cubeFaceFold]

@[simp] theorem cubeFaceFold_time (i j : N) (hij : i ≠ j) (r : I) (x : N → I) :
    cubeFaceFold i j r x i = (faceFold r (x j, x i)).2 := by
  simp [cubeFaceFold, hij]

@[simp] theorem cubeFaceFold_other (i j k : N) (hki : k ≠ i) (hkj : k ≠ j)
    (r : I) (x : N → I) : cubeFaceFold i j r x k = x k := by
  simp [cubeFaceFold, hki, hkj]

@[simp] theorem cubeFaceFold_zero (i j : N) (hij : i ≠ j) (x : N → I) :
    cubeFaceFold i j 0 x = x := by
  ext k
  by_cases hkj : k = j
  · subst k; simp
  · by_cases hki : k = i
    · subst k; simp [hij]
    · simp [hki, hkj]

/-- If the selected square starts on its boundary, some selected coordinate
is still an endpoint at every time. -/
theorem cubeFaceFold_selected_endpoint (i j : N) (hij : i ≠ j) (r : I) (x : N → I)
    (hx : (x i = 0 ∨ x i = 1) ∨ (x j = 0 ∨ x j = 1)) :
    ∃ k, (k = i ∨ k = j) ∧
      (cubeFaceFold i j r x k = 0 ∨ cubeFaceFold i j r x k = 1) := by
  have hp : SquareBoundary (x j, x i) := by
    rcases hx with (h | h) | (h | h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  rcases faceFold_boundary r (x j, x i) hp with h | h | h | h
  · exact ⟨j, Or.inr rfl, Or.inl (by simpa using h)⟩
  · exact ⟨j, Or.inr rfl, Or.inr (by simpa using h)⟩
  · exact ⟨i, Or.inl rfl, Or.inl (by simpa [hij] using h)⟩
  · exact ⟨i, Or.inl rfl, Or.inr (by simpa [hij] using h)⟩

/-- The fixed endpoint of an unaffected face and another endpoint retain
codimension-two basedness throughout the displayed homotopy. -/
theorem cubeFaceFold_two_endpoints (i j k l : N) (hij : i ≠ j)
    (hki : k ≠ i) (hkj : k ≠ j) (hkl : k ≠ l) (r : I) (x : N → I)
    (hk : x k = 0 ∨ x k = 1) (hl : x l = 0 ∨ x l = 1) :
    cubeFaceFold i j r x ∈ cubeCodimTwoBoundary N := by
  have hk' : cubeFaceFold i j r x k = 0 ∨ cubeFaceFold i j r x k = 1 := by
    simpa [hki, hkj] using hk
  by_cases hli : l = i
  · subst l
    obtain ⟨m, hm, he⟩ := cubeFaceFold_selected_endpoint i j hij r x (Or.inl hl)
    exact ⟨k, m, by rcases hm with rfl | rfl <;> assumption, hk', he⟩
  · by_cases hlj : l = j
    · subst l
      obtain ⟨m, hm, he⟩ := cubeFaceFold_selected_endpoint i j hij r x (Or.inr hl)
      exact ⟨k, m, by rcases hm with rfl | rfl <;> assumption, hk', he⟩
    · exact ⟨k, l, hkl, hk', by simpa [hli, hlj] using hl⟩

/-- At the terminal time the selected square itself preserves pairs of endpoints. -/
theorem cubeFaceFold_one_selected_corners (i j : N) (hij : i ≠ j) (x : N → I)
    (hi : x i = 0 ∨ x i = 1) (hj : x j = 0 ∨ x j = 1) :
    cubeFaceFold i j 1 x ∈ cubeCodimTwoBoundary N := by
  have h := faceFold_one_corners (x j, x i) hj hi
  exact ⟨i, j, hij, by simpa [hij] using h.2, by simpa using h.1⟩

/-- The terminal cube has the same genuine codimension-two basedness property. -/
theorem cubeFaceFold_one_codimTwo (i j : N) (hij : i ≠ j) (x : N → I)
    (hx : x ∈ cubeCodimTwoBoundary N) :
    cubeFaceFold i j 1 x ∈ cubeCodimTwoBoundary N := by
  obtain ⟨a, b, hab, ha, hb⟩ := hx
  by_cases hai : a = i
  · subst a
    by_cases hbj : b = j
    · subst b
      exact cubeFaceFold_one_selected_corners i j hij x ha hb
    · exact cubeFaceFold_two_endpoints i j b i hij hab.symm hbj hab.symm 1 x hb ha
  · by_cases haj : a = j
    · subst a
      by_cases hbi : b = i
      · subst b
        exact cubeFaceFold_one_selected_corners i j hij x hb ha
      · exact cubeFaceFold_two_endpoints i j b j hij hbi hab.symm hab.symm 1 x hb ha
    · exact cubeFaceFold_two_endpoints i j a b hij hai haj hab 1 x ha hb

/-- The full bottom face is unchanged by the coordinate fold. -/
theorem cubeFaceFold_bottom (i j : N) (hij : i ≠ j) (r : I) (x : N → I)
    (hx : x i = 0) : cubeFaceFold i j r x = x := by
  ext k
  by_cases hkj : k = j
  · subst k; simp [hx]
  · by_cases hki : k = i
    · subst k; simp [hij, hx]
    · simp [hki, hkj]

/-- The opposite lateral face is unchanged by the coordinate fold. -/
theorem cubeFaceFold_right (i j : N) (hij : i ≠ j) (r : I) (x : N → I)
    (hx : x j = 1) : cubeFaceFold i j r x = x := by
  ext k
  by_cases hkj : k = j
  · subst k; simp [hx]
  · by_cases hki : k = i
    · subst k; simp [hij, hx]
    · simp [hki, hkj]

/-- Reflect one original cube coordinate. -/
def cubeCoordinateReflect (j : N) (x : N → I) : N → I :=
  fun k ↦ if k = j then unitInterval.symm (x j) else x k

@[fun_prop] theorem continuous_cubeCoordinateReflect (j : N) :
    Continuous (cubeCoordinateReflect j) := by
  apply continuous_pi
  intro k
  unfold cubeCoordinateReflect
  split_ifs
  · exact unitInterval.continuous_symm.comp (continuous_apply j)
  · exact continuous_apply k

@[simp] theorem cubeCoordinateReflect_twice (j : N) (x : N → I) :
    cubeCoordinateReflect j (cubeCoordinateReflect j x) = x := by
  ext k
  by_cases h : k = j
  · subst k; simp [cubeCoordinateReflect]
  · simp [cubeCoordinateReflect, h]

@[simp] theorem cubeCoordinateReflect_endpoint (j k : N) (x : N → I) :
    (cubeCoordinateReflect j x k = 0 ∨ cubeCoordinateReflect j x k = 1) ↔
      (x k = 0 ∨ x k = 1) := by
  by_cases h : k = j
  · subst k
    simp [cubeCoordinateReflect, or_comm]
  · simp [cubeCoordinateReflect, h]

/-- Reflection retains the actual codimension-two boundary. -/
theorem cubeCoordinateReflect_codimTwo (j : N) (x : N → I)
    (hx : x ∈ cubeCodimTwoBoundary N) :
    cubeCoordinateReflect j x ∈ cubeCodimTwoBoundary N := by
  obtain ⟨a, b, hab, ha, hb⟩ := hx
  exact ⟨a, b, hab, (cubeCoordinateReflect_endpoint j a x).mpr ha,
    (cubeCoordinateReflect_endpoint j b x).mpr hb⟩

/-- Conjugate the lower fold by reflection to move the upper side into the top. -/
def cubeUpperFaceFold (i j : N) (r : I) (x : N → I) : N → I :=
  cubeCoordinateReflect j (cubeFaceFold i j r (cubeCoordinateReflect j x))

@[fun_prop] theorem continuous_cubeUpperFaceFold (i j : N) :
    Continuous (fun p : I × (N → I) ↦ cubeUpperFaceFold i j p.1 p.2) :=
  (continuous_cubeCoordinateReflect j).comp ((continuous_cubeFaceFold i j).comp
    (continuous_fst.prodMk ((continuous_cubeCoordinateReflect j).comp continuous_snd)))

@[simp] theorem cubeUpperFaceFold_zero (i j : N) (hij : i ≠ j) (x : N → I) :
    cubeUpperFaceFold i j 0 x = x := by
  simp [cubeUpperFaceFold, hij]

/-- The terminal reflected fold also preserves codimension-two basedness. -/
theorem cubeUpperFaceFold_one_codimTwo (i j : N) (hij : i ≠ j) (x : N → I)
    (hx : x ∈ cubeCodimTwoBoundary N) :
    cubeUpperFaceFold i j 1 x ∈ cubeCodimTwoBoundary N :=
  cubeCoordinateReflect_codimTwo j _ (cubeFaceFold_one_codimTwo i j hij _
    (cubeCoordinateReflect_codimTwo j x hx))

/-- Both fold directions retain an unaffected coordinate literally. -/
@[simp] theorem cubeUpperFaceFold_other (i j k : N) (hki : k ≠ i) (hkj : k ≠ j)
    (r : I) (x : N → I) : cubeUpperFaceFold i j r x k = x k := by
  simp [cubeUpperFaceFold, cubeCoordinateReflect, hki, hkj]

/-- The upper-side fold fixes the bottom face. -/
theorem cubeUpperFaceFold_bottom (i j : N) (hij : i ≠ j) (r : I) (x : N → I)
    (hx : x i = 0) : cubeUpperFaceFold i j r x = x := by
  unfold cubeUpperFaceFold
  rw [cubeFaceFold_bottom i j hij r _ (by simp [cubeCoordinateReflect, hij, hx])]
  exact cubeCoordinateReflect_twice j x

/-- The upper-side fold fixes the opposite, lower side. -/
theorem cubeUpperFaceFold_left (i j : N) (hij : i ≠ j) (r : I) (x : N → I)
    (hx : x j = 0) : cubeUpperFaceFold i j r x = x := by
  unfold cubeUpperFaceFold
  rw [cubeFaceFold_right i j hij r _ (by simp [cubeCoordinateReflect, hx])]
  exact cubeCoordinateReflect_twice j x

variable {Z : Type u} [TopologicalSpace Z] {z : Z} {n : ℕ}

/-- Every actual face of a cube with collapsed codimension-two boundary is spherical. -/
def cubicalSphericalFace (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z)
    (j : Fin (n + 1)) (e : I) (he : e = 0 ∨ e = 1) : GenLoop (Fin n) Z z :=
  ⟨⟨fun t ↦ F (j.insertNth e t),
      F.continuous.comp (continuous_const.finInsertNth j continuous_id)⟩, by
    rintro t ⟨k, hk⟩
    apply hF
    exact ⟨j, j.succAbove k, (Fin.succAbove_ne j k).symm,
      by simpa using he, by simpa using hk⟩⟩

/-- Pullback of the original full cube along the terminal coordinate fold. -/
def foldContinuousCube (F : C((Fin (n + 1) → I), Z)) (i j : Fin (n + 1)) :
    C((Fin (n + 1) → I), Z) :=
  ⟨fun x ↦ F (cubeFaceFold i j 1 x),
    F.continuous.comp ((continuous_cubeFaceFold i j).comp
      (continuous_const.prodMk continuous_id))⟩

theorem foldContinuousCube_codimTwo (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z)
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), foldContinuousCube F i j x = z := by
  intro x hx
  exact hF _ (cubeFaceFold_one_codimTwo i j hij x hx)

/-- An unaffected original face retains its actual class by a displayed
boundary-relative homotopy, using no addition theorem. -/
def otherFaceFoldHomotopy (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z)
    (i j k : Fin (n + 1)) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (e : I) (he : e = 0 ∨ e = 1) :
    (cubicalSphericalFace F hF k e he).val.HomotopyRel
      (cubicalSphericalFace (foldContinuousCube F i j)
        (foldContinuousCube_codimTwo F hF i j hij) k e he).val
      (_root_.Cube.boundary (Fin n)) where
  toFun p := F (cubeFaceFold i j p.1 (k.insertNth e p.2))
  continuous_toFun := F.continuous.comp ((continuous_cubeFaceFold i j).comp
    (continuous_fst.prodMk (continuous_const.finInsertNth k continuous_snd)))
  map_zero_left t := congrArg F (cubeFaceFold_zero i j hij (k.insertNth e t))
  map_one_left _ := rfl
  prop' r t ht := by
    obtain ⟨l, hl⟩ := ht
    have hbase := hF _ (cubeFaceFold_two_endpoints i j k (k.succAbove l) hij hki hkj
      (Fin.succAbove_ne k l).symm r (k.insertNth e t)
      (by simpa using he) (by simpa using hl))
    exact hbase.trans ((cubicalSphericalFace F hF k e he).property t ⟨l, hl⟩).symm

/-- The folded lower side is genuinely constant on its whole original parameter cube. -/
theorem foldContinuousCube_lower_side (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z)
    (i j : Fin (n + 1)) (hij : i ≠ j) (t : Fin n → I) :
    foldContinuousCube F i j (j.insertNth 0 t) = z := by
  apply hF
  refine ⟨i, j, hij, Or.inl ?_, Or.inl ?_⟩
  · simp [hij]
  · simp

/-- The original cube reflected in one coordinate. -/
def reflectContinuousCube (F : C((Fin (n + 1) → I), Z)) (j : Fin (n + 1)) :
    C((Fin (n + 1) → I), Z) :=
  ⟨fun x ↦ F (cubeCoordinateReflect j x),
    F.continuous.comp (continuous_cubeCoordinateReflect j)⟩

theorem reflectContinuousCube_codimTwo (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (j : Fin (n + 1)) :
    ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), reflectContinuousCube F j x = z :=
  fun x hx ↦ hF _ (cubeCoordinateReflect_codimTwo j x hx)

/-- Pullback along the upper-side terminal fold. -/
def foldUpperContinuousCube (F : C((Fin (n + 1) → I), Z)) (i j : Fin (n + 1)) :
    C((Fin (n + 1) → I), Z) :=
  reflectContinuousCube (foldContinuousCube (reflectContinuousCube F j) i j) j

theorem foldUpperContinuousCube_codimTwo (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z)
    (i j : Fin (n + 1)) (hij : i ≠ j) :
    ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), foldUpperContinuousCube F i j x = z :=
  fun x hx ↦ hF _ (cubeUpperFaceFold_one_codimTwo i j hij x hx)

/-- Upper folding likewise retains each other face class by an actual relative homotopy. -/
def otherFaceUpperFoldHomotopy (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z)
    (i j k : Fin (n + 1)) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (e : I) (he : e = 0 ∨ e = 1) :
    (cubicalSphericalFace F hF k e he).val.HomotopyRel
      (cubicalSphericalFace (foldUpperContinuousCube F i j)
        (foldUpperContinuousCube_codimTwo F hF i j hij) k e he).val
      (_root_.Cube.boundary (Fin n)) where
  toFun p := F (cubeUpperFaceFold i j p.1 (k.insertNth e p.2))
  continuous_toFun := by
    have hh : Continuous (fun p : I × (Fin n → I) ↦
        Fin.insertNth (α := fun _ ↦ I) k e p.2) :=
      Continuous.finInsertNth k continuous_const continuous_snd
    have hm : Continuous (fun p : I × (Fin n → I) ↦
        (p.1, cubeCoordinateReflect j (Fin.insertNth (α := fun _ ↦ I) k e p.2))) :=
      continuous_fst.prodMk ((continuous_cubeCoordinateReflect j).comp hh)
    have hc : Continuous (fun p : I × (Fin n → I) ↦
        cubeFaceFold i j p.1 (cubeCoordinateReflect j (k.insertNth e p.2))) :=
      (continuous_cubeFaceFold i j).comp hm
    exact F.continuous.comp ((continuous_cubeCoordinateReflect j).comp hc)
  map_zero_left t := congrArg F (cubeUpperFaceFold_zero i j hij (k.insertNth e t))
  map_one_left _ := rfl
  prop' r t ht := by
    obtain ⟨l, hl⟩ := ht
    have hk' : cubeCoordinateReflect j (k.insertNth e t) k = 0 ∨
        cubeCoordinateReflect j (k.insertNth e t) k = 1 :=
      (cubeCoordinateReflect_endpoint j k _).mpr (by simpa using he)
    have hl' : cubeCoordinateReflect j (k.insertNth e t) (k.succAbove l) = 0 ∨
        cubeCoordinateReflect j (k.insertNth e t) (k.succAbove l) = 1 :=
      (cubeCoordinateReflect_endpoint j (k.succAbove l) _).mpr (by simpa using hl)
    have hbase := hF _ (cubeCoordinateReflect_codimTwo j _
      (cubeFaceFold_two_endpoints i j k (k.succAbove l) hij hki hkj
        (Fin.succAbove_ne k l).symm r (cubeCoordinateReflect j (k.insertNth e t)) hk' hl'))
    exact hbase.trans ((cubicalSphericalFace F hF k e he).property t ⟨l, hl⟩).symm

/-- The original upper side is now constant on its full parameter cube. -/
theorem foldUpperContinuousCube_upper_side (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z)
    (i j : Fin (n + 1)) (hij : i ≠ j) (t : Fin n → I) :
    foldUpperContinuousCube F i j (j.insertNth 1 t) = z := by
  apply hF
  refine ⟨i, j, hij, Or.inl ?_, Or.inr ?_⟩
  · simp [cubeCoordinateReflect, hij]
  · simp [cubeCoordinateReflect]

end Topology
