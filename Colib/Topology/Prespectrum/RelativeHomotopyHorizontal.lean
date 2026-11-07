/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.RelativeHomotopy
public import Colib.Topology.Prespectrum.HomotopyComposition

/-! Reverse and concatenate the original path coordinate of a relative comparison.
These operations retain the independent comparison and structure coordinates. -/
/-! Implementation provenance:
`Quillen/Topology/Prespectrum/RelativeHomotopyHorizontal.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original continuous families, independent
parameters, fixed boundaries and strict structure compatibility are retained. -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {f g h : E ⟶ F}

/-- Reverse the original path coordinate while preserving comparison time. -/
def symmPath {H K : Homotopy f g} (J : H.RelHomotopy K) :
    H.symm.RelHomotopy K.symm where
  level n := {
    toFun := fun z ↦ J.level n (z.1, (unitInterval.symm z.2.1, z.2.2))
    continuous_toFun := by fun_prop
    map_zero_left z := (J.level n).apply_zero (unitInterval.symm z.1, z.2)
    map_one_left z := (J.level n).apply_one (unitInterval.symm z.1, z.2)
    prop' r z hz := by
      change J.level n (r, (unitInterval.symm z.1, z.2)) = _
      apply (J.level n).eq_fst
      rcases hz with hz | hz | hz
      · exact Or.inr (Or.inl (by simp [hz]))
      · exact Or.inl (by simp [hz])
      · exact Or.inr (Or.inr hz) }
  comm n r s x t := J.comm n r (unitInterval.symm s) x t

/-- Concatenate in the original path coordinate, using explicit swapped continuous squares.
No local compactness of the spectrum spaces is required. -/
def hcomp {H H' : Homotopy f g} {K K' : Homotopy g h}
    (J : H.RelHomotopy H') (L : K.RelHomotopy K') :
    (H.trans K).RelHomotopy (H'.trans K') := by
  let square {a b : E ⟶ F} {P Q : Homotopy a b} (M : P.RelHomotopy Q) (n : ℕ) :
      (⟨fun z : unitInterval × E.space n ↦ a.map n z.2, by fun_prop⟩ :
        C(unitInterval × E.space n, F.space n)).Homotopy
      ⟨fun z ↦ b.map n z.2, by fun_prop⟩ := {
    toFun := fun z ↦ M.level n (z.2.1, (z.1, z.2.2))
    continuous_toFun := by fun_prop
    map_zero_left z := ((M.level n).eq_fst z.1 (Or.inl rfl)).trans (P.at_zero n z.2)
    map_one_left z := ((M.level n).eq_fst z.1 (Or.inr (Or.inl rfl))).trans (P.at_one n z.2) }
  let concat (n : ℕ) := (square J n).trans (square L n)
  refine {
    level := fun n ↦ {
      toFun := fun z ↦ concat n (z.2.1, (z.1, z.2.2))
      continuous_toFun := by fun_prop
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
    comm := ?_ }
  · intro z
    change ((square J n).trans (square L n)) (z.1, (0, z.2)) =
      ((H.levelHomotopy n).trans (K.levelHomotopy n)) z
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split
    · exact (J.level n).apply_zero _
    · exact (L.level n).apply_zero _
  · intro z
    change ((square J n).trans (square L n)) (z.1, (1, z.2)) =
      ((H'.levelHomotopy n).trans (K'.levelHomotopy n)) z
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split
    · exact (J.level n).apply_one _
    · exact (L.level n).apply_one _
  · rintro r ⟨s, x⟩ hz
    change concat n (s, (r, x)) = (H.trans K).level n (s, x)
    rcases hz with hz | hz | hz
    · change s = 0 at hz
      subst s
      exact ((concat n).apply_zero _).trans ((H.trans K).at_zero n x).symm
    · change s = 1 at hz
      subst s
      exact ((concat n).apply_one _).trans ((H.trans K).at_one n x).symm
    · change x = E.point n at hz
      subst x
      change ((square J n).trans (square L n)) (s, (r, E.point n)) = _
      rw [ContinuousMap.Homotopy.trans_apply]
      split
      · exact ((J.at r).at_point n _).trans ((H.trans K).at_point n s).symm
      · exact ((L.at r).at_point n _).trans ((H.trans K).at_point n s).symm
  · intro n r s x t
    change ((square J (n+1)).trans (square L (n+1))) (s, (r, E.structureMap n x t)) =
      F.structureMap n (((square J n).trans (square L n)) (s, (r, x))) t
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split
    · exact J.comm n r _ x t
    · exact L.comm n r _ x t

end Topology.LoopPrespectrum.Homotopy.RelHomotopy
