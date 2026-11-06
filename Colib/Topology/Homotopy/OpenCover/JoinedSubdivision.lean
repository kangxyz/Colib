/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.TransParameters
public import Colib.Topology.Homotopy.OpenCover.PathValue

/-!
# Joined Subdivision

An actual subdivision of path concatenation, joining the two half-scaled lists.
-/

@[expose] public section

noncomputable section
open Set
universe u v
namespace FundamentalGroupoid.OpenCover
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {U : ι → Set X}
namespace PathSubdivision
variable {x y z : X} {p : Path x y} {q : Path y z}
variable (s : PathSubdivision (U := U) p) (t : PathSubdivision (U := U) q)

/-- Subdivision times rescaled to the two halves of a concatenated path. -/
def joinTimes : Fin (s.n + t.n + 1) → unitInterval :=
  joinParameters (fun i => leftHalf (s.times i)) (fun i => rightHalf (t.times i))

theorem joinTimes_left (i : Fin (s.n + 1)) :
    s.joinTimes t ⟨i.val, by omega⟩ = leftHalf (s.times i) := by
  apply joinParameters_left
  rw [s.last, t.first]
  apply Subtype.ext
  simp

theorem joinTimes_right (i : Fin (t.n + 1)) :
    s.joinTimes t ⟨s.n + i.val, by omega⟩ = rightHalf (t.times i) :=
  joinParameters_right _ _ i

theorem joinTimes_monotone : Monotone (s.joinTimes t) := by
  apply joinParameters_monotone
  · rw [s.last, t.first]
    apply Subtype.ext
    simp
  · exact leftHalf_monotone.comp s.monotone
  · exact rightHalf_monotone.comp t.monotone

/-- The containing chart inherited from the corresponding half-subdivision. -/
def joinChart (j : Fin (s.n + t.n)) : ι :=
  if h : j.val < s.n then s.chart ⟨j.val, h⟩ else t.chart ⟨j.val - s.n, by omega⟩

theorem join_contained (j : Fin (s.n + t.n)) :
    Set.range ((p.trans q).subpath (s.joinTimes t j.castSucc) (s.joinTimes t j.succ)) ⊆
      U (s.joinChart t j) := by
  by_cases h : j.val < s.n
  · let k : Fin s.n := ⟨j.val, h⟩
    have h0 : s.joinTimes t j.castSucc = leftHalf (s.times k.castSucc) := s.joinTimes_left t
      k.castSucc
    have h1 : s.joinTimes t j.succ = leftHalf (s.times k.succ) := s.joinTimes_left t k.succ
    rintro _ ⟨a, rfl⟩
    change (p.trans q) (Icc.convexComb (s.joinTimes t j.castSucc) (s.joinTimes t j.succ) a) ∈ _
    rw [h0, h1, leftHalf_convexComb, trans_leftHalf]
    simpa only [joinChart, h, dite_true, k, Path.subpath, Path.coe_mk_mk, Function.comp_apply]
      using s.contained k (Set.mem_range_self a)
  · let k : Fin t.n := ⟨j.val - s.n, by omega⟩
    have h0 : s.joinTimes t j.castSucc = rightHalf (t.times k.castSucc) := by
      convert s.joinTimes_right t k.castSucc using 1
      congr 1
      apply Fin.ext
      simp only [Fin.val_castSucc]
      dsimp [k]
      omega
    have h1 : s.joinTimes t j.succ = rightHalf (t.times k.succ) := by
      convert s.joinTimes_right t k.succ using 1
      congr 1
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp [k]
      omega
    rintro _ ⟨a, rfl⟩
    change (p.trans q) (Icc.convexComb (s.joinTimes t j.castSucc) (s.joinTimes t j.succ) a) ∈ _
    rw [h0, h1, rightHalf_convexComb, trans_rightHalf]
    simpa only [joinChart, h, dite_false, k, Path.subpath, Path.coe_mk_mk, Function.comp_apply]
      using t.contained k (Set.mem_range_self a)

/-- An actual subdivision of path concatenation, joining the two half-scaled lists. -/
def join : PathSubdivision (U := U) (p.trans q) where
  n := s.n + t.n
  times := s.joinTimes t
  monotone := s.joinTimes_monotone t
  first := by
    have h := s.joinTimes_left t 0
    rw [s.first] at h
    exact h.trans (by apply Subtype.ext; simp)
  last := by
    have h := s.joinTimes_right t (Fin.last t.n)
    rw [t.last] at h
    exact h.trans (by apply Subtype.ext; simp)
  chart := s.joinChart t
  contained := s.join_contained t

end PathSubdivision
end FundamentalGroupoid.OpenCover
