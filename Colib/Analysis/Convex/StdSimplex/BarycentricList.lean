/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Analysis.Convex.StdSimplex.BarycentricSubdivision
public import Mathlib.Data.List.FinRange

/-!
Adapted from `Quillen/Topology/LocalCoefficients/BarycentricList.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps and signs.

# Actual barycenters of finite vertex lists

The barycenter of a nonempty list is the uniform affine average of its vertices,
with repetitions retained. The empty augmentation list has an arbitrary fallback
which is never used by recursive coning.
-/

@[expose] public section

noncomputable section

attribute [local instance] Classical.decEq

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true


namespace stdSimplex.BarycentricSubdivision

variable {J K : Type*}

/-- Actual uniform barycenter of a nonempty list of simplex points. -/
def listBarycenter [Fintype J] [Nonempty J] : List (_root_.stdSimplex ℝ J) → _root_.stdSimplex ℝ J
  | [] => stdSimplex.vertex (Classical.choice ‹Nonempty J›)
  | p :: l => tupleBarycenter (Fin.cons p (fun i : Fin l.length ↦ l[i.val]))

/-- Reindexing a uniform tuple by an equality of lengths preserves its average. -/
theorem tupleBarycenter_cast [Fintype J] {m n : ℕ} (h : m = n)
    (v : Fin (m + 1) → _root_.stdSimplex ℝ J) :
    tupleBarycenter v = tupleBarycenter
      (fun i : Fin (n + 1) ↦ v (Fin.cast (congrArg (fun k ↦ k + 1) h.symm) i)) := by
  subst n
  rfl

/-- The list barycenter is natural for every affine map, with no restriction on
repeated vertices. -/
theorem listBarycenter_natural [Fintype J] [Nonempty J] [Fintype K] [Nonempty K]
    (l : List (_root_.stdSimplex ℝ J)) (hl : l ≠ [])
    (w : J → _root_.stdSimplex ℝ K) :
    affineSimplex w (listBarycenter l) = listBarycenter (l.map (affineSimplex w)) := by
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons p l =>
    simp only [listBarycenter, List.map_cons]
    rw [tupleBarycenter_natural]
    rw [tupleBarycenter_cast (List.length_map (as := l) (affineSimplex w)).symm]
    apply congrArg (fun v : Fin ((l.map (affineSimplex w)).length + 1) →
      _root_.stdSimplex ℝ K ↦ tupleBarycenter v)
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rfl
    · simp only [Fin.cast_succ_eq, Function.comp_apply, Fin.cons_succ, List.getElem_map,
        Fin.val_cast]

end stdSimplex.BarycentricSubdivision
