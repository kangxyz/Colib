/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.Cube.CoordinateFaceFold
public import Colib.Topology.Homotopy.HomotopyGroup.CoordinateTransposition

/-!
# A genuine lateral-face addition operation on original cubical loops

Time is the first ambient coordinate. Folding a lower lateral face into the
top produces literal `GenLoop.transAt`, with the chronological multiplication
order of the existing homotopy group. The side parameter puts time in the
selected top-coordinate slot; its comparison with increasing face coordinates
is a separate explicit coordinate permutation.
-/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/CubicalFaceFold.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual cubical maps,
relative homotopies, quotient multiplication, and signs are retained. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u

namespace Topology
variable {n : ℕ} {Z : Type u} [TopologicalSpace Z] {z : Z}

/-- The original cubical quotient class, retaining its HomotopyGroup type head. -/
def cubicalClass (p : GenLoop (Fin n) Z z) : HomotopyGroup.Pi n Z z := Quotient.mk' p

/-- The lateral face parameter with time placed in the selected top-coordinate slot. -/
def lateralFaceParameter (k : Fin n) (e : I) (t : Fin n → I) : Fin (n + 1) → I :=
  Fin.cons (t k) (Function.update t k e)

@[fun_prop] theorem continuous_lateralFaceParameter (k : Fin n) (e : I) :
    Continuous (lateralFaceParameter k e) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact continuous_apply k
  · change Continuous (fun t : Fin n → I ↦ Function.update t k e j)
    by_cases hj : j = k
    · subst j; simp only [Function.update_self]; exact continuous_const
    · simpa only [Function.update_of_ne hj] using (continuous_apply j :
        Continuous (fun t : Fin n → I ↦ t j))

/-- The original lateral n-loop with its time parameter in the selected top slot. -/
def lateralGenLoop (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z)
    (k : Fin n) (e : I) (he : e = 0 ∨ e = 1) : GenLoop (Fin n) Z z :=
  ⟨⟨fun t ↦ F (lateralFaceParameter k e t),
      F.continuous.comp (continuous_lateralFaceParameter k e)⟩, by
    rintro t ⟨l, hl⟩
    apply hF
    by_cases hlk : l = k
    · subst l
      exact ⟨0, k.succ, (Fin.succ_ne_zero k).symm, hl, by simpa [lateralFaceParameter] using he⟩
    · exact ⟨l.succ, k.succ, by intro h; exact hlk (Fin.succ_inj.mp h),
        by simpa [lateralFaceParameter, hlk] using hl,
        by simpa [lateralFaceParameter] using he⟩⟩

/-- The genuine original top n-loop. -/
def topGenLoop (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) : GenLoop (Fin n) Z z :=
  cubicalSphericalFace F hF 0 1 (Or.inr rfl)

/-- The genuine original bottom n-loop. -/
def bottomGenLoop (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) : GenLoop (Fin n) Z z :=
  cubicalSphericalFace F hF 0 0 (Or.inl rfl)

@[simp] theorem topGenLoop_apply (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (t : Fin n → I) :
    topGenLoop F hF t = F (Fin.cons 1 t) := by simp [topGenLoop, cubicalSphericalFace]

@[simp] theorem bottomGenLoop_apply (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (t : Fin n → I) :
    bottomGenLoop F hF t = F (Fin.cons 0 t) := by simp [bottomGenLoop, cubicalSphericalFace]

/-- The first half of the folded top retains the entire original side map. -/
theorem cubeFaceFold_top_first (k : Fin n) (t : Fin n → I) (ht : (t k : ℝ) ≤ 1 / 2) :
    cubeFaceFold 0 k.succ 1 (Fin.cons 1 t) =
      Fin.cons (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (t k : ℝ))) (Function.update t k 0) := by
  have hq := faceFold_one_top_first (t k) ht
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [cubeFaceFold, hq, (Fin.succ_ne_zero k).symm]
  · by_cases hj : j = k
    · subst j; simp [cubeFaceFold, hq]
    · simp [cubeFaceFold, hj]

/-- The second half retains the entire original top map. -/
theorem cubeFaceFold_top_second (k : Fin n) (t : Fin n → I) (ht : 1 / 2 ≤ (t k : ℝ)) :
    cubeFaceFold 0 k.succ 1 (Fin.cons 1 t) =
      Fin.cons 1 (Function.update t k
        (Set.projIcc (0 : ℝ) 1 zero_le_one (2 * (t k : ℝ) - 1))) := by
  have hq := faceFold_one_top_second (t k) ht
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [cubeFaceFold, hq, (Fin.succ_ne_zero k).symm]
  · by_cases hj : j = k
    · subst j; simp [cubeFaceFold, hq]
    · simp [cubeFaceFold, hj]

/-- The folded top is the original cubical concatenation, as an equality of maps. -/
theorem topGenLoop_fold_eq_transAt (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (k : Fin n) :
    topGenLoop (foldContinuousCube F 0 k.succ)
        (foldContinuousCube_codimTwo F hF 0 k.succ (Fin.succ_ne_zero k).symm) =
      GenLoop.transAt k (lateralGenLoop F hF k 0 (Or.inl rfl)) (topGenLoop F hF) := by
  ext t
  simp only [topGenLoop_apply]
  change F (cubeFaceFold 0 k.succ 1 (Fin.cons 1 t)) =
    if (t k : ℝ) ≤ 1 / 2 then
      F (lateralFaceParameter k 0
        (Function.update t k (Set.projIcc 0 1 zero_le_one (2 * (t k : ℝ)))))
    else topGenLoop F hF
      (Function.update t k (Set.projIcc 0 1 zero_le_one (2 * (t k : ℝ) - 1)))
  split_ifs with ht
  · rw [cubeFaceFold_top_first k t ht]
    congr 1
    simp [lateralFaceParameter]
  · rw [cubeFaceFold_top_second k t (le_of_not_ge ht)]
    exact (topGenLoop_apply F hF _).symm

/-- This is the actual homotopy-group addition law of one geometric face fold.
The multiplication order is the original chronological transAt convention. -/
theorem topGenLoop_fold_class [Nonempty (Fin n)] (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (k : Fin n) :
    cubicalClass (topGenLoop (foldContinuousCube F 0 k.succ)
        (foldContinuousCube_codimTwo F hF 0 k.succ (Fin.succ_ne_zero k).symm)) =
      cubicalClass (topGenLoop F hF) *
        cubicalClass (lateralGenLoop F hF k 0 (Or.inl rfl)) := by
  rw [topGenLoop_fold_eq_transAt]
  exact HomotopyGroup.mul_spec.symm

/-- One lower-side fold fixes the full original bottom map. -/
theorem bottomGenLoop_fold (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (k : Fin n) :
    bottomGenLoop (foldContinuousCube F 0 k.succ)
        (foldContinuousCube_codimTwo F hF 0 k.succ (Fin.succ_ne_zero k).symm) =
      bottomGenLoop F hF := by
  ext t
  simp only [bottomGenLoop_apply]
  exact congrArg F (cubeFaceFold_bottom 0 k.succ (Fin.succ_ne_zero k).symm 1
    (Fin.cons 0 t) rfl)

/-- Once every lateral face is constant, the full cube itself is a relative homotopy. -/
def allSidesConstantHomotopy (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z)
    (hside : ∀ (k : Fin n) (x : Fin (n + 1) → I),
      x k.succ = 0 ∨ x k.succ = 1 → F x = z) :
    (bottomGenLoop F hF).val.HomotopyRel (topGenLoop F hF).val
      (_root_.Cube.boundary (Fin n)) where
  toFun p := F (Fin.cons p.1 p.2)
  continuous_toFun := F.continuous.comp (by
    apply continuous_pi
    intro i
    refine Fin.cases continuous_fst (fun j ↦ ?_) i
    exact (continuous_apply j).comp continuous_snd)
  map_zero_left t := (bottomGenLoop_apply F hF t).symm
  map_one_left t := (topGenLoop_apply F hF t).symm
  prop' r t ht := by
    obtain ⟨k, hk⟩ := ht
    exact (hside k (Fin.cons r t) hk).trans
      ((bottomGenLoop F hF).property t ⟨k, hk⟩).symm

end Topology
