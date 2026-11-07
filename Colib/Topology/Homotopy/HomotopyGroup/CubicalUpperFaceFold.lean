/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.CubicalFaceFold

/-!
# The upper-side fold and the exact original multiplication order

Conjugating the geometric lower fold by coordinate reflection kills the upper
side. The top class becomes the inverse upper-side class followed by the old
top class. This uses the original reflection/inversion law and does not assume
commutativity or signed homotopy addition.
-/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/CubicalUpperFaceFold.lean` at
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

@[simp] theorem cubicalClass_symmAt [Nonempty (Fin n)] (k : Fin n)
    (p : GenLoop (Fin n) Z z) : cubicalClass (GenLoop.symmAt k p) = (cubicalClass p)⁻¹ :=
  HomotopyGroup.inv_spec.symm

@[simp] theorem cubicalClass_const [Nonempty (Fin n)] :
    cubicalClass (GenLoop.const : GenLoop (Fin n) Z z) = 1 := rfl

/-- Reflecting a lateral ambient coordinate reflects the matching top-domain coordinate. -/
theorem cubeCoordinateReflect_cons (k : Fin n) (r : I) (t : Fin n → I) :
    cubeCoordinateReflect k.succ (Fin.cons r t) = Fin.cons r (cubeCoordinateReflect k t) := by
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [cubeCoordinateReflect, (Fin.succ_ne_zero k).symm]
  · simp [cubeCoordinateReflect]

/-- Reflection of the full cube induces the original coordinate reversal on its top loop. -/
theorem topGenLoop_reflect (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (k : Fin n) :
    topGenLoop (reflectContinuousCube F k.succ)
        (reflectContinuousCube_codimTwo F hF k.succ) =
      GenLoop.symmAt k (topGenLoop F hF) := by
  ext t
  rw [topGenLoop_apply]
  change F (cubeCoordinateReflect k.succ (Fin.cons 1 t)) =
    topGenLoop F hF (cubeCoordinateReflect k t)
  rw [cubeCoordinateReflect_cons]
  exact (topGenLoop_apply F hF _).symm

/-- Reflection exchanges the displayed lateral faces without reversing their time parameter. -/
theorem lateralGenLoop_reflect_zero (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (k : Fin n) :
    lateralGenLoop (reflectContinuousCube F k.succ)
        (reflectContinuousCube_codimTwo F hF k.succ) k 0 (Or.inl rfl) =
      lateralGenLoop F hF k 1 (Or.inr rfl) := by
  ext t
  change F (cubeCoordinateReflect k.succ (lateralFaceParameter k 0 t)) =
    F (lateralFaceParameter k 1 t)
  apply congrArg F
  simp only [lateralFaceParameter, cubeCoordinateReflect_cons]
  ext i
  refine Fin.cases (by rfl) (fun j ↦ ?_) i
  by_cases hj : j = k
  · subst j; simp [cubeCoordinateReflect]
  · simp [cubeCoordinateReflect, hj]

/-- The upper-folded top is the reflected top of the lower-folded reflected cube. -/
theorem topGenLoop_upperFold_eq_symmAt (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (k : Fin n) :
    topGenLoop (foldUpperContinuousCube F 0 k.succ)
        (foldUpperContinuousCube_codimTwo F hF 0 k.succ (Fin.succ_ne_zero k).symm) =
      GenLoop.symmAt k (topGenLoop (foldContinuousCube (reflectContinuousCube F k.succ) 0 k.succ)
        (foldContinuousCube_codimTwo _ (reflectContinuousCube_codimTwo F hF k.succ)
          0 k.succ (Fin.succ_ne_zero k).symm)) :=
  topGenLoop_reflect _ _ k

/-- The original noncommutative multiplication order of the geometric upper-side fold. -/
theorem topGenLoop_upperFold_class [Nonempty (Fin n)] (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (k : Fin n) :
    cubicalClass (topGenLoop (foldUpperContinuousCube F 0 k.succ)
        (foldUpperContinuousCube_codimTwo F hF 0 k.succ (Fin.succ_ne_zero k).symm)) =
      (cubicalClass (lateralGenLoop F hF k 1 (Or.inr rfl)))⁻¹ *
        cubicalClass (topGenLoop F hF) := by
  rw [topGenLoop_upperFold_eq_symmAt F hF k, cubicalClass_symmAt,
    topGenLoop_fold_class _ (reflectContinuousCube_codimTwo F hF k.succ),
    topGenLoop_reflect F hF, lateralGenLoop_reflect_zero F hF, cubicalClass_symmAt,
    mul_inv_rev, inv_inv]

/-- The upper-side fold also fixes the full original bottom loop. -/
theorem bottomGenLoop_upperFold (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (k : Fin n) :
    bottomGenLoop (foldUpperContinuousCube F 0 k.succ)
        (foldUpperContinuousCube_codimTwo F hF 0 k.succ (Fin.succ_ne_zero k).symm) =
      bottomGenLoop F hF := by
  ext t
  simp only [bottomGenLoop_apply]
  exact congrArg F (cubeUpperFaceFold_bottom 0 k.succ (Fin.succ_ne_zero k).symm 1
    (Fin.cons 0 t) rfl)

/-- Lower folding leaves its opposite upper side unchanged as an actual map. -/
theorem lateralGenLoop_fold_upper (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (k : Fin n) :
    lateralGenLoop (foldContinuousCube F 0 k.succ)
        (foldContinuousCube_codimTwo F hF 0 k.succ (Fin.succ_ne_zero k).symm)
        k 1 (Or.inr rfl) = lateralGenLoop F hF k 1 (Or.inr rfl) := by
  ext t
  exact congrArg F (cubeFaceFold_right 0 k.succ (Fin.succ_ne_zero k).symm 1
    (lateralFaceParameter k 1 t) (by simp [lateralFaceParameter]))

/-- Upper folding leaves its opposite lower side unchanged as an actual map. -/
theorem lateralGenLoop_upperFold_lower (F : C((Fin (n + 1) → I), Z))
    (hF : ∀ x ∈ cubeCodimTwoBoundary (Fin (n + 1)), F x = z) (k : Fin n) :
    lateralGenLoop (foldUpperContinuousCube F 0 k.succ)
        (foldUpperContinuousCube_codimTwo F hF 0 k.succ (Fin.succ_ne_zero k).symm)
        k 0 (Or.inl rfl) = lateralGenLoop F hF k 0 (Or.inl rfl) := by
  ext t
  exact congrArg F (cubeUpperFaceFold_left 0 k.succ (Fin.succ_ne_zero k).symm 1
    (lateralFaceParameter k 0 t) (by simp [lateralFaceParameter]))

end Topology
