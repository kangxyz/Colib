/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.Topology.Realization.MonomorphismHEP
public import Colib.Topology.Category.TopCat.SequentialColimit.HomotopyInvariance
public import Mathlib.CategoryTheory.Limits.Connected

/-! The sequential monomorphism case of filtered realization invariance.
This is a new consequence of the native sequential HEP theorem, adapted to the
actual natural-number resolution strata. It does not assert general filtered
invariance or assume that arbitrary filtered colimits preserve equivalences. -/
@[expose] public noncomputable section
open CategoryTheory Limits TopCat
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.FilteredRealization
variable (F : ℕ ⥤ SSet.{u}) (c : Cocone F) (hc : IsColimit c)

/-- The exact realized stage-zero comparisons form a natural transformation. -/
def stageZeroComparison : (Functor.const ℕ).obj |F.obj 0| ⟶ F ⋙ SSet.toTop where
  app n := SSet.toTop.map (F.map (homOfLE (Nat.zero_le n)))
  naturality n m f := by
    change 𝟙 _ ≫ SSet.toTop.map (F.map (homOfLE (Nat.zero_le m))) =
      SSet.toTop.map (F.map (homOfLE (Nat.zero_le n))) ≫ SSet.toTop.map (F.map f)
    rw [Category.id_comp]
    rw [← Functor.map_comp, ← F.map_comp]
    rfl

/-- A sequential simplicial diagram with mono successor maps and actual
stage-zero equivalences has the specified colimit leg as a homotopy equivalence. -/
def sequentialStageZeroHomotopyEquiv
    (hm : ∀ n, Mono (F.map (homOfLE (Nat.le_succ n))))
    (e : ∀ n, ContinuousMap.HomotopyEquiv |F.obj 0| |F.obj n|)
    (he : ∀ n, (e n).toFun =
      (SSet.toTop.map (F.map (homOfLE (Nat.zero_le n)))).hom) :
    ContinuousMap.HomotopyEquiv |F.obj 0| |c.pt| := by
  let E : ContinuousMap.HomotopyEquiv |F.obj 0| |c.pt| :=
    sequentialCoconeHomotopyEquiv (stageZeroComparison F)
    (fun n => by
      change HomotopyExtensionProperty (𝟙 |F.obj 0|)
      exact homotopyExtensionProperty_of_isIso _)
    (fun n => by
      let := hm n
      exact SSet.homotopyExtensionProperty_realization_mono _)
    e he (constCocone ℕ |F.obj 0|) (isColimitConstCocone ℕ |F.obj 0|)
    (SSet.toTop.mapCocone c) (isColimitOfPreserves SSet.toTop hc)
  have hE : E.toFun = (SSet.toTop.map (c.ι.app 0)).hom := by
    dsimp only [E]
    rw [sequentialCoconeHomotopyEquiv_toFun]
    apply congrArg TopCat.Hom.hom
    have h := (isColimitConstCocone ℕ |F.obj 0|).ι_map
      (SSet.toTop.mapCocone c) (stageZeroComparison F) 0
    simpa [stageZeroComparison, constCocone] using h
  exact { E with
    toFun := (SSet.toTop.map (c.ι.app 0)).hom
    left_inv := by simpa only [hE] using E.left_inv
    right_inv := by simpa only [hE] using E.right_inv }

@[simp] theorem sequentialStageZeroHomotopyEquiv_toFun
    (hm : ∀ n, Mono (F.map (homOfLE (Nat.le_succ n))))
    (e : ∀ n, ContinuousMap.HomotopyEquiv |F.obj 0| |F.obj n|)
    (he : ∀ n, (e n).toFun =
      (SSet.toTop.map (F.map (homOfLE (Nat.zero_le n)))).hom) :
    (sequentialStageZeroHomotopyEquiv F c hc hm e he).toFun =
      (SSet.toTop.map (c.ι.app 0)).hom := rfl
end Topology.FilteredRealization

attribute [colib_tag "COL-0238",
  colib_ref "WeibelKBook" "V, proof of Theorem 3.1, page 20" "background"
    "Filtered nerves and sequential resolution unions"]
  Topology.FilteredRealization.sequentialStageZeroHomotopyEquiv
