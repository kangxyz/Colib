/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrackClass

/-!
# The actual normalized cube representing a self-track

The original track is first translated by the inverse of the original loop.
Its two endpoints are connected to the constant loop by the same displayed
cancellation. Uncurrying gives a genuine based cube, with track time first
and the original normalization coordinate second. No representative is chosen
from a homotopy class.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/GenLoopNormalizedSelfTrack.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, basepoints,
coordinate order and signs are retained under native Colib ownership. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology

/-- Normalize an actual loop-space self-track using the inverse prefix and both cancellations. -/
def loopNormalizedSelfTrack {X : Type u} [TopologicalSpace X] {x : X}
    (γ : Path x x) (α : Path γ γ) : Path (Path.refl x) (Path.refl x) :=
  (loopInversePrefixCancellation γ).symm.trans
    (((α.map (loopLeftTranslationEquiv γ.symm).continuous).cast
      (loopLeftTranslationEquiv_apply _ _).symm
      (loopLeftTranslationEquiv_apply _ _).symm).trans
        (loopInversePrefixCancellation γ))

/-- The existing normalization has exactly the displayed inverse-prefix representative. -/
theorem loopKOneNormalization_path {X : Type u} [TopologicalSpace X] {x : X}
    (γ : Path x x) (α : Path γ γ) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
      (loopShiftMulEquiv 0 (loopKOneNormalization γ ⟦α⟧)) =
        (⟦loopNormalizedSelfTrack γ α⟧ : FundamentalGroup _ (Path.refl x)) := by
  simp only [loopKOneNormalization, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (pathTransport (loopInversePrefixCancellation γ) 1
      (HomotopyGroup.map (loopLeftTranslationEquiv γ.symm).toFun
        (loopLeftTranslationEquiv_apply _ _)
        (HomotopyGroup.pi1MulEquivFundamentalGroup.symm ⟦α⟧))) = _
  rw [piOneEquivFundamentalGroup_pathTransport,
    HomotopyGroup.pi1MulEquivFundamentalGroup_naturality,
    MulEquiv.apply_symm_apply, FundamentalGroup.mapOfEq_apply]
  rfl

/-- For a homeomorphism the inverse based equivalence is the actual inverse map. -/
theorem homotopyEquivPiEquiv_homeomorph_symm {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {x : X} {y : Y}
    (h : e.toHomotopyEquiv.toFun x = y)
    (h' : e.symm.toHomotopyEquiv.toFun y = x) (n : ℕ)
    (a : HomotopyGroup.Pi (n + 1) Y y) :
    (homotopyEquivPiEquiv e.toHomotopyEquiv h n).symm a =
      HomotopyGroup.piMap n e.symm.toHomotopyEquiv.toFun h' a := by
  apply (homotopyEquivPiEquiv e.toHomotopyEquiv h n).injective
  rw [MulEquiv.apply_symm_apply, homotopyEquivPiEquiv_apply]
  induction a using Quotient.inductionOn with
  | h p =>
    apply congrArg Quotient.mk'
    ext z
    exact (e.apply_symm_apply (p z)).symm

/-- The inverse homeomorphism retains the actual path representative in degree one. -/
theorem piOneEquivFundamentalGroup_homeomorph_symm {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y) {x : X} {y : Y}
    (h : e.toHomotopyEquiv.toFun x = y)
    (h' : e.symm.toHomotopyEquiv.toFun y = x) (a : HomotopyGroup.Pi 1 Y y) :
    HomotopyGroup.pi1MulEquivFundamentalGroup
      ((homotopyEquivPiEquiv e.toHomotopyEquiv h 0).symm a) =
        FundamentalGroup.mapOfEq e.symm.toHomotopyEquiv.toFun h'
          (HomotopyGroup.pi1MulEquivFundamentalGroup a) := by
  rw [homotopyEquivPiEquiv_homeomorph_symm e h h']
  exact HomotopyGroup.pi1MulEquivFundamentalGroup_naturality _ _ _

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- The normalized track, restored to the original cube space at its constant cube. -/
def genLoopNormalizedSelfTrackPath (m : ℕ) (p : GenLoop (Fin (m + 1)) X x)
    (α : Path p p) :
    Path (GenLoop.const : GenLoop (Fin (m + 1)) X x) GenLoop.const := by
  let L := GenLoop.loopHomeo (X := X) (x := x) (0 : Fin (m + 1))
  have hL : L.toHomotopyEquiv.toFun GenLoop.const = Path.refl GenLoop.const := by
    ext s z
    rfl
  have hL' : L.symm.toHomotopyEquiv.toFun (Path.refl GenLoop.const) = GenLoop.const :=
    (congrArg L.symm hL).symm.trans (L.symm_apply_apply _)
  exact basedLoopMap L.symm.toHomotopyEquiv.toFun hL'
    (loopNormalizedSelfTrack (L.toHomotopyEquiv.toFun p)
      (α.map L.toHomotopyEquiv.toFun.continuous))

/-- The actual normalized one-higher cube uses the new first coordinate for track time. -/
def genLoopNormalizedSelfTrackCube (m : ℕ) (p : GenLoop (Fin (m + 1)) X x)
    (α : Path p p) : GenLoop (Fin (m + 2)) X x := by
  let M := {j : Fin (m + 2) // j ≠ (0 : Fin (m + 2))}
  let e : GenLoop M X x ≃ₜ GenLoop (Fin (m + 1)) X x :=
    GenLoop.congr x (finSuccAboveEquiv (0 : Fin (m + 2))).symm
  have he : e.toHomotopyEquiv.toFun GenLoop.const = GenLoop.const := by ext z; rfl
  have he' : e.symm.toHomotopyEquiv.toFun GenLoop.const = GenLoop.const :=
    (congrArg e.symm he).symm.trans (e.symm_apply_apply _)
  exact GenLoop.fromLoop (0 : Fin (m + 2))
    (basedLoopMap e.symm.toHomotopyEquiv.toFun he'
      (genLoopNormalizedSelfTrackPath m p α))

/-- The new first coordinate is exactly track time; the remaining coordinates keep their order. -/
@[simp] theorem genLoopNormalizedSelfTrackCube_apply (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (α : Path p p) (z : Fin (m + 2) → unitInterval) :
    genLoopNormalizedSelfTrackCube m p α z =
      genLoopNormalizedSelfTrackPath m p α (z 0) (Fin.tail z) := rfl

/-- The explicit normalized cube represents the already defined original higher self-track class. -/
theorem genLoopNormalizedSelfTrackCube_class (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) (α : Path p p) :
    (⟦genLoopNormalizedSelfTrackCube m p α⟧ : HomotopyGroup.Pi (m + 2) X x) =
      genLoopSelfTrackClass m p α := by
  let G := GenLoop (Fin (m + 1)) X x
  let B := GenLoop {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x
  let L : G ≃ₜ Path (GenLoop.const : B) GenLoop.const := GenLoop.loopHomeo (0 : Fin (m + 1))
  have hL : L.toHomotopyEquiv.toFun (GenLoop.const : G) = Path.refl GenLoop.const := by
    ext s z
    rfl
  have hL' : L.symm.toHomotopyEquiv.toFun (Path.refl GenLoop.const) = GenLoop.const :=
    (congrArg L.symm hL).symm.trans (L.symm_apply_apply _)
  let M := {j : Fin (m + 2) // j ≠ (0 : Fin (m + 2))}
  let e : GenLoop M X x ≃ₜ G :=
    GenLoop.congr x (finSuccAboveEquiv (0 : Fin (m + 2))).symm
  have he : e.toHomotopyEquiv.toFun GenLoop.const = (GenLoop.const : G) := by ext z; rfl
  have he' : e.symm.toHomotopyEquiv.toFun GenLoop.const = GenLoop.const :=
    (congrArg e.symm he).symm.trans (e.symm_apply_apply _)
  apply (homotopyGroupEquivFundamentalGroup (0 : Fin (m + 2))).injective
  simp only [genLoopSelfTrackClass, genLoopSelfTrackNormalization, Equiv.trans_apply,
    MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, Equiv.apply_symm_apply]
  change (⟦GenLoop.toLoop (0 : Fin (m + 2))
      (genLoopNormalizedSelfTrackCube m p α)⟧ : FundamentalGroup _ _) =
    HomotopyGroup.pi1MulEquivFundamentalGroup
      ((homotopyEquivPiEquiv e.toHomotopyEquiv he 0).symm
        ((homotopyEquivPiEquiv L.toHomotopyEquiv hL 0).symm
          (loopShiftMulEquiv 0 (loopKOneNormalization (L.toHomotopyEquiv.toFun p)
            (HomotopyGroup.pi1MulEquivFundamentalGroup
              (HomotopyGroup.map L.toHomotopyEquiv.toFun rfl
                (HomotopyGroup.pi1MulEquivFundamentalGroup.symm ⟦α⟧)))))))
  rw [piOneEquivFundamentalGroup_homeomorph_symm e he he',
    piOneEquivFundamentalGroup_homeomorph_symm L hL hL',
    HomotopyGroup.pi1MulEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply]
  have hmap : FundamentalGroup.mapOfEq L.toHomotopyEquiv.toFun rfl
      (⟦α⟧ : FundamentalGroup G p) =
        (⟦α.map L.toHomotopyEquiv.toFun.continuous⟧ :
          FundamentalGroup _ (L.toHomotopyEquiv.toFun p)) := by
    rw [FundamentalGroup.mapOfEq_apply]
    rfl
  rw [hmap, loopKOneNormalization_path, FundamentalGroup.mapOfEq_apply,
    FundamentalGroup.mapOfEq_apply]
  change (⟦GenLoop.toLoop (0 : Fin (m + 2))
      (GenLoop.fromLoop (0 : Fin (m + 2)) _)⟧ : FundamentalGroup _ _) = _
  rw [GenLoop.to_from]
  rfl

end Topology
