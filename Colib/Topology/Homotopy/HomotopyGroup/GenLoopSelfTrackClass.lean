/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.GenLoopSelfTrack
public import Colib.Topology.Homotopy.HomotopyGroup.CoordinateFundamentalGroup
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.KOneNormalization

/-!
# The higher class of an original fixed-cube self-track

An endpoint-fixed self-track of a positive-dimensional based cube determines
an actual one-higher homotopy class. We use coordinate zero for the loop-space
presentation, the original inverse-prefix cancellation, and `finSuccAboveEquiv`
for the remaining coordinates. The resulting equivalence detects precisely
relative homotopy of the original tracks.

This module concerns one fixed cube. It does not assert descent as that cube
varies, spatial additivity, stable successor compatibility, or a spectrum map.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/GenLoopSelfTrackClass.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, basepoints,
coordinate order and signs are retained under native Colib ownership. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Topology
variable {X : Type u} [TopologicalSpace X] {x : X}

/-- Normalize at the original cube using its first coordinate, then restore the
standard coordinate order in the one-higher homotopy group. -/
def genLoopSelfTrackNormalization (m : ℕ) (p : GenLoop (Fin (m + 1)) X x) :
    FundamentalGroup (GenLoop (Fin (m + 1)) X x) p ≃
      HomotopyGroup.Pi (m + 2) X x := by
  let G := GenLoop (Fin (m + 1)) X x
  let B := GenLoop {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x
  let L : G ≃ₜ Path (GenLoop.const : B) GenLoop.const := GenLoop.loopHomeo (0 : Fin (m + 1))
  have hL : L (GenLoop.const : G) = Path.refl GenLoop.const := by ext s z; rfl
  let M := {j : Fin (m + 2) // j ≠ (0 : Fin (m + 2))}
  let e : GenLoop M X x ≃ₜ G :=
    GenLoop.congr x (finSuccAboveEquiv (0 : Fin (m + 2))).symm
  have he : e GenLoop.const = (GenLoop.const : G) := by ext z; rfl
  exact HomotopyGroup.pi1MulEquivFundamentalGroup.symm.toEquiv.trans
    ((homotopyEquivPiEquiv L.toHomotopyEquiv (x := p) rfl 0).toEquiv.trans
      (HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.trans
        ((loopKOneNormalization (L p)).toEquiv.trans
          ((loopShiftMulEquiv 0).toEquiv.trans
            ((homotopyEquivPiEquiv L.toHomotopyEquiv hL 0).symm.toEquiv.trans
              ((homotopyEquivPiEquiv e.toHomotopyEquiv he 0).symm.toEquiv.trans
                (HomotopyGroup.pi1MulEquivFundamentalGroup.toEquiv.trans
                  (homotopyGroupEquivFundamentalGroup (0 : Fin (m + 2))).symm)))))))

/-- The actual constant self-track has the identity higher class. -/
theorem genLoopSelfTrackNormalization_one (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) : genLoopSelfTrackNormalization m p 1 = 1 := by
  let G := GenLoop (Fin (m + 1)) X x
  let B := GenLoop {j : Fin (m + 1) // j ≠ (0 : Fin (m + 1))} X x
  let L : G ≃ₜ Path (GenLoop.const : B) GenLoop.const := GenLoop.loopHomeo (0 : Fin (m + 1))
  have hL : L (GenLoop.const : G) = Path.refl GenLoop.const := by ext s z; rfl
  let M := {j : Fin (m + 2) // j ≠ (0 : Fin (m + 2))}
  let e : GenLoop M X x ≃ₜ G :=
    GenLoop.congr x (finSuccAboveEquiv (0 : Fin (m + 2))).symm
  have he : e GenLoop.const = (GenLoop.const : G) := by ext z; rfl
  let E : FundamentalGroup G p ≃* HomotopyGroup.Pi (m + 2) X x :=
    HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans
      ((homotopyEquivPiEquiv L.toHomotopyEquiv (x := p) rfl 0).trans
        (HomotopyGroup.pi1MulEquivFundamentalGroup.trans
          ((loopKOneNormalization (L p)).trans
            ((loopShiftMulEquiv 0).trans
              ((homotopyEquivPiEquiv L.toHomotopyEquiv hL 0).symm.trans
                ((homotopyEquivPiEquiv e.toHomotopyEquiv he 0).symm.trans
                  (HomotopyGroup.pi1MulEquivFundamentalGroup.trans
                    (coordinateFundamentalGroupMulEquiv (0 : Fin (m + 2))).symm)))))))
  exact map_one E

@[simp] private theorem genLoopSelfTrackNormalization_id (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) :
    genLoopSelfTrackNormalization m p
      (CategoryTheory.End.of (CategoryTheory.CategoryStruct.id (FundamentalGroupoid.mk p))) = 1 :=
  genLoopSelfTrackNormalization_one m p

/-- The normalized higher class retains the supplied original path, not a chosen replacement. -/
def genLoopSelfTrackClass (m : ℕ) (p : GenLoop (Fin (m + 1)) X x)
    (α : Path p p) : HomotopyGroup.Pi (m + 2) X x :=
  genLoopSelfTrackNormalization m p (FundamentalGroup.fromPath ⟦α⟧)

@[simp] theorem genLoopSelfTrackClass_refl (m : ℕ)
    (p : GenLoop (Fin (m + 1)) X x) :
    genLoopSelfTrackClass m p (Path.refl p) = 1 :=
  genLoopSelfTrackNormalization_one m p

/-- Equality of higher classes is exactly homotopy relative to the original two endpoints. -/
theorem genLoopSelfTrackClass_eq_iff (m : ℕ) (p : GenLoop (Fin (m + 1)) X x)
    (α β : Path p p) :
    genLoopSelfTrackClass m p α = genLoopSelfTrackClass m p β ↔ α.Homotopic β := by
  change genLoopSelfTrackNormalization m p (FundamentalGroup.fromPath ⟦α⟧) =
    genLoopSelfTrackNormalization m p (FundamentalGroup.fromPath ⟦β⟧) ↔ _
  constructor
  · intro h
    exact Quotient.exact (congrArg CategoryTheory.End.asHom
      ((genLoopSelfTrackNormalization m p).injective h))
  · intro h
    exact congrArg (genLoopSelfTrackNormalization m p) (congrArg FundamentalGroup.fromPath
      (Quotient.sound h))

/-- The actual class vanishes precisely when the original self-track contracts rel endpoints. -/
theorem genLoopSelfTrackClass_eq_one_iff (m : ℕ) (p : GenLoop (Fin (m + 1)) X x)
    (α : Path p p) :
    genLoopSelfTrackClass m p α = 1 ↔ α.Homotopic (Path.refl p) := by
  rw [← genLoopSelfTrackClass_refl m p]
  exact genLoopSelfTrackClass_eq_iff m p α (Path.refl p)

end Topology
