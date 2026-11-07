/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.HomotopyGroup.CoordinateTransposition
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift

/-!
The literal two loop-shift inverses retain the coordinate-transposition sign, including outer degree
zero.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/Loop/TransposeSign.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, basepoints,
coefficients and signs are retained with native Colib dependencies. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u
namespace Topology

lemma cubeCoordinateSwap_zero_one_tail_tail {n : ℕ} (z : Fin (n + 2) → unitInterval) :
    Fin.tail (Fin.tail (cubeCoordinateSwap 0 1 z)) = Fin.tail (Fin.tail z) := by
  funext i
  have h : i.succ.succ ≠ (1 : Fin (n+2)) := by
    intro e
    have he := congrArg Fin.val e
    simp only [Fin.val_succ, Fin.val_one] at he
    omega
  simp [Fin.tail, cubeCoordinateSwap, h]

variable {X : Type u} [TopologicalSpace X] {x : X}

/-- A literal double-loop coordinate interchange becomes the first two-coordinate
swap on the actual twice-uncurried cube. -/
theorem loopUncurry_twice_coordinateSwap {n : ℕ}
    (f : C(Path (Path.refl x) (Path.refl x), Path (Path.refl x) (Path.refl x)))
    (hf : f (Path.refl (Path.refl x)) = Path.refl (Path.refl x))
    (hcoord : ∀ γ s t, f γ s t = γ t s)
    (p : GenLoop (Fin n) (Path (Path.refl x) (Path.refl x)) (Path.refl (Path.refl x))) :
    loopUncurry (loopUncurry (GenLoop.postcomp f hf p)) =
      transposeGenLoop (0 : Fin (n+2)) 1 (by exact Fin.zero_ne_one) (loopUncurry (loopUncurry p)) :=
        by
  ext z
  change f (p (Fin.tail (Fin.tail z))) (z 1) (z 0) =
    p (Fin.tail (Fin.tail (cubeCoordinateSwap 0 1 z)))
      ((cubeCoordinateSwap 0 1 z) 1) ((cubeCoordinateSwap 0 1 z) 0)
  rw [hcoord, cubeCoordinateSwap_zero_one_tail_tail]
  simp [cubeCoordinateSwap]

/-- The original two loop-shift inverses identify a double-loop transpose with
inversion on the genuine original homotopy group. This includes outer degree zero. -/
theorem loopShiftEquiv_twice_coordinateSwap (n : ℕ)
    (f : C(Path (Path.refl x) (Path.refl x), Path (Path.refl x) (Path.refl x)))
    (hf : f (Path.refl (Path.refl x)) = Path.refl (Path.refl x))
    (hcoord : ∀ γ s t, f γ s t = γ t s)
    (a : HomotopyGroup.Pi n (Path (Path.refl x) (Path.refl x)) (Path.refl (Path.refl x))) :
    (loopShiftEquiv (x := x) (n+1)).symm
      ((loopShiftEquiv (x := Path.refl x) n).symm (HomotopyGroup.map f hf a)) =
    ((loopShiftEquiv (x := x) (n+1)).symm
      ((loopShiftEquiv (x := Path.refl x) n).symm a))⁻¹ := by
  refine Quotient.inductionOn a (fun p ↦ ?_)
  change (Quotient.mk' (loopUncurry (loopUncurry (GenLoop.postcomp f hf p))) :
      HomotopyGroup.Pi (n+2) X x) =
    ((Quotient.mk' (loopUncurry (loopUncurry p)))⁻¹ : HomotopyGroup.Pi (n+2) X x)
  exact (congrArg (fun q ↦ (Quotient.mk' q : HomotopyGroup.Pi (n+2) X x))
    (loopUncurry_twice_coordinateSwap f hf hcoord p)).trans
      (transposeGenLoop_class 0 1 (by exact Fin.zero_ne_one) (loopUncurry (loopUncurry p)))

end Topology

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u v
namespace Topology
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    {x : X} {y : Y}

/-- Uncurrying an original loop-space map retains the actual underlying based map. -/
@[simp] theorem loopUncurry_postcomp {n : ℕ} (f : C(X, Y)) (hf : f x = y)
    (p : GenLoop (Fin n) (Path x x) (Path.refl x)) :
    loopUncurry (GenLoop.postcomp (basedLoopMap f hf) (basedLoopMap_refl f hf) p) =
      GenLoop.postcomp f hf (loopUncurry p) := by
  ext z
  rfl

/-- The literal parameter-correct loop structure anti-commutes with the original
loop-degree shift. The minus sign comes from the proved cube transposition. -/
theorem loopShift_parameter_structure_sign (n : ℕ)
    (f : C(X, Path y y)) (hf : f x = Path.refl y)
    (τ : C(Path (Path.refl y) (Path.refl y), Path (Path.refl y) (Path.refl y)))
    (hτ : τ (Path.refl (Path.refl y)) = Path.refl (Path.refl y))
    (hcoord : ∀ γ s t, τ γ s t = γ t s)
    (a : HomotopyGroup.Pi n (Path x x) (Path.refl x)) :
    (loopShiftEquiv (x := y) (n+1)).symm
      ((loopShiftEquiv (x := Path.refl y) n).symm
        (HomotopyGroup.map (τ.comp (basedLoopMap f hf))
          ((congrArg τ (basedLoopMap_refl f hf)).trans hτ) a)) =
    ((loopShiftEquiv (x := y) (n+1)).symm
      (HomotopyGroup.map f hf ((loopShiftEquiv (x := x) n).symm a)))⁻¹ := by
  rw [HomotopyGroup.map_comp (basedLoopMap f hf) (basedLoopMap_refl f hf) τ hτ a]
  rw [loopShiftEquiv_twice_coordinateSwap n τ hτ hcoord]
  congr 1
  apply congrArg (loopShiftEquiv (x := y) (n+1)).symm
  refine Quotient.inductionOn a (fun p ↦ ?_)
  exact congrArg (fun q ↦ (Quotient.mk' q : HomotopyGroup.Pi (n+1) (Path y y) (Path.refl y)))
    (loopUncurry_postcomp f hf p)

end Topology
