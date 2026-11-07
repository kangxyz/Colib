/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.ComponentTranslation
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.Reversal

/-!
# Original left-prefix translations of loop components

The actual left prefix is obtained by reversing the existing right translation twice. Its
forward map is the literal original path concatenation. The specified constant-suffix removal
and every original loop coordinate are retained, rather than choosing a path between components.
-/
/-! Implementation source: `Quillen/Topology/HomotopyGroups/Loop/LeftComponentTranslation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, basepoints,
coefficients and signs are retained with native Colib dependencies. -/
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u
namespace Topology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- Original left concatenation is a homotopy equivalence, using the actual right translation. -/
def loopLeftTranslationEquiv (γ : Path x x) :
    ContinuousMap.HomotopyEquiv (Path x x) (Path x x) :=
  (loopReversalHomeomorph x).toHomotopyEquiv.trans
    ((loopRightTranslationEquiv γ.symm).trans (loopReversalHomeomorph x).toHomotopyEquiv)

/-- The specified forward map is exactly the original left-prefix concatenation. -/
theorem loopLeftTranslationEquiv_apply (γ δ : Path x x) :
    loopLeftTranslationEquiv γ δ = γ.trans δ := by
  change (loopRightTranslationEquiv γ.symm δ.symm).symm = _
  rw [loopRightTranslationEquiv_apply, Path.trans_symm, Path.symm_symm, Path.symm_symm]

/-- The unchanged based map preserves every original left-prefixed loop. -/
theorem loopLeftTranslationEquiv_naturality (f : C(X, Y)) (h : f x = y) (γ : Path x x) :
    (basedLoopMap f h).comp (loopLeftTranslationEquiv γ).toFun =
      (loopLeftTranslationEquiv (basedLoopMap f h γ)).toFun.comp (basedLoopMap f h) := by
  ext δ t
  change basedLoopMap f h (loopLeftTranslationEquiv γ δ) t =
    loopLeftTranslationEquiv (basedLoopMap f h γ) (basedLoopMap f h δ) t
  rw [loopLeftTranslationEquiv_apply, loopLeftTranslationEquiv_apply, basedLoopMap_trans]

/-- The displayed constant suffix is removed by the original reversed constant-prefix track. -/
def loopRightUnitPath (γ : Path x x) : Path (γ.trans (Path.refl x)) γ :=
  ((loopLeftUnitPath γ.symm).map Path.continuous_symm).cast
    (by simp [Path.trans_symm]) (by simp)

/-- Both suffix-removal time and the original reversed loop coordinate remain literal. -/
theorem loopRightUnitPath_apply (γ : Path x x) (s t : unitInterval) :
    loopRightUnitPath γ s t = loopLeftUnitPath γ.symm s (unitInterval.symm t) := rfl

/-- Suffix removal commutes with the original based map at both independent coordinates. -/
theorem loopRightUnitPath_naturality (f : C(X, Y)) (h : f x = y) (γ : Path x x)
    (s t : unitInterval) :
    basedLoopMap f h (loopRightUnitPath γ s) t =
      loopRightUnitPath (basedLoopMap f h γ) s t := rfl

/-- The literal left-prefix map gives the equivalence based at its actual displayed image. -/
def loopLeftTranslationHomotopyEquiv (γ : Path x x) (n : ℕ) :
    HomotopyGroup.Pi n (Path x x) (Path.refl x) ≃
      HomotopyGroup.Pi n (Path x x) (γ.trans (Path.refl x)) :=
  Equiv.ofBijective
    (HomotopyGroup.map (loopLeftTranslationEquiv γ).toFun
      (loopLeftTranslationEquiv_apply γ (Path.refl x)))
    (homotopyGroupMap_bijective_of_homotopyEquiv (loopLeftTranslationEquiv γ)
      (loopLeftTranslationEquiv_apply γ (Path.refl x)) n)

/-- Left prefix followed by its specified suffix removal reaches the original loop component. -/
def loopLeftComponentHomotopyEquiv (γ : Path x x) (n : ℕ) :
    HomotopyGroup.Pi n (Path x x) (Path.refl x) ≃ HomotopyGroup.Pi n (Path x x) γ :=
  (loopLeftTranslationHomotopyEquiv γ n).trans (pathTransport (loopRightUnitPath γ) n)

/-- The prescribed left-component equivalence is natural under the unchanged based loop map. -/
theorem loopLeftComponentHomotopyEquiv_naturality (f : C(X, Y)) (h : f x = y)
    (γ : Path x x) (n : ℕ) (a : HomotopyGroup.Pi n (Path x x) (Path.refl x)) :
    loopLeftComponentHomotopyEquiv (basedLoopMap f h γ) n
      (HomotopyGroup.map (basedLoopMap f h) (basedLoopMap_refl f h) a) =
        HomotopyGroup.map (basedLoopMap f h) rfl (loopLeftComponentHomotopyEquiv γ n a) := by
  let g := basedLoopMap f h
  have ht : g (γ.trans (Path.refl x)) = (g γ).trans (Path.refl y) := by
    rw [basedLoopMap_trans, basedLoopMap_refl]
  have hn : HomotopyGroup.map g ht (loopLeftTranslationHomotopyEquiv γ n a) =
      loopLeftTranslationHomotopyEquiv (g γ) n
        (HomotopyGroup.map g (basedLoopMap_refl f h) a) := by
    induction a using Quotient.inductionOn with
    | h p =>
      change Quotient.mk' (GenLoop.postcomp g ht
        (GenLoop.postcomp (loopLeftTranslationEquiv γ).toFun _ p)) =
          Quotient.mk' (GenLoop.postcomp (loopLeftTranslationEquiv (g γ)).toFun _
            (GenLoop.postcomp g _ p))
      apply congrArg Quotient.mk'
      ext s t
      exact congrArg (fun q : C(Path x x, Path y y) ↦ q (p s) t)
        (loopLeftTranslationEquiv_naturality f h γ)
  change pathTransport (loopRightUnitPath (g γ)) n
    (loopLeftTranslationHomotopyEquiv (g γ) n
      (HomotopyGroup.map g (basedLoopMap_refl f h) a)) = _
  rw [← hn]
  exact pathTransport_naturality_of_track g (loopRightUnitPath γ) (loopRightUnitPath (g γ))
    ht rfl (fun s ↦ by ext t; exact loopRightUnitPath_naturality f h γ s t)
    n (loopLeftTranslationHomotopyEquiv γ n a)

end Topology
