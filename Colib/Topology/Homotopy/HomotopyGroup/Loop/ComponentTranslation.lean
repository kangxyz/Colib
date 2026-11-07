/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.WeakEquivalence
public import Colib.Topology.HomotopyFiber.BasepointTransport
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.MovingBasepoint

/-!
# Actual translations between loop-space components

Right concatenation by a displayed loop is a genuine homotopy equivalence, obtained from the
existing original-fiber basepoint transport. The forward map is exactly the original path
concatenation, and its square with every unchanged based loop map commutes strictly.
The constant-prefix removal track is also retained pointwise and natural in the original map.
-/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/Loop/ComponentTranslation.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, basepoints,
coefficients and signs are retained with native Colib dependencies. -/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped Topology unitInterval

universe u

namespace Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- Actual right translation on based loops is a genuine homotopy equivalence. -/
def loopRightTranslationEquiv (γ : Path x x) :
    ContinuousMap.HomotopyEquiv (Path x x) (Path x x) :=
  (loopHomotopyFiberHomeomorph x).toHomotopyEquiv.trans
    ((HomotopyFiber.basepointTransportEquiv (ContinuousMap.const PUnit.{u + 1} x) γ).trans
      (loopHomotopyFiberHomeomorph x).symm.toHomotopyEquiv)

/-- The original translation keeps exactly the standard concatenation parametrization. -/
@[simp] theorem loopRightTranslationEquiv_apply (γ δ : Path x x) :
    loopRightTranslationEquiv γ δ = δ.trans γ := by
  apply Path.ext
  funext t
  exact congrArg (fun p : C(unitInterval, X) ↦ p t)
    (HomotopyFiber.basepointTransportEquiv_path (ContinuousMap.const PUnit.{u + 1} x)
      γ (loopHomotopyFiberHomeomorph x δ))

/-- The unchanged based loop map commutes with the actual concatenation of original loops. -/
@[simp] theorem basedLoopMap_trans (f : C(X, Y)) (h : f x = y) (γ δ : Path x x) :
    basedLoopMap f h (γ.trans δ) = (basedLoopMap f h γ).trans (basedLoopMap f h δ) := by
  ext t
  change f ((γ.trans δ) t) = ((basedLoopMap f h γ).trans (basedLoopMap f h δ)) t
  simp only [Path.trans_apply]
  split_ifs <;> rfl

/-- Strict naturality retains the whole original concatenated loops. -/
theorem loopRightTranslationEquiv_naturality (f : C(X, Y)) (h : f x = y) (γ : Path x x) :
    (basedLoopMap f h).comp (loopRightTranslationEquiv γ).toFun =
      (loopRightTranslationEquiv (basedLoopMap f h γ)).toFun.comp (basedLoopMap f h) := by
  ext δ t
  change basedLoopMap f h (loopRightTranslationEquiv γ δ) t =
    loopRightTranslationEquiv (basedLoopMap f h γ) (basedLoopMap f h δ) t
  rw [loopRightTranslationEquiv_apply, loopRightTranslationEquiv_apply, basedLoopMap_trans]

/-- The actual constant-prefix removal gives the displayed point of its loop component. -/
def loopLeftUnitPath (γ : Path x x) : Path ((Path.refl x).trans γ) γ where
  toFun s := Path.delayReflLeft s γ
  continuous_toFun := Path.continuous_delayReflLeft.comp (continuous_id.prodMk continuous_const)
  source' := Path.delayReflLeft_zero γ
  target' := Path.delayReflLeft_one γ

/-- Constant-prefix removal is natural at every original loop coordinate and track time. -/
theorem loopLeftUnitPath_naturality (f : C(X, Y)) (h : f x = y) (γ : Path x x)
    (s t : unitInterval) :
    basedLoopMap f h (loopLeftUnitPath γ s) t = loopLeftUnitPath (basedLoopMap f h γ) s t := rfl

/-- The actual right-translation map gives an equivalence based at the displayed concatenation
of the constant loop and the original loop. -/
def loopRightTranslationHomotopyEquiv (γ : Path x x) (n : ℕ) :
    HomotopyGroup.Pi n (Path x x) (Path.refl x) ≃
      HomotopyGroup.Pi n (Path x x) ((Path.refl x).trans γ) :=
  Equiv.ofBijective
    (HomotopyGroup.map (loopRightTranslationEquiv γ).toFun
      (loopRightTranslationEquiv_apply γ (Path.refl x)))
    (homotopyGroupMap_bijective_of_homotopyEquiv (loopRightTranslationEquiv γ)
      (loopRightTranslationEquiv_apply γ (Path.refl x)) n)

/-- Right translation followed by its exact constant-prefix track identifies every displayed
loop component with the chosen component, in every finite homotopy degree. -/
def loopComponentHomotopyEquiv (γ : Path x x) (n : ℕ) :
    HomotopyGroup.Pi n (Path x x) (Path.refl x) ≃ HomotopyGroup.Pi n (Path x x) γ :=
  (loopRightTranslationHomotopyEquiv γ n).trans (pathTransport (loopLeftUnitPath γ) n)

/-- The component equivalence is natural for the unchanged original based loop maps. -/
theorem loopComponentHomotopyEquiv_naturality (f : C(X, Y)) (h : f x = y)
    (γ : Path x x) (n : ℕ) (a : HomotopyGroup.Pi n (Path x x) (Path.refl x)) :
    loopComponentHomotopyEquiv (basedLoopMap f h γ) n
      (HomotopyGroup.map (basedLoopMap f h) (basedLoopMap_refl f h) a) =
        HomotopyGroup.map (basedLoopMap f h) rfl (loopComponentHomotopyEquiv γ n a) := by
  let g := basedLoopMap f h
  have ht : g ((Path.refl x).trans γ) = (Path.refl y).trans (g γ) := by
    rw [basedLoopMap_trans, basedLoopMap_refl]
  have hn : HomotopyGroup.map g ht (loopRightTranslationHomotopyEquiv γ n a) =
      loopRightTranslationHomotopyEquiv (g γ) n
        (HomotopyGroup.map g (basedLoopMap_refl f h) a) := by
    induction a using Quotient.inductionOn with
    | h p =>
      change Quotient.mk' (GenLoop.postcomp g ht
        (GenLoop.postcomp (loopRightTranslationEquiv γ).toFun _ p)) =
        Quotient.mk' (GenLoop.postcomp (loopRightTranslationEquiv (g γ)).toFun _
          (GenLoop.postcomp g _ p))
      apply congrArg Quotient.mk'
      ext s t
      exact congrArg (fun q : C(Path x x, Path y y) ↦ q (p s) t)
        (loopRightTranslationEquiv_naturality f h γ)
  change pathTransport (loopLeftUnitPath (g γ)) n
    (loopRightTranslationHomotopyEquiv (g γ) n
      (HomotopyGroup.map g (basedLoopMap_refl f h) a)) = _
  rw [← hn]
  exact pathTransport_naturality_of_track g (loopLeftUnitPath γ) (loopLeftUnitPath (g γ))
    ht rfl (fun s ↦ by ext t; exact loopLeftUnitPath_naturality f h γ s t)
    n (loopRightTranslationHomotopyEquiv γ n a)

/-- In every finite degree, the actual map at any displayed loop is bijective exactly when
its map at the constant loop is bijective. The natural equivalences retain the original loop,
the strict translation square, and the displayed constant-prefix track. -/
theorem basedLoopMap_homotopy_bijective_iff_refl (f : C(X, Y)) (h : f x = y)
    (γ : Path x x) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (basedLoopMap f h) (x := γ) rfl) ↔
      Function.Bijective (HomotopyGroup.map (N := Fin n)
        (basedLoopMap f h) (basedLoopMap_refl f h)) := by
  have hm : loopComponentHomotopyEquiv (basedLoopMap f h γ) n ∘
      HomotopyGroup.map (basedLoopMap f h) (basedLoopMap_refl f h) =
      HomotopyGroup.map (basedLoopMap f h) rfl ∘ loopComponentHomotopyEquiv γ n :=
    funext (loopComponentHomotopyEquiv_naturality f h γ n)
  rw [← Function.Bijective.of_comp_iff _ (loopComponentHomotopyEquiv γ n).bijective,
    ← hm, Function.Bijective.of_comp_iff' (loopComponentHomotopyEquiv _ n).bijective]

/-- Component translation is compatible with transport along every actual path of loops.
The square is the continuous constant-prefix removal of the entire displayed loop path. -/
theorem loopComponentHomotopyEquiv_pathTransport {γ δ : Path x x}
    (β : Path γ δ) (n : ℕ) (a : HomotopyGroup.Pi n (Path x x) (Path.refl x)) :
    pathTransport β n (loopComponentHomotopyEquiv γ n a) =
      loopComponentHomotopyEquiv δ n a := by
  let η : Path ((Path.refl x).trans γ) ((Path.refl x).trans δ) :=
    { toFun t := (Path.refl x).trans (β t)
      continuous_toFun := Path.continuous_trans.comp (continuous_const.prodMk β.continuous)
      source' := congrArg (fun p ↦ (Path.refl x).trans p) β.source
      target' := congrArg (fun p ↦ (Path.refl x).trans p) β.target }
  have ht : pathTransport η n (loopRightTranslationHomotopyEquiv γ n a) =
      loopRightTranslationHomotopyEquiv δ n a := by
    induction a using Quotient.inductionOn with
    | h p =>
      apply pathTransport_eq_of_cube_homotopy η n
        (GenLoop.postcomp (loopRightTranslationEquiv γ).toFun _ p)
        (GenLoop.postcomp (loopRightTranslationEquiv δ).toFun _ p)
        { toFun z := (p z.2).trans (β z.1)
          continuous_toFun := Path.continuous_trans.comp
            ((p.val.continuous.comp continuous_snd).prodMk (β.continuous.comp continuous_fst))
          map_zero_left := fun s ↦ by
            change (p s).trans (β 0) = loopRightTranslationEquiv γ (p s)
            rw [β.source, loopRightTranslationEquiv_apply]
          map_one_left := fun s ↦ by
            change (p s).trans (β 1) = loopRightTranslationEquiv δ (p s)
            rw [β.target, loopRightTranslationEquiv_apply] }
      intro t s hs
      change (p s).trans (β t) = (Path.refl x).trans (β t)
      exact congrArg (fun q ↦ q.trans (β t)) (p.property s hs)
  let H : C(unitInterval × unitInterval, Path x x) :=
    ⟨fun z ↦ Path.delayReflLeft z.1 (β z.2),
      Path.continuous_delayReflLeft.comp (continuous_fst.prodMk (β.continuous.comp continuous_snd))⟩
  have hs := pathTransport_square η β (loopLeftUnitPath γ) (loopLeftUnitPath δ) H
    (fun t ↦ Path.delayReflLeft_zero (β t)) (fun t ↦ Path.delayReflLeft_one (β t))
    (fun t ↦ congrArg (Path.delayReflLeft t) β.source)
    (fun t ↦ congrArg (Path.delayReflLeft t) β.target)
    n (loopRightTranslationHomotopyEquiv γ n a)
  change pathTransport β n (pathTransport (loopLeftUnitPath γ) n
    (loopRightTranslationHomotopyEquiv γ n a)) = _
  exact hs.trans (congrArg (pathTransport (loopLeftUnitPath δ) n) ht)

end Topology
