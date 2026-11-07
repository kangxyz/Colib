/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.InverseComponentTranslation
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportFundamentalGroup
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.DegreeShift

/-! An independent automorphism-class construction in the original K-one group.
All component translations use the actual inverse prefix and specified cancellation. -/

/-! Implementation source: `Quillen/Topology/HomotopyGroups/Loop/KOneNormalization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, basepoints,
coordinate order and signs are retained under native Colib ownership. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v

namespace Topology
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- Moving the prefix through an actual path of loops transports the original left component. -/
theorem loopLeftComponentHomotopyEquiv_pathTransport {γ δ : Path x x}
    (β : Path γ δ) (n : ℕ) (a : HomotopyGroup.Pi n (Path x x) (Path.refl x)) :
    pathTransport β n (loopLeftComponentHomotopyEquiv γ n a) =
      loopLeftComponentHomotopyEquiv δ n a := by
  let η : Path (γ.trans (Path.refl x)) (δ.trans (Path.refl x)) :=
    { toFun t := (β t).trans (Path.refl x)
      continuous_toFun := Path.continuous_trans.comp (β.continuous.prodMk continuous_const)
      source' := congrArg (fun p ↦ p.trans (Path.refl x)) β.source
      target' := congrArg (fun p ↦ p.trans (Path.refl x)) β.target }
  have ht : pathTransport η n (loopLeftTranslationHomotopyEquiv γ n a) =
      loopLeftTranslationHomotopyEquiv δ n a := by
    induction a using Quotient.inductionOn with
    | h p =>
      apply pathTransport_eq_of_cube_homotopy η n
        (GenLoop.postcomp (loopLeftTranslationEquiv γ).toFun _ p)
        (GenLoop.postcomp (loopLeftTranslationEquiv δ).toFun _ p)
        { toFun z := (β z.1).trans (p z.2)
          continuous_toFun := Path.continuous_trans.comp
            ((β.continuous.comp continuous_fst).prodMk (p.val.continuous.comp continuous_snd))
          map_zero_left := fun s ↦ by
            change (β 0).trans (p s) = loopLeftTranslationEquiv γ (p s)
            rw [β.source, loopLeftTranslationEquiv_apply]
          map_one_left := fun s ↦ by
            change (β 1).trans (p s) = loopLeftTranslationEquiv δ (p s)
            rw [β.target, loopLeftTranslationEquiv_apply] }
      intro t s hs
      change (β t).trans (p s) = (β t).trans (Path.refl x)
      exact congrArg (fun q ↦ (β t).trans q) (p.property s hs)
  let H : C(unitInterval × unitInterval, Path x x) :=
    ⟨fun z ↦ (Path.delayReflLeft z.1 (β z.2).symm).symm,
      Path.continuous_symm.comp (Path.continuous_delayReflLeft.comp
        (continuous_fst.prodMk
          (Path.continuous_symm.comp (β.continuous.comp continuous_snd))))⟩
  have hs := pathTransport_square η β (loopRightUnitPath γ) (loopRightUnitPath δ) H
    (fun t ↦ by simp [H, η, Path.delayReflLeft_zero, Path.trans_symm])
    (fun t ↦ by simp [H, Path.delayReflLeft_one])
    (fun t ↦ by change (Path.delayReflLeft t (β 0).symm).symm = _; rw [β.source]; rfl)
    (fun t ↦ by change (Path.delayReflLeft t (β 1).symm).symm = _; rw [β.target]; rfl)
    n (loopLeftTranslationHomotopyEquiv γ n a)
  change pathTransport β n (pathTransport (loopRightUnitPath γ) n
    (loopLeftTranslationHomotopyEquiv γ n a)) = _
  exact hs.trans (congrArg (pathTransport (loopRightUnitPath δ) n) ht)

/-- Normalize an outer loop at any actual inner-loop component into the original second group. -/
def loopKOneNormalization (γ : Path x x) :
    FundamentalGroup (Path x x) γ ≃* HomotopyGroup.Pi 2 X x :=
  HomotopyGroup.pi1MulEquivFundamentalGroup.symm.trans
    ((MulEquiv.ofBijective
      (HomotopyGroup.piMap 0 (loopLeftTranslationEquiv γ.symm).toFun
        (loopLeftTranslationEquiv_apply _ _))
      (homotopyGroupMap_bijective_of_homotopyEquiv (loopLeftTranslationEquiv γ.symm)
        (loopLeftTranslationEquiv_apply _ _) 1)).trans
      ((pathTransportMulEquiv (loopInversePrefixCancellation γ) 0).trans
        (loopShiftMulEquiv 0).symm))

/-- The explicit inverse-prefix normalization is the inverse of the original left component. -/
theorem loopKOneNormalization_eq (γ : Path x x)
    (a : FundamentalGroup (Path x x) γ) :
    loopKOneNormalization γ a =
      (loopShiftMulEquiv 0).symm ((loopLeftComponentHomotopyEquiv γ 1).symm
        (HomotopyGroup.pi1MulEquivFundamentalGroup.symm a)) := by
  change (loopShiftMulEquiv 0).symm (loopInversePrefixHomotopyEquiv γ 1
    (HomotopyGroup.pi1MulEquivFundamentalGroup.symm a)) = _
  rw [loopInversePrefixHomotopyEquiv_eq]

/-- Normalization retains transport along the actual path between object-loop components. -/
theorem loopKOneNormalization_transport {γ δ : Path x x} (β : Path γ δ)
    (a : FundamentalGroup (Path x x) γ) :
    loopKOneNormalization δ (FundamentalGroup.fundamentalGroupMulEquivOfPath β a) =
      loopKOneNormalization γ a := by
  rw [loopKOneNormalization_eq, loopKOneNormalization_eq]
  congr 1
  apply (loopLeftComponentHomotopyEquiv δ 1).injective
  rw [Equiv.apply_symm_apply]
  have h := loopLeftComponentHomotopyEquiv_pathTransport β 1
    ((loopLeftComponentHomotopyEquiv γ 1).symm
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm a))
  rw [Equiv.apply_symm_apply] at h
  rw [← h]
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [MulEquiv.apply_symm_apply, piOneEquivFundamentalGroup_pathTransport,
    MulEquiv.apply_symm_apply]

/-- The inverse of left-component translation retains the original based loop map. -/
theorem loopLeftComponent_inverse_naturality (f : C(X, Y)) (h : f x = y)
    (γ : Path x x) (a : HomotopyGroup.Pi 1 (Path x x) γ) :
    (loopLeftComponentHomotopyEquiv (basedLoopMap f h γ) 1).symm
        (HomotopyGroup.map (basedLoopMap f h) rfl a) =
      HomotopyGroup.map (basedLoopMap f h) (basedLoopMap_refl f h)
        ((loopLeftComponentHomotopyEquiv γ 1).symm a) := by
  apply (loopLeftComponentHomotopyEquiv (basedLoopMap f h γ) 1).injective
  rw [Equiv.apply_symm_apply, loopLeftComponentHomotopyEquiv_naturality,
    Equiv.apply_symm_apply]

/-- The independently normalized loop class is natural for the original based map. -/
theorem loopKOneNormalization_naturality (f : C(X, Y)) (h : f x = y)
    (γ : Path x x) (a : FundamentalGroup (Path x x) γ) :
    HomotopyGroup.piMap 1 f h (loopKOneNormalization γ a) =
      loopKOneNormalization (basedLoopMap f h γ)
        (FundamentalGroup.mapOfEq (basedLoopMap f h) rfl a) := by
  rw [loopKOneNormalization_eq, loopKOneNormalization_eq]
  apply (loopShiftMulEquiv 0).injective
  rw [MulEquiv.apply_symm_apply]
  have hs := DFunLike.congr_fun (loopShiftMulEquiv_natural 0 f h)
    ((loopShiftMulEquiv 0).symm ((loopLeftComponentHomotopyEquiv γ 1).symm
      (HomotopyGroup.pi1MulEquivFundamentalGroup.symm a)))
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply] at hs
  rw [← hs]
  change HomotopyGroup.map (basedLoopMap f h) (basedLoopMap_refl f h)
      ((loopLeftComponentHomotopyEquiv γ 1).symm
        (HomotopyGroup.pi1MulEquivFundamentalGroup.symm a)) = _
  rw [← loopLeftComponent_inverse_naturality]
  congr 1
  apply HomotopyGroup.pi1MulEquivFundamentalGroup.injective
  rw [MulEquiv.apply_symm_apply]
  rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality, MulEquiv.apply_symm_apply]

/-- A specified equality of the actual image loop retains both endpoint casts of the outer path. -/
theorem loopKOneNormalization_naturality_of_loopEq
    (f : C(X, Y)) (h : f x = y) (γ : Path x x) (δ : Path y y)
    (hγ : basedLoopMap f h γ = δ) (α : Path γ γ) :
    HomotopyGroup.piMap 1 f h (loopKOneNormalization γ (FundamentalGroup.fromPath ⟦α⟧)) =
      loopKOneNormalization δ
        (FundamentalGroup.fromPath ⟦(α.map (basedLoopMap f h).continuous).cast hγ.symm hγ.symm⟧)
          := by
  subst δ
  rw [loopKOneNormalization_naturality, FundamentalGroup.mapOfEq_apply]
  rfl

end Topology
