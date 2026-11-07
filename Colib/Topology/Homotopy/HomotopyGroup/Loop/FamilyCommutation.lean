/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.KOneNormalization
public import Colib.Topology.Homotopy.HomotopyGroup.Loop.Reversal

/-!
# Normalization and axis cancellation from an actual loop-family commutation

A supplied whole-family commutation homotopy need not fix its source vertex.
Its actual inverse-family homotopy is constructed with path associators and
inverse-pair cancellations. The original two normalization caps then give the
same second homotopy class. A separate paired-path argument caps the original
pointwise product of an outer loop and its outer reverse, retaining the double
object-loop factor.

The intended categorical input is the actual biproduct braiding homotopy of the
zero-first Q-cone family. No nullity of the object loop, simplicity of the ambient
space, or triviality of its fundamental-group action is assumed or asserted.
The constructions use Mathlib's path operations and the original native loop
normalization; the fundamental-group multiplication order is unchanged.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u v
namespace Topology
variable {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z] {x : X}

private def concatenateFamilyHomotopies
    {f₀ f₁ g₀ g₁ : C(Z, Path x x)} (H : f₀.Homotopy f₁) (K : g₀.Homotopy g₁) :
    (⟨fun z => (f₀ z).trans (g₀ z), by fun_prop⟩ : C(Z, Path x x)).Homotopy
      ⟨fun z => (f₁ z).trans (g₁ z), by fun_prop⟩ where
  toFun z := (H z).trans (K z)
  continuous_toFun := Path.continuous_trans.comp (H.continuous.prodMk K.continuous)
  map_zero_left z := by rw [H.apply_zero, K.apply_zero]; rfl
  map_one_left z := by rw [H.apply_one, K.apply_one]; rfl

private def loopFamilyAssociator (a b c : C(Z, Path x x)) :
    (⟨fun z => ((a z).trans (b z)).trans (c z), by fun_prop⟩ : C(Z, Path x x)).Homotopy
      ⟨fun z => (a z).trans ((b z).trans (c z)), by fun_prop⟩ where
  toFun z := (Path.Homotopy.transAssoc (a z.2) (b z.2) (c z.2)).eval z.1
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (unitInterval × Z) × unitInterval =>
      ((a z.1.2).trans ((b z.1.2).trans (c z.1.2)))
        ⟨↑(unitInterval.symm (unitInterval.symm z.1.1)) * ↑z.2 +
          ↑(unitInterval.symm z.1.1) * Path.Homotopy.transAssocReparamAux z.2, _⟩)
    fun_prop
  map_zero_left z := by
    ext t
    exact (Path.Homotopy.transAssoc (a z) (b z) (c z)).apply_zero t
  map_one_left z := by
    ext t
    exact (Path.Homotopy.transAssoc (a z) (b z) (c z)).apply_one t

private def loopFamilyRightUnit (f : C(Z, Path x x)) :
    (⟨fun z => (f z).trans (Path.refl x), by fun_prop⟩ : C(Z, Path x x)).Homotopy f where
  toFun z := Path.delayReflRight z.1 (f z.2)
  continuous_toFun := Path.continuous_delayReflRight.comp
    (continuous_fst.prodMk (f.continuous.comp continuous_snd))
  map_zero_left z := Path.delayReflRight_zero (f z)
  map_one_left z := Path.delayReflRight_one (f z)

private def loopFamilyLeftUnit (f : C(Z, Path x x)) :
    (⟨fun z => (Path.refl x).trans (f z), by fun_prop⟩ : C(Z, Path x x)).Homotopy f where
  toFun z := Path.delayReflLeft z.1 (f z.2)
  continuous_toFun := Path.continuous_delayReflLeft.comp
    (continuous_fst.prodMk (f.continuous.comp continuous_snd))
  map_zero_left z := Path.delayReflLeft_zero (f z)
  map_one_left z := Path.delayReflLeft_one (f z)

private def constantLoopFamilyHomotopy {p q : Path x x} (κ : Path p q) :
    (ContinuousMap.const Z p).Homotopy (ContinuousMap.const Z q) where
  toFun z := κ z.1
  continuous_toFun := κ.continuous.comp continuous_fst
  map_zero_left _ := κ.source
  map_one_left _ := κ.target

/-- Reverse the varying inner loop using the given homotopy and only inverse-pair cancellation. -/
private def inverseLoopFamilyCommutation (f : C(Z, Path x x)) (p : Path x x)
    (H : (⟨fun z => p.trans (f z), by fun_prop⟩ : C(Z, Path x x)).Homotopy
      ⟨fun z => (f z).trans p, by fun_prop⟩) :
    (⟨fun z => (f z).symm.trans p,
      Path.continuous_trans.comp
        ((Path.continuous_symm.comp f.continuous).prodMk continuous_const)⟩ :
              C(Z, Path x x)).Homotopy
      ⟨fun z => p.trans (f z).symm,
        Path.continuous_trans.comp
          (continuous_const.prodMk (Path.continuous_symm.comp f.continuous))⟩ := by
  let M (a b : C(Z, Path x x)) : C(Z, Path x x) :=
    ⟨fun z => (a z).trans (b z), by fun_prop⟩
  let C : C(Z, Path x x) := ContinuousMap.const Z p
  let Cinv : C(Z, Path x x) := ContinuousMap.const Z p.symm
  let O : C(Z, Path x x) := ContinuousMap.const Z (Path.refl x)
  let v := loopReversal.comp f
  let Hrev : (M v Cinv).Homotopy (M Cinv v) :=
    ((ContinuousMap.Homotopy.refl loopReversal).comp H).cast
      (by ext z : 1; exact Path.trans_symm p (f z))
      (by ext z : 1; exact Path.trans_symm (f z) p)
  let S : (M (M C (M v Cinv)) C).Homotopy (M (M C (M Cinv v)) C) :=
    concatenateFamilyHomotopies
      (concatenateFamilyHomotopies (ContinuousMap.Homotopy.refl C) Hrev)
      (ContinuousMap.Homotopy.refl C)
  let Kinv : (M Cinv C).Homotopy O :=
    constantLoopFamilyHomotopy (loopInversePrefixCancellation p)
  let Kpos : (M C Cinv).Homotopy O :=
    constantLoopFamilyHomotopy
      ((loopInversePrefixCancellation p.symm).cast
        (congrArg (fun q => q.trans p.symm) (Path.symm_symm p).symm) rfl)
  let L : (M (M C (M v Cinv)) C).Homotopy (M C v) :=
    (concatenateFamilyHomotopies (loopFamilyAssociator C v Cinv).symm
      (ContinuousMap.Homotopy.refl C)).trans
      ((loopFamilyAssociator (M C v) Cinv C).trans
        ((concatenateFamilyHomotopies (ContinuousMap.Homotopy.refl (M C v)) Kinv).trans
          (loopFamilyRightUnit (M C v))))
  let R : (M (M C (M Cinv v)) C).Homotopy (M v C) :=
    (concatenateFamilyHomotopies (loopFamilyAssociator C Cinv v).symm
      (ContinuousMap.Homotopy.refl C)).trans
      ((concatenateFamilyHomotopies
        (concatenateFamilyHomotopies Kpos (ContinuousMap.Homotopy.refl v))
        (ContinuousMap.Homotopy.refl C)).trans
          (concatenateFamilyHomotopies (loopFamilyLeftUnit v)
            (ContinuousMap.Homotopy.refl C)))
  exact R.symm.trans (S.symm.trans L)

private theorem loopComponentPiOne_comm (p : Path x x)
    (a b : HomotopyGroup.Pi 1 (Path x x) p) : a * b = b * a := by
  let e := HomotopyGroup.pi1MulEquivFundamentalGroup.trans (loopKOneNormalization p)
  apply e.injective
  simp only [map_mul]
  exact mul_comm _ _

/-- Actual family commutation equates the two original normalization orders with their given caps.
The homotopy is not required to be stationary at the source vertex. -/
theorem loopFamily_normalizationOrder (f : C(Z, Path x x)) (z : Z)
    (H : (⟨fun w => (f z).trans (f w), by fun_prop⟩ : C(Z, Path x x)).Homotopy
      ⟨fun w => (f w).trans (f z), by fun_prop⟩)
    (γ : Path ((f z).symm.trans (f z)) (Path.refl x))
    (δ : Path ((f z).trans (f z).symm) (Path.refl x))
    (a : HomotopyGroup.Pi 1 Z z) :
    (loopShiftMulEquiv 0).symm
        (pathTransport γ 1
          (HomotopyGroup.map
            (⟨fun w => (f w).symm.trans (f z),
              Path.continuous_trans.comp
                ((Path.continuous_symm.comp f.continuous).prodMk continuous_const)⟩ :
              C(Z, Path x x)) rfl a)) =
      (loopShiftMulEquiv 0).symm
        (pathTransport δ 1
          (HomotopyGroup.map
            (⟨fun w => (f z).trans (f w).symm,
              Path.continuous_trans.comp
                (continuous_const.prodMk (Path.continuous_symm.comp f.continuous))⟩ :
              C(Z, Path x x)) rfl a)) := by
  have h := DFunLike.congr_fun
    (piOne_homotopy_corrected (inverseLoopFamilyCommutation f (f z) H) γ δ
      (loopComponentPiOne_comm (Path.refl x))) a
  exact congrArg (loopShiftMulEquiv 0).symm h

private def pairedPathUnitHomotopy {Y : Type*} [TopologicalSpace Y] {p : Y}
    (α β : Path p p) :
    ((α.prod (Path.refl p)).trans ((Path.refl p).prod β)).Homotopy (α.prod β) := by
  let A := Path.Homotopy.transRefl α
  let B := Path.Homotopy.reflTrans β
  let K : ((α.trans (Path.refl p)).prod ((Path.refl p).trans β)).Homotopy (α.prod β) := {
    toHomotopy := A.toHomotopy.prodMk B.toHomotopy
    prop' s t ht := Prod.ext (A.eq_fst s ht) (B.eq_fst s ht) }
  exact K.cast (Path.trans_prod_eq_prod_trans α (Path.refl p) (Path.refl p) β).symm rfl

/-- The original pointwise inverse-axis loop has a based cap at the double object loop.
Its two axes are identified by the actual family homotopy, including its vertex track. -/
def loopFamilyInverseAxisCap (f : C(Z, Path x x)) (z : Z)
    (H : (⟨fun w => (f z).trans (f w), by fun_prop⟩ : C(Z, Path x x)).Homotopy
      ⟨fun w => (f w).trans (f z), by fun_prop⟩)
    (δ : Path z z) :
    (((δ.map f.continuous).prod (δ.map f.continuous).symm).map
      Path.continuous_trans).Homotopy (Path.refl ((f z).trans (f z))) := by
  let p := f z
  let α := δ.map f.continuous
  let L : C(Path x x, Path x x) := ⟨fun q => p.trans q, by fun_prop⟩
  let R : C(Path x x, Path x x) := ⟨fun q => q.trans p, by fun_prop⟩
  let M : C(Path x x × Path x x, Path x x) :=
    ⟨fun q => q.1.trans q.2, Path.continuous_trans⟩
  have haxes : FundamentalGroup.map L p (⟦α⟧ : FundamentalGroup (Path x x) p) =
      FundamentalGroup.map R p (⟦α⟧ : FundamentalGroup (Path x x) p) := by
    have h := fundamentalGroup_homotopy_corrected H
      (Path.refl (p.trans p)) (Path.refl (p.trans p))
      (by
        intro a b
        apply (loopKOneNormalization (p.trans p)).injective
        simp only [map_mul]
        exact mul_comm _ _) (⟦δ⟧ : FundamentalGroup Z z)
    exact (FundamentalGroup.fundamentalGroupMulEquivOfPath
      (Path.refl (p.trans p))).injective h
  have h : (⟦(α.prod α.symm).map M.continuous⟧ :
      FundamentalGroup (Path x x) (p.trans p)) =
      (1 : FundamentalGroup (Path x x) (p.trans p)) := by
    calc
      _ = (⟦((α.prod (Path.refl p)).trans
          ((Path.refl p).prod α.symm)).map M.continuous⟧ :
            FundamentalGroup (Path x x) (p.trans p)) := by
        apply Quotient.sound
        exact ⟨(pairedPathUnitHomotopy α α.symm).symm.map M⟩
      _ = FundamentalGroup.map L p (⟦α.symm⟧ : FundamentalGroup (Path x x) p) *
          FundamentalGroup.map R p (⟦α⟧ : FundamentalGroup (Path x x) p) := by
        rw [Path.map_trans]
        rfl
      _ = (FundamentalGroup.map L p (⟦α⟧ : FundamentalGroup (Path x x) p))⁻¹ *
          FundamentalGroup.map R p (⟦α⟧ : FundamentalGroup (Path x x) p) := by
        change FundamentalGroup.map L p ((⟦α⟧ : FundamentalGroup (Path x x) p)⁻¹) * _ = _
        rw [map_inv]
      _ = 1 := by rw [haxes, inv_mul_cancel]
  exact (Quotient.exact h).some

end Topology
