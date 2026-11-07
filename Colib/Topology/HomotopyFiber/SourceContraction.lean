/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyFiber.LoopPrefixBasepointNaturality
public import Colib.Topology.HomotopyFiber.ContractibleSourcePath

/-!
Implementation provenance: `Quillen/Topology/HomotopyFiber/SourceContraction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, tracks,
hypotheses, and signs are retained under native mathematical ownership.

# The original loop-fiber inverse along a displayed source contraction

A genuine contraction of the source coordinate of a homotopy-fiber map gives
an explicit path-difference formula. The proof slides the actual source,
retains every stored fiber path, and cancels the original forward equivalence.
No replacement inverse or prescribed-track equality is assumed.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w
open Topology
open scoped Topology unitInterval
open unitInterval
namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f : C(X, Y)) (y : Y) (h : C(Z, HomotopyFiber f y)) (e : X)
  (H : ((projection f y).comp h).Homotopy (ContinuousMap.const Z e))

/-- The stored fiber path preceded by the reversed projected source-contraction track. -/
def contractedPathMap : C(Z, Path (f e) y) where
  toFun z := ((H.evalAt z).symm.map f.continuous).trans (toPath f y (h z))
  continuous_toFun := by
    refine (Path.continuous_uncurry_iff (X := Y) (x := f e) (y := y) (g := fun z : Z =>
      (((H.evalAt z).symm.map f.continuous).trans (toPath f y (h z)) : Path (f e) y))).mp ?_
    change Continuous (fun a : Z × unitInterval =>
      (((H.evalAt a.1).symm.map f.continuous).trans (toPath f y (h a.1))) a.2)
    refine Path.trans_continuous_family
      (fun z : Z => (H.evalAt z).symm.map f.continuous) ?_
      (fun z : Z => toPath f y (h z)) ?_
    · change Continuous (fun a : Z × unitInterval => f (H (σ a.2, a.1)))
      fun_prop
    · change Continuous (fun a : Z × unitInterval => (h a.1).val.2 a.2)
      fun_prop

/-- A path with the displayed initial point gives its literal homotopy-fiber point. -/
def constantSourcePathMap : C(Path (f e) y, HomotopyFiber f y) where
  toFun γ := pointWithPath f e y γ
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk continuous_induced_dom

/-- Move along the supplied source contraction and prepend its traversed image in reverse. -/
def contractionSlide : C(unitInterval × Z, HomotopyFiber f y) where
  toFun a := ⟨(H a,
    (((homotopyPrefix H a.2 a.1).symm.map f.continuous).trans
      (toPath f y (h a.2))).toContinuousMap), Path.source _, Path.target _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk H.continuous
    apply ContinuousMap.continuous_of_continuous_uncurry
    refine Path.trans_continuous_family
      (fun a : unitInterval × Z => (homotopyPrefix H a.2 a.1).symm.map f.continuous) ?_
      (fun a : unitInterval × Z => toPath f y (h a.2)) ?_
    · change Continuous (fun a : (unitInterval × Z) × unitInterval =>
        f (H (a.1.1 * σ a.2, a.1.2)))
      fun_prop
    · change Continuous (fun a : (unitInterval × Z) × unitInterval =>
        (h a.1.2).val.2 a.2)
      fun_prop

/-- Remove the constant prefix at the initial end of the source slide. -/
def contractionUnpad : C(unitInterval × Z, HomotopyFiber f y) where
  toFun a := ⟨((h a.2).val.1,
    (Path.delayReflLeft a.1 (toPath f y (h a.2))).toContinuousMap),
      Path.source _, Path.target _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · exact continuous_fst.comp (continuous_subtype_val.comp (h.continuous.comp continuous_snd))
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun a : (unitInterval × Z) × unitInterval =>
        (h a.1.2).val.2 (σ (qRight (σ a.2, a.1.1))))
      fun_prop

/-- The source slide begins at the original fiber map with its constant prefix. -/
theorem contractionSlide_zero (z : Z) :
    contractionSlide f y h e H (0, z) = contractionUnpad f y h (0, z) := by
  apply Subtype.ext
  apply Prod.ext
  · exact H.apply_zero z
  · apply ContinuousMap.ext
    intro t
    change (((homotopyPrefix H z 0).symm.map f.continuous).trans
      (toPath f y (h z))) t = (Path.delayReflLeft 0 (toPath f y (h z))) t
    rw [Path.delayReflLeft_zero]
    simp only [Path.trans_apply]
    split_ifs
    · change f (H (0 * σ _, z)) = f (h z).val.1
      simp only [zero_mul, ContinuousMap.Homotopy.apply_zero]
      rfl
    · rfl

/-- The source slide ends at the displayed constant-source path family. -/
theorem contractionSlide_one (z : Z) :
    contractionSlide f y h e H (1, z) =
      constantSourcePathMap f y e (contractedPathMap f y h e H z) := by
  apply Subtype.ext
  apply Prod.ext
  · exact H.apply_one z
  · apply ContinuousMap.ext
    intro t
    change (((homotopyPrefix H z 1).symm.map f.continuous).trans
      (toPath f y (h z))) t =
        (((H.evalAt z).symm.map f.continuous).trans (toPath f y (h z))) t
    simp only [Path.trans_apply]
    split_ifs
    · change f (H (1 * σ _, z)) = f (H (σ _, z))
      simp
    · rfl

/-- The complete prefix removal gives the original fiber point. -/
theorem contractionUnpad_one (z : Z) : contractionUnpad f y h (1, z) = h z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (Path.delayReflLeft 1 (toPath f y (h z))).toContinuousMap = _
    rw [Path.delayReflLeft_one]
    rfl

/-- The actual source slide gives a homotopy of the original fiber map. -/
def contractionFiberHomotopy : h.Homotopy
    ((constantSourcePathMap f y e).comp (contractedPathMap f y h e H)) :=
  let padded : C(Z, HomotopyFiber f y) :=
    ⟨fun z => contractionUnpad f y h (0, z),
      (contractionUnpad f y h).continuous.comp (continuous_const.prodMk continuous_id)⟩
  (show padded.Homotopy h from {
    toContinuousMap := contractionUnpad f y h
    map_zero_left := fun _ => rfl
    map_one_left := contractionUnpad_one f y h }).symm.trans {
      toContinuousMap := contractionSlide f y h e H
      map_zero_left := contractionSlide_zero f y h e H
      map_one_left := contractionSlide_one f y h e H }

variable {f y h e H}

/-- A fixed path followed by its inverse cancels continuously over all final paths. -/
def prefixCancellation {a b c : Y} (p : Path a b) :
    ((pathPrefix (c := c) p).comp (pathPrefix p.symm)).Homotopy
      (ContinuousMap.id (Path a c)) := by
  let J : (pathPrefix (c := c) (p.trans p.symm)).Homotopy
      (pathPrefix (Path.refl a)) := {
    toFun z := ((Path.Homotopy.reflTransSymm p).symm.eval z.1).trans z.2
    continuous_toFun := by
      apply Continuous.path_trans
      · apply Path.continuous_uncurry_iff.mp
        change Continuous (fun z : (unitInterval × Path a c) × unitInterval =>
          (Path.Homotopy.reflTransSymm p).symm (z.1.1, z.2))
        exact (Path.Homotopy.reflTransSymm p).symm.continuous.comp
          (continuous_fst.fst.prodMk continuous_snd)
      · exact continuous_snd
    map_zero_left q := by rw [Path.Homotopy.eval_zero]; rfl
    map_one_left q := by rw [Path.Homotopy.eval_one]; rfl }
  let K : (pathPrefix (c := c) (Path.refl a)).Homotopy
      (ContinuousMap.id (Path a c)) := {
    toFun z := Path.delayReflLeft z.1 z.2
    continuous_toFun := Path.continuous_delayReflLeft
    map_zero_left q := Path.delayReflLeft_zero q
    map_one_left q := Path.delayReflLeft_one q }
  exact (pathPrefixAssociator p p.symm).symm.trans (J.trans K)

variable (f y h e H)

/-- Compare the contracted path at the displayed basepoint with every original path. -/
def contractedDifference (z₀ : Z) : C(Z, Path y y) :=
  (pathPrefix (contractedPathMap f y h e H z₀).symm).comp
    (contractedPathMap f y h e H)

/-- The unchanged loop/fiber inverse is homotopic to the actual contracted-path difference. -/
def inverseContractionHomotopy [ContractibleSpace X] (z₀ : Z) :
    (((loopEquivOfContractibleSourcePath f (h z₀).val.1 y
      (toPath f y (h z₀))).invFun).comp h).Homotopy
        (contractedDifference f y h e H z₀) := by
  let a := contractedPathMap f y h e H
  let d := contractedDifference f y h e H z₀
  let E := loopEquivOfContractibleSourcePath f (h z₀).val.1 y (toPath f y (h z₀))
  let K := contractionFiberHomotopy f y h e H
  let q := K.evalAt z₀
  have P : ((loopPrefix f e y (a z₀)).comp d).Homotopy
      ((constantSourcePathMap f y e).comp a) :=
    (ContinuousMap.Homotopy.refl (constantSourcePathMap f y e)).comp
      ((prefixCancellation (c := y) (a z₀)).compContinuousMap a)
  have Q : (E.toFun.comp d).Homotopy ((loopPrefix f e y (a z₀)).comp d) := by
    have hq := (loopPrefixPathHomotopy q).compContinuousMap d
    exact hq.cast
      (congrArg (fun k => k.comp d) (loopPrefix_eq_forward f (h z₀).val.1 y
        (toPath f y (h z₀)))) rfl
  have F : (E.toFun.comp d).Homotopy h := Q.trans (P.trans K.symm)
  have L : (E.invFun.comp (E.toFun.comp d)).Homotopy d :=
    (Classical.choice E.left_inv).compContinuousMap d
  exact L.symm.trans ((ContinuousMap.Homotopy.refl E.invFun).comp F) |>.symm

end Topology.HomotopyFiber
