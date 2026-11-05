/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.UnitInterval
public import Colib.Topology.HomotopyFiber.Sequence
public import Colib.Topology.HomotopyFiber.Map

/-!
# Homotopy invariance of the concrete homotopy fiber

A continuous homotopy between maps induces an explicit equivalence of their
path-space homotopy fibers. The two inverse homotopies are constructed by
shrinking a path followed by its reverse, then removing constant prefixes.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/Equivalence.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space models,
basepoint tracks, maps and universe parameters are retained. -/
@[expose] public section


noncomputable section
open scoped Topology unitInterval
open unitInterval

universe u v

namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {f g : C(X, Y)}

/-- Change the map defining a homotopy fiber by prepending the reversed
pointwise path of the given homotopy. -/
def homotopyMap (H : f.Homotopy g) (y : Y) :
    C(HomotopyFiber f y, HomotopyFiber g y) where
  toFun z := ⟨(z.1.1, ((H.evalAt z.1.1).symm.trans (toPath f y z)).toContinuousMap),
    Path.source _, Path.target _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      refine Path.trans_continuous_family
        (fun z : HomotopyFiber f y => (H.evalAt z.1.1).symm) ?_
        (fun z : HomotopyFiber f y => toPath f y z) ?_
      · change Continuous (fun z : HomotopyFiber f y × I => H (σ z.2, z.1.1.1))
        fun_prop
      · change Continuous (fun z : HomotopyFiber f y × I => z.1.1.2 z.2)
        fun_prop

@[simp]
theorem projection_homotopyMap (H : f.Homotopy g) (y : Y) :
    (projection g y).comp (homotopyMap H y) = projection f y := rfl

/-- The initial segment of a pointwise homotopy path. -/
def homotopyPrefix (H : f.Homotopy g) (x : X) (s : I) : Path (f x) (H (s, x)) where
  toFun t := H (s * t, x)
  continuous_toFun := H.continuous.comp (by fun_prop)
  source' := by simp
  target' := by simp

/-- Shrink the two prefixes added by changing the map and changing it back. -/
def cancelHomotopyPrefixes (H : f.Homotopy g) (y : Y) :
    C(I × HomotopyFiber f y, HomotopyFiber f y) where
  toFun z := ⟨(z.2.1.1,
    ((homotopyPrefix H z.2.1.1 (σ z.1)).trans
      ((homotopyPrefix H z.2.1.1 (σ z.1)).symm.trans
        (toPath f y z.2))).toContinuousMap), Path.source _, Path.target _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      refine Path.trans_continuous_family
        (fun z : I × HomotopyFiber f y => homotopyPrefix H z.2.1.1 (σ z.1)) ?_
        (fun z : I × HomotopyFiber f y =>
          (homotopyPrefix H z.2.1.1 (σ z.1)).symm.trans (toPath f y z.2)) ?_
      · change Continuous (fun z : (I × HomotopyFiber f y) × I =>
          H (σ z.1.1 * z.2, z.1.2.1.1))
        fun_prop
      · refine Path.trans_continuous_family
          (fun z : I × HomotopyFiber f y => (homotopyPrefix H z.2.1.1 (σ z.1)).symm) ?_
          (fun z : I × HomotopyFiber f y => toPath f y z.2) ?_
        · change Continuous (fun z : (I × HomotopyFiber f y) × I =>
            H (σ z.1.1 * σ z.2, z.1.2.1.1))
          fun_prop
        · change Continuous (fun z : (I × HomotopyFiber f y) × I => z.1.2.1.2 z.2)
          fun_prop

/-- Remove both constant prefixes simultaneously. -/
def unpadTwice (f : C(X, Y)) (y : Y) : C(I × HomotopyFiber f y, HomotopyFiber f y) where
  toFun z := ⟨(z.2.1.1,
    (Path.delayReflLeft z.1 (Path.delayReflLeft z.1 (toPath f y z.2))).toContinuousMap),
      Path.source _, Path.target _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (I × HomotopyFiber f y) × I =>
        z.1.2.1.2 (σ (qRight (σ (σ (qRight (σ z.2, z.1.1))), z.1.1))))
      fun_prop

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem cancelHomotopyPrefixes_zero (H : f.Homotopy g) (y : Y) (z : HomotopyFiber f y) :
    cancelHomotopyPrefixes H y (0, z) = homotopyMap H.symm y (homotopyMap H y z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    change ((homotopyPrefix H z.1.1 (σ 0)).trans
        ((homotopyPrefix H z.1.1 (σ 0)).symm.trans (toPath f y z))) t =
      ((H.symm.evalAt z.1.1).symm.trans
        ((H.evalAt z.1.1).symm.trans (toPath f y z))) t
    simp only [Path.trans_apply, Path.symm_apply]
    split_ifs <;> first
    | rfl
    | (change H (σ 0 * _, z.1.1) = H (_, z.1.1); simp)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem cancelHomotopyPrefixes_one (H : f.Homotopy g) (y : Y) (z : HomotopyFiber f y) :
    cancelHomotopyPrefixes H y (1, z) = unpadTwice f y (0, z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply ContinuousMap.ext
    intro t
    change ((homotopyPrefix H z.1.1 (σ 1)).trans
        ((homotopyPrefix H z.1.1 (σ 1)).symm.trans (toPath f y z))) t =
      (Path.delayReflLeft 0 (Path.delayReflLeft 0 (toPath f y z))) t
    rw [Path.delayReflLeft_zero, Path.delayReflLeft_zero]
    have hp (t : I) : homotopyPrefix H z.1.1 (σ 1) t = f z.1.1 := by
      change H (σ 1 * t, z.1.1) = f z.1.1
      simp
    simp only [Path.trans_apply, Path.symm_apply, Path.refl_apply, Function.comp_apply, hp]
    rfl

@[simp]
theorem unpadTwice_one (f : C(X, Y)) (y : Y) (z : HomotopyFiber f y) :
    unpadTwice f y (1, z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (Path.delayReflLeft 1 (Path.delayReflLeft 1 (toPath f y z))).toContinuousMap = _
    simp only [Path.delayReflLeft_one]
    rfl

/-- The double-padded identity used as the midpoint of the inverse homotopy. -/
def doublePadded (f : C(X, Y)) (y : Y) : C(HomotopyFiber f y, HomotopyFiber f y) where
  toFun z := unpadTwice f y (0, z)
  continuous_toFun := (unpadTwice f y).continuous.comp (by fun_prop)

/-- The actual left-inverse homotopy for change of defining map. -/
def homotopyMapLeftInverse (H : f.Homotopy g) (y : Y) :
    ((homotopyMap H.symm y).comp (homotopyMap H y)).Homotopy
      (ContinuousMap.id (HomotopyFiber f y)) :=
  (show ((homotopyMap H.symm y).comp (homotopyMap H y)).Homotopy (doublePadded f y) from
    { toContinuousMap := cancelHomotopyPrefixes H y
      map_zero_left := cancelHomotopyPrefixes_zero H y
      map_one_left := cancelHomotopyPrefixes_one H y }).trans
  { toContinuousMap := unpadTwice f y
    map_zero_left := fun _ => rfl
    map_one_left := unpadTwice_one f y }

/-- Homotopic maps have homotopy-equivalent topological homotopy fibers,
with the maps and both inverse homotopies explicitly constructed. -/
def homotopyEquiv (H : f.Homotopy g) (y : Y) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber f y) (HomotopyFiber g y) where
  toFun := homotopyMap H y
  invFun := homotopyMap H.symm y
  left_inv := ⟨homotopyMapLeftInverse H y⟩
  right_inv := by
    simpa only [ContinuousMap.Homotopy.symm_symm] using
      (show ((homotopyMap H.symm.symm y).comp (homotopyMap H.symm y)).Homotopic
        (ContinuousMap.id (HomotopyFiber g y)) from ⟨homotopyMapLeftInverse H.symm y⟩)

/-- Propositional homotopy invariance follows from the explicit construction. -/
theorem nonempty_homotopyEquiv (H : f.Homotopic g) (y : Y) :
    Nonempty (ContinuousMap.HomotopyEquiv (HomotopyFiber f y) (HomotopyFiber g y)) :=
  H.map fun H => homotopyEquiv H y

/-- Slide the starting point of a path to its endpoint while shortening the path.
This contracts the homotopy fiber of the identity map. -/
def idContraction (y : Y) :
    (ContinuousMap.id (HomotopyFiber (ContinuousMap.id Y) y)).Homotopy
      (ContinuousMap.const _ (basepoint (ContinuousMap.id Y) y y rfl)) where
  toFun z := ⟨(z.2.1.2 z.1,
    ⟨fun t => z.2.1.2 (σ (σ z.1 * σ t)), by fun_prop⟩),
    by simp, by simpa using z.2.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (I × HomotopyFiber (ContinuousMap.id Y) y) × I =>
        z.1.2.1.2 (σ (σ z.1.1 * σ z.2)))
      fun_prop
  map_zero_left z := by
    apply Subtype.ext
    apply Prod.ext
    · exact z.2.1
    · apply ContinuousMap.ext
      intro t
      change z.1.2 (σ (σ 0 * σ t)) = z.1.2 t
      simp
  map_one_left z := by
    apply Subtype.ext
    apply Prod.ext
    · exact z.2.2
    · apply ContinuousMap.ext
      intro t
      change z.1.2 (σ (σ 1 * σ t)) = y
      simpa using z.2.2

@[simp]
theorem idContraction_basepoint (y : Y) (t : I) :
    idContraction y (t, basepoint (ContinuousMap.id Y) y y rfl) =
      basepoint (ContinuousMap.id Y) y y rfl := rfl

/-- The actual path-space fiber of an identity map is contractible. -/
instance contractibleSpace_id (y : Y) :
    ContractibleSpace (HomotopyFiber (ContinuousMap.id Y) y) :=
  (contractible_iff_id_nullhomotopic _).mpr
    ⟨basepoint (ContinuousMap.id Y) y y rfl, ⟨idContraction y⟩⟩

/-- Any self-map continuously homotopic to the identity has contractible fibers. -/
theorem contractibleSpace_of_homotopic_id {f : C(Y, Y)}
    (H : f.Homotopic (ContinuousMap.id Y)) (y : Y) : ContractibleSpace (HomotopyFiber f y) := by
  obtain ⟨H⟩ := H
  exact (homotopyEquiv H y).contractibleSpace

/-- The homotopy fiber of a constant map is exactly a product with a path space. -/
def constantHomeomorph (X : Type u) [TopologicalSpace X] (a y : Y) :
    HomotopyFiber (ContinuousMap.const X a) y ≃ₜ X × Path a y where
  toFun z := (z.1.1, toPath (ContinuousMap.const X a) y z)
  invFun z := ⟨(z.1, z.2.toContinuousMap), z.2.source, z.2.target⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · fun_prop
    · apply Path.continuous_uncurry_iff.mp
      change Continuous (fun z : HomotopyFiber (ContinuousMap.const X a) y × I => z.1.1.2 z.2)
      fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_fst
    exact continuous_induced_dom.comp continuous_snd

/-- A chosen nullhomotopy explicitly identifies the homotopy fiber with the
source times the corresponding path space. -/
def nullhomotopyEquiv (f : C(X, Y)) (a y : Y)
    (H : f.Homotopy (ContinuousMap.const X a)) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber f y) (X × Path a y) :=
  (homotopyEquiv H y).trans (constantHomeomorph X a y).toHomotopyEquiv

end Topology.HomotopyFiber
