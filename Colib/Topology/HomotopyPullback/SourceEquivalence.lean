/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Basic
public import Colib.Topology.HomotopyFiber.SourceEquivalence
public import Colib.Topology.Homotopy.Equiv.Fiberwise

/-!
# Source equivalences of path-space homotopy pullbacks

Source homotopy equivalences induce homotopy and fiberwise equivalences of the actual path-space
    homotopy pullbacks.
-/
/-! Implementation source: `Quillen/Topology/HomotopyPullback/SourceEquivalence.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The prescribed continuous maps and
uniform parameter-preserving homotopies are retained. -/
@[expose] public section


noncomputable section
open scoped Topology unitInterval
open unitInterval
universe u
namespace Topology.HomotopyPullback
variable {X A Y : Type u} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace Y]
  {f f' : C(X, Y)} (q : C(A, Y))

/-- Regard a point of the total homotopy pullback as a point of its actual fiber. -/
def fiberPart (z : HomotopyPullback f q) : HomotopyFiber f (q z.1.1) := ⟨z.1.2, z.2⟩

/-- Reassemble a parameter and an actual homotopy-fiber point. -/
def fromFiber (a : A) (z : HomotopyFiber f (q a)) : HomotopyPullback f q := ⟨(a, z.1), z.2⟩

/-- Uniform source change keeps both the parameter and target path unchanged. -/
def sourceMap {Z : Type u} [TopologicalSpace Z] (f : C(X, Y)) (k : C(Z, X)) :
    C(HomotopyPullback (f.comp k) q, HomotopyPullback f q) where
  toFun z := ⟨(z.1.1, k z.1.2.1, z.1.2.2), z.2⟩
  continuous_toFun := by fun_prop

@[simp] theorem sourceMap_parameter {Z : Type u} [TopologicalSpace Z]
    (f : C(X, Y)) (k : C(Z, X)) (z : HomotopyPullback (f.comp k) q) :
    (sourceMap q f k z).1.1 = z.1.1 := rfl

/-- Homotopic defining maps give a uniform change of path-space pullbacks. -/
def homotopyMap (H : f.Homotopy f') : C(HomotopyPullback f q, HomotopyPullback f' q) where
  toFun z := fromFiber q z.1.1 (HomotopyFiber.homotopyMap H (q z.1.1) (fiberPart q z))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    refine Path.trans_continuous_family
      (fun z : HomotopyPullback f q ↦ (H.evalAt z.1.2.1).symm) ?_
      (fun z : HomotopyPullback f q ↦ HomotopyFiber.toPath f (q z.1.1) (fiberPart q z)) ?_
    · change Continuous (fun z : HomotopyPullback f q × I ↦ H (σ z.2, z.1.1.2.1))
      fun_prop
    · change Continuous (fun z : HomotopyPullback f q × I ↦ z.1.1.2.2 z.2)
      fun_prop

@[simp] theorem homotopyMap_parameter (H : f.Homotopy f') (z : HomotopyPullback f q) :
    (homotopyMap q H z).1.1 = z.1.1 := rfl

/-- The uniform path-prefix cancellation used by the inverse homotopy. -/
def cancelHomotopyPrefixes (H : f.Homotopy f') :
    C(I × HomotopyPullback f q, HomotopyPullback f q) where
  toFun z := fromFiber q z.2.1.1
    (HomotopyFiber.cancelHomotopyPrefixes H (q z.2.1.1) (z.1, fiberPart q z.2))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    refine Path.trans_continuous_family
      (fun z : I × HomotopyPullback f q ↦ HomotopyFiber.homotopyPrefix H z.2.1.2.1 (σ z.1)) ?_
      (fun z : I × HomotopyPullback f q ↦
        (HomotopyFiber.homotopyPrefix H z.2.1.2.1 (σ z.1)).symm.trans
          (HomotopyFiber.toPath f (q z.2.1.1) (fiberPart q z.2))) ?_
    · change Continuous (fun z : (I × HomotopyPullback f q) × I ↦ H (σ z.1.1 * z.2, z.1.2.1.2.1))
      fun_prop
    · refine Path.trans_continuous_family
        (fun z : I × HomotopyPullback f q ↦ (HomotopyFiber.homotopyPrefix H z.2.1.2.1 (σ
          z.1)).symm) ?_
        (fun z : I × HomotopyPullback f q ↦ HomotopyFiber.toPath f (q z.2.1.1) (fiberPart q z.2)) ?_
      · change Continuous (fun z : (I × HomotopyPullback f q) × I ↦ H (σ z.1.1 * σ z.2,
        z.1.2.1.2.1))
        fun_prop
      · change Continuous (fun z : (I × HomotopyPullback f q) × I ↦ z.1.2.1.2.2 z.2)
        fun_prop

/-- Uniform removal of the two constant prefixes. -/
def unpadTwice (f : C(X, Y)) : C(I × HomotopyPullback f q, HomotopyPullback f q) where
  toFun z := fromFiber q z.2.1.1
    (HomotopyFiber.unpadTwice f (q z.2.1.1) (z.1, fiberPart q z.2))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (I × HomotopyPullback f q) × I ↦
      z.1.2.1.2.2 (σ (qRight (σ (σ (qRight (σ z.2, z.1.1))), z.1.1))))
    fun_prop

@[simp] theorem cancelHomotopyPrefixes_zero (H : f.Homotopy f') (z : HomotopyPullback f q) :
    cancelHomotopyPrefixes q H (0, z) = homotopyMap q H.symm (homotopyMap q H z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg Subtype.val (HomotopyFiber.cancelHomotopyPrefixes_zero H (q z.1.1) (fiberPart
    q z))

@[simp] theorem cancelHomotopyPrefixes_one (H : f.Homotopy f') (z : HomotopyPullback f q) :
    cancelHomotopyPrefixes q H (1, z) = unpadTwice q f (0, z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg Subtype.val (HomotopyFiber.cancelHomotopyPrefixes_one H (q z.1.1) (fiberPart
    q z))

@[simp] theorem unpadTwice_one (f : C(X, Y)) (z : HomotopyPullback f q) :
    unpadTwice q f (1, z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg Subtype.val (HomotopyFiber.unpadTwice_one f (q z.1.1) (fiberPart q z))

/-- The self-map of the homotopy pullback whose path has two constant prefixes, obtained as the
time-zero slice of `unpadTwice`; its base and source coordinates are retained. -/
def doublePadded (f : C(X, Y)) : C(HomotopyPullback f q, HomotopyPullback f q) where
  toFun z := unpadTwice q f (0, z)
  continuous_toFun := (unpadTwice q f).continuous.comp (by fun_prop)

/-- An actual uniform inverse homotopy for change of defining map. -/
def homotopyMapLeftInverse (H : f.Homotopy f') :
    ((homotopyMap q H.symm).comp (homotopyMap q H)).Homotopy
      (ContinuousMap.id (HomotopyPullback f q)) :=
  (show ((homotopyMap q H.symm).comp (homotopyMap q H)).Homotopy (doublePadded q f) from
    { toContinuousMap := cancelHomotopyPrefixes q H
      map_zero_left := cancelHomotopyPrefixes_zero q H
      map_one_left := cancelHomotopyPrefixes_one q H }).trans
  { toContinuousMap := unpadTwice q f
    map_zero_left := fun _ ↦ rfl
    map_one_left := unpadTwice_one q f }

/-- The uniform inverse homotopy never changes the parameter. -/
theorem homotopyMapLeftInverse_parameter (H : f.Homotopy f') (t : I) (z : HomotopyPullback f q) :
    (homotopyMapLeftInverse q H (t, z)).1.1 = z.1.1 := by
  simp only [homotopyMapLeftInverse, ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl

/-- Uniform homotopy equivalence under a homotopy of the defining map. -/
def homotopyEquiv (H : f.Homotopy f') :
    ContinuousMap.HomotopyEquiv (HomotopyPullback f q) (HomotopyPullback f' q) where
  toFun := homotopyMap q H
  invFun := homotopyMap q H.symm
  left_inv := ⟨homotopyMapLeftInverse q H⟩
  right_inv := by
    simpa only [ContinuousMap.Homotopy.symm_symm] using
      (show ((homotopyMap q H.symm.symm).comp (homotopyMap q H.symm)).Homotopic
        (ContinuousMap.id (HomotopyPullback f' q)) from ⟨homotopyMapLeftInverse q H.symm⟩)

/-- Homotopy change is an explicit equivalence over the parameter, including
both actual inverse homotopies. -/
def homotopyFiberwiseEquiv (H : f.Homotopy f') :
    FiberwiseHomotopyEquiv (baseProjection f q) (baseProjection f' q) where
  toMap := homotopyMap q H
  invMap := homotopyMap q H.symm
  left := homotopyMapLeftInverse q H
  right := (homotopyMapLeftInverse q H.symm).cast (by simp) rfl
  to_over := fun _ ↦ rfl
  inv_over := fun _ ↦ rfl
  left_over := homotopyMapLeftInverse_parameter q H
  right_over := homotopyMapLeftInverse_parameter q H.symm

/-- Uniform source slide, retaining its parameter while correcting the path. -/
def sourceSlide (f : C(X, Y)) {k : C(X, X)} (H : k.Homotopy (ContinuousMap.id X)) :
    C(I × HomotopyPullback (f.comp k) q, HomotopyPullback f q) where
  toFun z := fromFiber q z.2.1.1
    (HomotopyFiber.sourceSlide f H (q z.2.1.1) (z.1, fiberPart q z.2))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    refine Path.trans_continuous_family
      (fun z : I × HomotopyPullback (f.comp k) q ↦
        (HomotopyFiber.homotopyPrefix H z.2.1.2.1 z.1).symm.map f.continuous) ?_
      (fun z : I × HomotopyPullback (f.comp k) q ↦
        HomotopyFiber.toPath (f.comp k) (q z.2.1.1) (fiberPart q z.2)) ?_
    · change Continuous (fun z : (I × HomotopyPullback (f.comp k) q) × I ↦
        f (H (z.1.1 * σ z.2, z.1.2.1.2.1)))
      fun_prop
    · change Continuous (fun z : (I × HomotopyPullback (f.comp k) q) × I ↦
        z.1.2.1.2.2 z.2)
      fun_prop

/-- Uniform removal of the source-slide's constant initial padding. -/
def sourceUnpad (f : C(X, Y)) (k : C(X, X)) :
    C(I × HomotopyPullback (f.comp k) q, HomotopyPullback f q) where
  toFun z := fromFiber q z.2.1.1
    (HomotopyFiber.sourceUnpad f k (q z.2.1.1) (z.1, fiberPart q z.2))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk (by fun_prop)
    apply Continuous.prodMk (by fun_prop)
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : (I × HomotopyPullback (f.comp k) q) × I ↦
      z.1.2.1.2.2 (σ (qRight (σ z.2, z.1.1))))
    fun_prop

@[simp] theorem sourceSlide_zero (f : C(X, Y)) {k : C(X, X)}
    (H : k.Homotopy (ContinuousMap.id X)) (z : HomotopyPullback (f.comp k) q) :
    sourceSlide q f H (0, z) = sourceUnpad q f k (0, z) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg Subtype.val (HomotopyFiber.sourceSlide_zero f H (q z.1.1) (fiberPart q z))

@[simp] theorem sourceSlide_one (f : C(X, Y)) {k : C(X, X)}
    (H : k.Homotopy (ContinuousMap.id X)) (z : HomotopyPullback (f.comp k) q) :
    sourceSlide q f H (1, z) = homotopyMap q ((ContinuousMap.Homotopy.refl f).comp H) z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg Subtype.val (HomotopyFiber.sourceSlide_one f H (q z.1.1) (fiberPart q z))

@[simp] theorem sourceUnpad_one (f : C(X, Y)) (k : C(X, X))
    (z : HomotopyPullback (f.comp k) q) : sourceUnpad q f k (1, z) = sourceMap q f k z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrArg Subtype.val (HomotopyFiber.sourceUnpad_one f k (q z.1.1) (fiberPart q z))

/-- The canonical source map has a uniform homotopy to homotopy change. -/
def sourceMapHomotopy (f : C(X, Y)) {k : C(X, X)}
    (H : k.Homotopy (ContinuousMap.id X)) :
    (sourceMap q f k).Homotopy (homotopyMap q ((ContinuousMap.Homotopy.refl f).comp H)) :=
  let padded : C(HomotopyPullback (f.comp k) q, HomotopyPullback f q) :=
    ⟨fun z ↦ sourceUnpad q f k (0, z), (sourceUnpad q f k).continuous.comp (by fun_prop)⟩
  (show padded.Homotopy (sourceMap q f k) from
    { toContinuousMap := sourceUnpad q f k
      map_zero_left := fun _ ↦ rfl
      map_one_left := sourceUnpad_one q f k }).symm.trans
  { toContinuousMap := sourceSlide q f H
    map_zero_left := sourceSlide_zero q f H
    map_one_left := sourceSlide_one q f H }

/-- The whole source-map homotopy stays over the original parameter. -/
theorem sourceMapHomotopy_parameter (f : C(X, Y)) {k : C(X, X)}
    (H : k.Homotopy (ContinuousMap.id X)) (t : I) (z : HomotopyPullback (f.comp k) q) :
    (sourceMapHomotopy q f H (t, z)).1.1 = z.1.1 := by
  simp only [sourceMapHomotopy, ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> rfl

/-- A map homotopic to identity gives a genuine source equivalence over every
parameter, with actual parameter-preserving inverse homotopies. -/
def sourceSelfFiberwiseEquiv (f : C(X, Y)) {k : C(X, X)}
    (H : k.Homotopy (ContinuousMap.id X)) :
    FiberwiseHomotopyEquiv (baseProjection (f.comp k) q) (baseProjection f q) :=
  (homotopyFiberwiseEquiv q ((ContinuousMap.Homotopy.refl f).comp H)).replaceForward
    (sourceMap q f k) (sourceMapHomotopy q f H) (sourceMapHomotopy_parameter q f H)

/-- Genuine uniform source-equivalence invariance. Neither inverse maps nor
homotopies are selected independently in the fibers. -/
def sourceFiberwiseEquiv {Z : Type u} [TopologicalSpace Z] (f : C(X, Y))
    (e : ContinuousMap.HomotopyEquiv Z X) :
    FiberwiseHomotopyEquiv (baseProjection (f.comp e.toFun) q) (baseProjection f q) :=
  FiberwiseHomotopyEquiv.ofAdjacentComposites
    (sourceMap q f e.toFun)
    (sourceMap q (f.comp e.toFun) e.invFun)
    (sourceMap q ((f.comp e.toFun).comp e.invFun) e.toFun)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    (sourceSelfFiberwiseEquiv q f e.right_inv.some)
    (sourceSelfFiberwiseEquiv q (f.comp e.toFun) e.left_inv.some)
    rfl rfl

/-- The resulting unbased equivalence still retains the canonical source map. -/
def sourceEquiv {Z : Type u} [TopologicalSpace Z] (f : C(X, Y))
    (e : ContinuousMap.HomotopyEquiv Z X) :
    ContinuousMap.HomotopyEquiv (HomotopyPullback (f.comp e.toFun) q) (HomotopyPullback f q) :=
  (sourceFiberwiseEquiv q f e).toHomotopyEquiv

@[simp] theorem sourceEquiv_toFun {Z : Type u} [TopologicalSpace Z]
    (f : C(X, Y)) (e : ContinuousMap.HomotopyEquiv Z X) :
    (sourceEquiv q f e).toFun = sourceMap q f e.toFun := rfl

end Topology.HomotopyPullback

end
