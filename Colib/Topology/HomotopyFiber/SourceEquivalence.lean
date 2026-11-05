/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.Equiv.AdjacentComposites

public import Colib.Topology.UnitInterval
public import Colib.Topology.HomotopyFiber.Equivalence

/-!
# Invariance under homotopy equivalence of the source

The equivalence constructed here uses the canonical source map as its forward
map. Its proof uses explicit source-sliding homotopies and a two-out-of-six
argument, avoiding triangle-coherence assumptions on the source equivalence.
-/
/-! Implementation source: `Quillen/Topology/HomotopyFiber/SourceEquivalence.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual path-space models,
basepoint tracks, maps and universe parameters are retained. -/
@[expose] public section


noncomputable section
open scoped Topology unitInterval
open unitInterval

universe u v

namespace Topology.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- The canonical map of fibers induced by precomposition in the source. -/
def sourceMap {Z : Type*} [TopologicalSpace Z] (f : C(X, Y)) (u : C(Z, X)) (y : Y) :
    C(HomotopyFiber (f.comp u) y, HomotopyFiber f y) :=
  map u (ContinuousMap.id Y) rfl y

@[simp]
theorem projection_sourceMap {Z : Type*} [TopologicalSpace Z]
    (f : C(X, Y)) (u : C(Z, X)) (y : Y) :
    (projection f y).comp (sourceMap f u y) = u.comp (projection (f.comp u) y) := rfl

@[simp]
theorem sourceMap_comp {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W]
    (f : C(X, Y)) (u : C(Z, X)) (v : C(W, Z)) (y : Y) :
    (sourceMap f u y).comp (sourceMap (f.comp u) v y) = sourceMap f (u.comp v) y := rfl

/-- Slide a source point along a homotopy to the identity, prepending the
reversed image of the part already traversed to its fiber path. -/
def sourceSlide (f : C(X, Y)) {k : C(X, X)}
    (H : k.Homotopy (ContinuousMap.id X)) (y : Y) :
    C(I × HomotopyFiber (f.comp k) y, HomotopyFiber f y) where
  toFun z := ⟨(H (z.1, z.2.1.1),
    (((homotopyPrefix H z.2.1.1 z.1).symm.map f.continuous).trans
      (toPath (f.comp k) y z.2)).toContinuousMap), Path.source _, Path.target _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      refine Path.trans_continuous_family
        (fun z : I × HomotopyFiber (f.comp k) y =>
          (homotopyPrefix H z.2.1.1 z.1).symm.map f.continuous) ?_
        (fun z : I × HomotopyFiber (f.comp k) y => toPath (f.comp k) y z.2) ?_
      · change Continuous (fun z : (I × HomotopyFiber (f.comp k) y) × I =>
          f (H (z.1.1 * σ z.2, z.1.2.1.1)))
        fun_prop
      · change Continuous (fun z : (I × HomotopyFiber (f.comp k) y) × I =>
          z.1.2.1.2 z.2)
        fun_prop

/-- Remove the constant prefix at the initial end of the source slide. -/
def sourceUnpad (f : C(X, Y)) (k : C(X, X)) (y : Y) :
    C(I × HomotopyFiber (f.comp k) y, HomotopyFiber f y) where
  toFun z := ⟨(k z.2.1.1,
    (Path.delayReflLeft z.1 (toPath (f.comp k) y z.2)).toContinuousMap),
      Path.source _, Path.target _⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · apply ContinuousMap.continuous_of_continuous_uncurry
      change Continuous (fun z : (I × HomotopyFiber (f.comp k) y) × I =>
        z.1.2.1.2 (σ (qRight (σ z.2, z.1.1))))
      fun_prop

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem sourceSlide_zero (f : C(X, Y)) {k : C(X, X)}
    (H : k.Homotopy (ContinuousMap.id X)) (y : Y) (z : HomotopyFiber (f.comp k) y) :
    sourceSlide f H y (0, z) = sourceUnpad f k y (0, z) := by
  apply Subtype.ext
  apply Prod.ext
  · exact H.map_zero_left z.1.1
  · apply ContinuousMap.ext
    intro t
    change (((homotopyPrefix H z.1.1 0).symm.map f.continuous).trans
      (toPath (f.comp k) y z)) t = (Path.delayReflLeft 0 (toPath (f.comp k) y z)) t
    rw [Path.delayReflLeft_zero]
    simp only [Path.trans_apply]
    split_ifs
    · change f (H (0 * σ _, z.1.1)) = f (k z.1.1)
      simp
    · rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem sourceSlide_one (f : C(X, Y)) {k : C(X, X)}
    (H : k.Homotopy (ContinuousMap.id X)) (y : Y) (z : HomotopyFiber (f.comp k) y) :
    sourceSlide f H y (1, z) =
      homotopyMap ((ContinuousMap.Homotopy.refl f).comp H) y z := by
  apply Subtype.ext
  apply Prod.ext
  · exact H.map_one_left z.1.1
  · apply ContinuousMap.ext
    intro t
    change (((homotopyPrefix H z.1.1 1).symm.map f.continuous).trans
      (toPath (f.comp k) y z)) t =
      ((((ContinuousMap.Homotopy.refl f).comp H).evalAt z.1.1).symm.trans
        (toPath (f.comp k) y z)) t
    simp only [Path.trans_apply]
    split_ifs
    · change f (H (1 * σ _, z.1.1)) = f (H (σ _, z.1.1))
      simp
    · rfl

@[simp]
theorem sourceUnpad_one (f : C(X, Y)) (k : C(X, X)) (y : Y)
    (z : HomotopyFiber (f.comp k) y) : sourceUnpad f k y (1, z) = sourceMap f k y z := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (Path.delayReflLeft 1 (toPath (f.comp k) y z)).toContinuousMap = _
    rw [Path.delayReflLeft_one]
    rfl

/-- The canonical source map is homotopic to change of defining map. -/
def sourceMapHomotopy (f : C(X, Y)) {k : C(X, X)}
    (H : k.Homotopy (ContinuousMap.id X)) (y : Y) :
    (sourceMap f k y).Homotopy (homotopyMap ((ContinuousMap.Homotopy.refl f).comp H) y) :=
  let padded : C(HomotopyFiber (f.comp k) y, HomotopyFiber f y) :=
    ⟨fun z => sourceUnpad f k y (0, z), (sourceUnpad f k y).continuous.comp (by fun_prop)⟩
  (show padded.Homotopy (sourceMap f k y) from
    { toContinuousMap := sourceUnpad f k y
      map_zero_left := fun _ => rfl
      map_one_left := sourceUnpad_one f k y }).symm.trans
  { toContinuousMap := sourceSlide f H y
    map_zero_left := sourceSlide_zero f H y
    map_one_left := sourceSlide_one f H y }

/-- Replacing the forward map of an equivalence by a homotopic map preserves
its inverse, with the inverse laws proved by composition of homotopies. -/
def replaceForward {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    (e : ContinuousMap.HomotopyEquiv A B) (p : C(A, B)) (H : p.Homotopic e.toFun) :
    ContinuousMap.HomotopyEquiv A B where
  toFun := p
  invFun := e.invFun
  left_inv := ((ContinuousMap.Homotopic.refl _).comp H).trans e.left_inv
  right_inv := (H.comp (ContinuousMap.Homotopic.refl _)).trans e.right_inv

/-- A self-map homotopic to identity induces an equivalence by its canonical
source map. No coherence between inverse homotopies is needed. -/
def sourceSelfEquiv (f : C(X, Y)) {k : C(X, X)}
    (H : k.Homotopy (ContinuousMap.id X)) (y : Y) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber (f.comp k) y) (HomotopyFiber f y) :=
  replaceForward (homotopyEquiv ((ContinuousMap.Homotopy.refl f).comp H) y)
    (sourceMap f k y) ⟨sourceMapHomotopy f H y⟩

/-- A homotopy equivalence of sources induces an equivalence of the concrete
path-space fibers. Its forward map is the canonical source map, without adding
or changing the target path. -/
def sourceEquiv {Z : Type*} [TopologicalSpace Z] (f : C(X, Y))
    (e : ContinuousMap.HomotopyEquiv Z X) (y : Y) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber (f.comp e.toFun) y) (HomotopyFiber f y) :=
  ContinuousMap.HomotopyEquiv.ofAdjacentComposites
    (sourceMap f e.toFun y)
    (sourceMap (f.comp e.toFun) e.invFun y)
    (sourceMap ((f.comp e.toFun).comp e.invFun) e.toFun y)
    (sourceSelfEquiv f (Classical.choice e.right_inv) y)
    (sourceSelfEquiv (f.comp e.toFun) (Classical.choice e.left_inv) y)
    rfl rfl

@[simp]
theorem sourceEquiv_toFun {Z : Type*} [TopologicalSpace Z] (f : C(X, Y))
    (e : ContinuousMap.HomotopyEquiv Z X) (y : Y) :
    (sourceEquiv f e y).toFun = sourceMap f e.toFun y := rfl

@[simp]
theorem sourceEquiv_apply {Z : Type*} [TopologicalSpace Z] (f : C(X, Y))
    (e : ContinuousMap.HomotopyEquiv Z X) (y : Y)
    (z : HomotopyFiber (f.comp e.toFun) y) :
    sourceEquiv f e y z = sourceMap f e.toFun y z := rfl

/-- A homotopy-commutative change of source by an equivalence induces an
equivalence of fibers, with both path correction and source change explicit. -/
def sourceEquivOfHomotopy {Z : Type*} [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Z, Y)) (e : ContinuousMap.HomotopyEquiv Z X)
    (H : g.Homotopy (f.comp e.toFun)) (y : Y) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber g y) (HomotopyFiber f y) :=
  (homotopyEquiv H y).trans (sourceEquiv f e y)

/-- Every fiber of a homotopy equivalence is contractible in the actual
compact-open path-space model. -/
theorem contractibleSpace_homotopyEquiv {Z : Type*} [TopologicalSpace Z]
    (e : ContinuousMap.HomotopyEquiv Z X) (x : X) :
    ContractibleSpace (HomotopyFiber e.toFun x) :=
  (sourceEquiv (ContinuousMap.id X) e x).contractibleSpace

end Topology.HomotopyFiber
