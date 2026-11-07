/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.ProductComparison
public import Colib.Topology.HomotopyFiber.CompactLifting
public import Colib.Topology.HomotopyFiber.Product
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalence
public import Colib.Topology.ClassifyingSpace.Constant

/-! # Actual fibers of simplicial-product realization projections

The prescribed canonical realization-product comparison gives exact compact
lifts on the actual projection homotopy fiber. Composing with the explicit
ordinary-product fiber contraction proves every finite homotopy-set bijection.
No unrestricted realization-product homeomorphism is used.


Implementation provenance:
`Quillen/Topology/Realization/ProductFiber.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open Topology CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology
universe u

namespace SSet.ProductRealization
variable (X Y : SSet.{u})

/-- The canonical map retains the source point and its original path. -/
def sourceFiberComparison (y : |Y|) :
    C(HomotopyFiber (SSet.toTop.map (snd X Y)).hom y,
      HomotopyFiber (ContinuousMap.snd : C(|X| × |Y|, |Y|)) y) :=
  HomotopyFiber.sourceMap ContinuousMap.snd (comparison X Y) y

@[simp] theorem sourceFiberComparison_apply (y : |Y|)
    (p : HomotopyFiber (SSet.toTop.map (snd X Y)).hom y) :
    (sourceFiberComparison X Y y p).1 = (comparison X Y p.1.1, p.1.2) := rfl

/-- The canonical comparison on actual product-projection fibers induces all
finite based homotopy-set bijections, including dimension zero. -/
theorem sourceFiberComparison_bijective (y : |Y|)
    (p : HomotopyFiber (SSet.toTop.map (snd X Y)).hom y) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (sourceFiberComparison X Y y)
      (x := p) rfl) :=
  HomotopyFiber.sourceMap_homotopyGroupMap_bijective ContinuousMap.snd (comparison X Y)
    (comparison_injective X Y) (comparison_compact_lifts X Y) y p n

/-- Projection to the first original simplicial factor from the actual fiber. -/
def fiberProjection (y : |Y|) :
    C(HomotopyFiber (SSet.toTop.map (snd X Y)).hom y, |X|) :=
  (HomotopyFiber.sndEquiv |X| y).toFun.comp (sourceFiberComparison X Y y)

/-- The forward map is exactly the original realized first projection. -/
@[simp] theorem fiberProjection_apply (y : |Y|)
    (p : HomotopyFiber (SSet.toTop.map (snd X Y)).hom y) :
    fiberProjection X Y y p = SSet.toTop.map (fst X Y) p.1.1 := rfl

/-- The original first projection induces all finite based homotopy-set
bijections on the actual second-projection homotopy fiber. -/
theorem fiberProjection_bijective (y : |Y|)
    (p : HomotopyFiber (SSet.toTop.map (snd X Y)).hom y) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (fiberProjection X Y y) (x := p) rfl) :=
  homotopyGroupMap_bijective_comp (sourceFiberComparison X Y y)
    (HomotopyFiber.sndEquiv |X| y).toFun rfl rfl n
    (sourceFiberComparison_bijective X Y y p n)
    (homotopyGroupMap_bijective_of_homotopyEquiv (HomotopyFiber.sndEquiv |X| y) rfl n)

/-- The actual constant-tail simplicial inclusion. -/
def vertexSection (y : Y _⦋0⦌) : X ⟶ X ⊗ Y := lift (𝟙 X) (SSet.const y)

/-- The realized section has exactly the displayed constant second coordinate. -/
theorem vertexSection_snd (y : Y _⦋0⦌) (x : |X|) :
    SSet.toTop.map (snd X Y) (SSet.toTop.map (vertexSection X Y y) x) =
      SSet.realizationPoint y := by
  change (SSet.toTop.map (vertexSection X Y y) ≫ SSet.toTop.map (snd X Y)) x = _
  rw [← CategoryTheory.Functor.map_comp]
  simpa only [vertexSection, lift_snd] using (SSet.realization_const_apply (X := X) y x)

/-- The prescribed constant-path inclusion into the actual realized fiber. -/
def fiberInclusion (y : Y _⦋0⦌) :
    C(|X|, HomotopyFiber (SSet.toTop.map (snd X Y)).hom (SSet.realizationPoint y)) where
  toFun x := HomotopyFiber.basepoint _ _ (SSet.toTop.map (vertexSection X Y y) x)
    (vertexSection_snd X Y y x)
  continuous_toFun := by unfold HomotopyFiber.basepoint; fun_prop

/-- The original first projection retracts this exact constant-path inclusion. -/
theorem fiberProjection_inclusion (y : Y _⦋0⦌) :
    (fiberProjection X Y (SSet.realizationPoint y)).comp (fiberInclusion X Y y) = ContinuousMap.id
      |X| := by
  apply ContinuousMap.ext
  intro x
  change (SSet.toTop.map (vertexSection X Y y) ≫ SSet.toTop.map (fst X Y)) x = x
  rw [← CategoryTheory.Functor.map_comp]
  simp [vertexSection]

/-- The original constant-path fiber inclusion induces every finite based
homotopy-set bijection, including dimension zero. -/
theorem fiberInclusion_bijective (y : Y _⦋0⦌) (x : |X|) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (fiberInclusion X Y y) (x := x) rfl) := by
  let f := fiberInclusion X Y y
  let g := fiberProjection X Y (SSet.realizationPoint y)
  have hgf : g.comp f = ContinuousMap.id |X| := fiberProjection_inclusion X Y y
  have hp : g (f x) = x := DFunLike.congr_fun hgf x
  have hg : Function.Bijective (HomotopyGroup.map (N := Fin n) g hp) := by
    exact homotopyGroupMap_bijective_comp (sourceFiberComparison X Y (SSet.realizationPoint y))
      (HomotopyFiber.sndEquiv |X| (SSet.realizationPoint y)).toFun rfl hp n
      (sourceFiberComparison_bijective X Y (SSet.realizationPoint y) (f x) n)
      (homotopyGroupMap_bijective_of_homotopyEquiv
        (HomotopyFiber.sndEquiv |X| (SSet.realizationPoint y)) hp n)
  have hi (a : HomotopyGroup (Fin n) |X| x) :
      HomotopyGroup.map g hp (HomotopyGroup.map f rfl a) = a := by
    rw [← HomotopyGroup.map_comp f rfl g hp]
    rw [homotopyGroupMap_congr hgf _ rfl]
    exact HomotopyGroup.map_id a
  constructor
  · intro a b hab
    exact (hi a).symm.trans ((congrArg (HomotopyGroup.map g hp) hab).trans (hi b))
  · intro a
    refine ⟨HomotopyGroup.map g hp a, ?_⟩
    apply hg.injective
    exact hi _

end SSet.ProductRealization
