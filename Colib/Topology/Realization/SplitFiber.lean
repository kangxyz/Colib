/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.ProductFiber

/-! # Actual row fibers from a prescribed split product comparison

A genuine homotopy equivalence from a row to a simplicial product, together
with its actual constant-tail splitting, implies every finite homotopy-set
bijection for the original constant-path fiber inclusion. The input is the
product comparison itself, not a fiber-equivalence conclusion.


Implementation provenance:
`Quillen/Topology/Realization/SplitFiber.lean`
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

namespace SSet.SplitRealizationFiber
variable {A B E : SSet.{u}} (χ : E ⟶ A ⊗ B)

/-- The actual realized second projection after the row comparison. -/
def projection : C(|E|, |B|) :=
  (SSet.toTop.map (snd A B)).hom.comp (SSet.toTop.map χ).hom

/-- Source change along the original row comparison retains its complete path. -/
def comparison (y : |B|) :
    C(HomotopyFiber (projection χ) y,
      HomotopyFiber (SSet.toTop.map (snd A B)).hom y) :=
  HomotopyFiber.sourceMap (SSet.toTop.map (snd A B)).hom (SSet.toTop.map χ).hom y

@[simp] theorem comparison_apply (y : |B|) (p : HomotopyFiber (projection χ) y) :
    (comparison χ y p).1 = (SSet.toTop.map χ p.1.1, p.1.2) := rfl

/-- An actual row comparison equivalence induces the canonical source-fiber
map as an actual homotopy equivalence. -/
def comparisonHomotopyEquiv
    (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|)
    (he : e.toFun = (SSet.toTop.map χ).hom) (y : |B|) :
    ContinuousMap.HomotopyEquiv (HomotopyFiber (projection χ) y)
      (HomotopyFiber (SSet.toTop.map (snd A B)).hom y) := by
  let e' : ContinuousMap.HomotopyEquiv |E| |A ⊗ B| := {
    e with toFun := (SSet.toTop.map χ).hom
           left_inv := by simpa only [he] using e.left_inv
           right_inv := by simpa only [he] using e.right_inv }
  exact HomotopyFiber.sourceEquiv (SSet.toTop.map (snd A B)).hom e' y

@[simp] theorem comparisonHomotopyEquiv_toFun
    (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|)
    (he : e.toFun = (SSet.toTop.map χ).hom) (y : |B|) :
    (comparisonHomotopyEquiv χ e he y).toFun = comparison χ y := rfl

/-- The original first projection on the source coordinate of the fiber. -/
def firstProjection (y : |B|) : C(HomotopyFiber (projection χ) y, |A|) :=
  (ProductRealization.fiberProjection A B y).comp (comparison χ y)

@[simp] theorem firstProjection_apply (y : |B|) (p : HomotopyFiber (projection χ) y) :
    firstProjection χ y p = SSet.toTop.map (χ ≫ fst A B) p.1.1 := by
  change (SSet.toTop.map χ ≫ SSet.toTop.map (fst A B)) p.1.1 = _
  rw [← Functor.map_comp]

/-- Degreewise product additivity supplies every finite homotopy-set bijection
on the actual row fiber, through its original first projection. -/
theorem firstProjection_bijective
    (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|)
    (he : e.toFun = (SSet.toTop.map χ).hom) (y : |B|)
    (p : HomotopyFiber (projection χ) y) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (firstProjection χ y) (x := p) rfl) :=
  homotopyGroupMap_bijective_comp (comparison χ y) (ProductRealization.fiberProjection A B y)
    rfl rfl n
    (homotopyGroupMap_bijective_of_homotopyEquiv (comparisonHomotopyEquiv χ e he y) rfl n)
    (ProductRealization.fiberProjection_bijective A B y (comparison χ y p) n)

variable (s : A ⟶ E) (y : B _⦋0⦌)
  (hs : s ≫ χ = ProductRealization.vertexSection A B y)

include hs

/-- The literal split inclusion has exactly the chosen constant tail. -/
theorem projection_section (x : |A|) :
    projection χ (SSet.toTop.map s x) = SSet.realizationPoint y := by
  change SSet.toTop.map (snd A B) ((SSet.toTop.map s ≫ SSet.toTop.map χ) x) = _
  rw [← Functor.map_comp, hs]
  exact ProductRealization.vertexSection_snd A B y x

/-- The prescribed original split inclusion, equipped with its constant path. -/
def inclusion : C(|A|, HomotopyFiber (projection χ) (SSet.realizationPoint y)) where
  toFun x := HomotopyFiber.basepoint _ _ (SSet.toTop.map s x) (projection_section χ s y hs x)
  continuous_toFun := by unfold HomotopyFiber.basepoint; fun_prop

@[simp] theorem inclusion_path (x : |A|) :
    (inclusion χ s y hs x).1.2 = ContinuousMap.const _ (SSet.realizationPoint y) := rfl

/-- The comparison identifies the whole original fiber inclusion, including
its path coordinate, with the actual product fiber inclusion. -/
theorem comparison_inclusion :
    (comparison χ (SSet.realizationPoint y)).comp (inclusion χ s y hs) =
      ProductRealization.fiberInclusion A B y := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · change (SSet.toTop.map s ≫ SSet.toTop.map χ) x = _
    rw [← Functor.map_comp, hs]
    rfl
  · rfl

/-- The original split inclusion induces every finite based homotopy-set
bijection, including dimension zero, from actual product additivity. -/
theorem inclusion_bijective
    (e : ContinuousMap.HomotopyEquiv |E| |A ⊗ B|)
    (he : e.toFun = (SSet.toTop.map χ).hom) (x : |A|) (n : ℕ) :
    Function.Bijective (HomotopyGroup.map (N := Fin n) (inclusion χ s y hs) (x := x) rfl) := by
  let f := inclusion χ s y hs
  let g := comparison χ (SSet.realizationPoint y)
  have hgf : g.comp f = ProductRealization.fiberInclusion A B y := comparison_inclusion χ s y hs
  have hp : g (f x) = ProductRealization.fiberInclusion A B y x :=
    ContinuousMap.congr_fun hgf x
  have hg : Function.Bijective (HomotopyGroup.map (N := Fin n) g (x := f x) hp) :=
    homotopyGroupMap_bijective_of_homotopyEquiv
      (comparisonHomotopyEquiv χ e he (SSet.realizationPoint y)) hp n
  have hcomp : Function.Bijective (HomotopyGroup.map (N := Fin n) (g.comp f) (x := x) hp) := by
    rw [homotopyGroupMap_congr hgf hp rfl]
    exact ProductRealization.fiberInclusion_bijective A B y x n
  have heq : HomotopyGroup.map (N := Fin n) (g.comp f) (x := x) hp =
      (HomotopyGroup.map (N := Fin n) g (x := f x) hp) ∘
        (HomotopyGroup.map (N := Fin n) f (x := x) rfl) := by
    funext a
    exact HomotopyGroup.map_comp f rfl g hp a
  rw [heq] at hcomp
  exact (Function.Bijective.of_comp_iff' hg _).1 hcomp

end SSet.SplitRealizationFiber
