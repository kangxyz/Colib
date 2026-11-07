/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.HomotopyCofiber.ReducedMappingConeCollapse
public import Colib.Topology.HomotopyFiber.PointComparison
public import Colib.Topology.Homotopy.HomotopyGroup.Connectivity.EquivalenceSquare

/-!
# The literal cone-to-fiber gap through original base-line collapse

The actual reduction from the ordinary cone to the reduced cone induces an equivalence of
its original inclusion fibers when the chosen source and target points have HEP. This
comparison retains every source coordinate and postcomposes the entire stored path with the
actual collapse. It carries the full unreduced cylinder gap to the literal reduced cylinder
gap, and therefore transports its finite connectivity without changing the original map.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyCofiber/ReducedMappingConeFiberReduction.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original objects, maps,
point hypotheses, whole stored cylinder paths and universe parameters are
retained. Native namespace and lower-import ownership are used. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Topology.ReducedMappingCone
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀)

/-- The literal inclusion of the target in the original ordinary cone. -/
def unreducedInclusion : C(Y, UnreducedSpace f) :=
  ⟨fun y ↦ unreducedEnd f (Sum.inl y), by fun_prop⟩

/-- The original cone tip before collapsing the chosen-point interval. -/
def unreducedVertex : UnreducedSpace f := unreducedEnd f (Sum.inr PUnit.unit)

/-- The full ordinary cone cylinder, as the original source-to-fiber map. -/
def unreducedFiberComparison : C(X, HomotopyFiber (unreducedInclusion f) (unreducedVertex f)) where
  toFun x := ⟨(f x, ⟨fun t ↦ unreducedCylinder f (x, ULift.up t), by fun_prop⟩),
    ConcreteCategory.congr_hom (unreducedSquare f).w (Sum.inl x),
    ConcreteCategory.congr_hom (unreducedSquare f).w (Sum.inr x)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk f.continuous
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : X × unitInterval ↦ unreducedCylinder f (z.1, ULift.up z.2))
    fun_prop

/-- The unchanged reduced cylinder is the canonical source-to-inclusion-fiber map. -/
def fiberComparison : C(X, HomotopyFiber (inr x₀ y₀ f) (point x₀ y₀ f)) where
  toFun x := ⟨(f x, ⟨fun t ↦ cylinder x₀ y₀ f (t, x), by fun_prop⟩),
    cylinder_zero x₀ y₀ f x, cylinder_one x₀ y₀ f x⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk f.continuous
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun z : X × unitInterval ↦ cylinder x₀ y₀ f (z.2, z.1))
    fun_prop

/-- The original full cylinder parameter is unchanged in the reduced gap. -/
@[simp] theorem fiberComparison_path (x : X) (t : unitInterval) :
    (fiberComparison x₀ y₀ f x).1.2 t = cylinder x₀ y₀ f (t, x) := rfl

/-- Reduction preserves the original target inclusion strictly. -/
theorem reduction_unreducedInclusion :
    (reduction x₀ y₀ f).hom.comp (unreducedInclusion f) = inr x₀ y₀ f := by
  ext y
  exact reduction_end x₀ y₀ f (Sum.inl y)

/-- The literal old cone tip maps to the unchanged reduced cone point. -/
theorem reduction_unreducedVertex :
    reduction x₀ y₀ f (unreducedVertex f) = point x₀ y₀ f :=
  reduction_end x₀ y₀ f (Sum.inr PUnit.unit)

variable
  (hX : TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀)))
  (hY : TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y₀)))

/-- Genuine chosen-point HEP gives the original collapse-induced equivalence of inclusion fibers. -/
def fiberReductionEquiv :
    ContinuousMap.HomotopyEquiv
      (HomotopyFiber (unreducedInclusion f) (unreducedVertex f))
      (HomotopyFiber (inr x₀ y₀ f) (point x₀ y₀ f)) :=
  (HomotopyFiber.mapHomotopyEquivOfEquivalences
    (p := unreducedInclusion f) (q := inr x₀ y₀ f)
    (ContinuousMap.HomotopyEquiv.refl Y) (reductionHomotopyEquiv x₀ y₀ f hf hX hY)
    (by ext y; exact reduction_end x₀ y₀ f (Sum.inl y)) (unreducedVertex f)).trans
      (HomotopyFiber.basepointEqHomeomorph (inr x₀ y₀ f)
        (reduction_unreducedVertex x₀ y₀ f)).toHomotopyEquiv

/-- The original fiber source and the entire path postcomposition are retained literally. -/
@[simp] theorem fiberReductionEquiv_val
    (z : HomotopyFiber (unreducedInclusion f) (unreducedVertex f)) :
    (fiberReductionEquiv x₀ y₀ f hf hX hY z).1 =
      (z.1.1, (reduction x₀ y₀ f).hom.comp z.1.2) := rfl

/-- Actual collapse sends the whole unreduced cylinder gap to the unchanged reduced gap. -/
theorem fiberReductionEquiv_comp_unreducedFiberComparison :
    (fiberReductionEquiv x₀ y₀ f hf hX hY).toFun.comp (unreducedFiberComparison f) =
      fiberComparison x₀ y₀ f := by
  ext x : 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · ext t
    exact reduction_cylinder x₀ y₀ f x (ULift.up t)

include hf hX hY in
/-- The finite range of the original unreduced gap survives the exact chosen-base-line collapse. -/
theorem fiberComparison_isHomotopyConnectedMap_of_unreduced (r : ℕ)
    (hr : IsHomotopyConnectedMap (unreducedFiberComparison f) r) :
    IsHomotopyConnectedMap (fiberComparison x₀ y₀ f) r :=
  IsHomotopyConnectedMap.of_equivalence_square (ContinuousMap.HomotopyEquiv.refl X)
    (fiberReductionEquiv x₀ y₀ f hf hX hY)
    (fiberReductionEquiv_comp_unreducedFiberComparison x₀ y₀ f hf hX hY) r hr

end Topology.ReducedMappingCone
