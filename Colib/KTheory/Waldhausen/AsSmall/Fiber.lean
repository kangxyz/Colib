/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.AsSmall.Acyclic
public import Colib.KTheory.Waldhausen.Fibration.CanonicalFiberMap
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformationNaturality
public import Colib.Topology.Realization.HomotopyNaturality
public import Colib.Topology.HomotopyFiber.Homeomorph
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceCancellation
public import Colib.Topology.HomotopyFiber.Congruence
public import Colib.CategoryTheory.TheoremB.VertexWeakAssembly
public import Colib.CategoryTheory.TheoremB.ReplacementProjectionTower

/-!
# Exact transport of the original canonical fiber comparison

The common-universe model preserves the actual change-of-weak arrow, the
actual acyclic subcategory, and every point of the reversed zero-to-inclusion
nullhomotopy. Weakness therefore transports for the original canonical map.


Implementation provenance:
`Quillen/Waldhausen/SmallModel/Fiber.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {W : Structure C} (N : NestedWeakEquivalences W)

/-- The original and lifted acyclic cylinders commute strictly, before realization. -/
theorem acyclicSmallCylinder_square :
    (acyclicSmallSSetIso N).hom ▷ Δ[1] ≫
      weakNaturalTransformationCylinder (acyclicStructure N.asSmall) N.asSmall.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N.asSmall)
        (zeroToAcyclicInclusion N.asSmall) (zeroToAcyclicInclusion_weak N.asSmall) =
    weakNaturalTransformationCylinder (acyclicStructure N) N.coarse
      (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
      (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) ≫
        N.coarse.asSmallSSetIso.hom := by
  ext n z : 4
  apply Subtype.ext
  change nerveCylinderDiagram
    (Functor.whiskerLeft (z.1.val ⋙ acyclicSmallUp N) (zeroToAcyclicInclusion N.asSmall))
      z.2.down =
      nerveCylinderDiagram (Functor.whiskerLeft z.1.val (zeroToAcyclicInclusion N)) z.2.down ⋙
        (AsSmall.up : C ⥤ AsSmall.{0} C)
  rw [nerveCylinderDiagram_postcomp]
  apply nerveCylinderDiagram_congr_app _ _ rfl rfl
  intro p
  exact heq_of_eq (N.asSmall.coarse.isZero.eq_of_src _ _)

/-- Every point of the original reversed acyclic nullhomotopy is preserved. -/
theorem acyclicSmallNullhomotopy (t : unitInterval) (x : (acyclicStructure N).Delooping) :
    N.coarse.asSmallDeloopingHomeomorph (acyclicNullhomotopy N (t,x)) =
      acyclicNullhomotopy N.asSmall (t, acyclicSmallDeloopingHomeomorph N x) := by
  have hs : (acyclicSmallSSetIso N).hom ▷ Δ[1] ≫
      weakNaturalTransformationCylinder (acyclicStructure N.asSmall) N.asSmall.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N.asSmall)
        (zeroToAcyclicInclusion N.asSmall) (zeroToAcyclicInclusion_weak N.asSmall) ≫
      N.coarse.asSmallSSetIso.inv =
      weakNaturalTransformationCylinder (acyclicStructure N) N.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
        (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) := by
    rw [← Category.assoc, acyclicSmallCylinder_square, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hh := SSet.realizationSimplicialHomotopy_naturality
    (weakNaturalTransformationHomotopy (acyclicStructure N.asSmall) N.asSmall.coarse
      (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N.asSmall)
      (zeroToAcyclicInclusion N.asSmall) (zeroToAcyclicInclusion_weak N.asSmall))
    (weakNaturalTransformationHomotopy (acyclicStructure N) N.coarse
      (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
      (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N))
    (acyclicSmallSSetIso N).hom N.coarse.asSmallSSetIso.inv hs (unitInterval.symm t) x
  apply N.coarse.asSmallDeloopingHomeomorph.symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact hh.symm

/-- The original change-of-weak map commutes with both actual realization homeomorphisms. -/
theorem asSmall_changeWeak_square :
    N.coarse.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun.comp (changeWeakMap N) =
      (changeWeakMap N.asSmall).comp W.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun := by
  change (SSet.toTop.map (sSetMap (changeWeak_exact N)) ≫
      SSet.toTop.map N.coarse.asSmallSSetIso.hom).hom =
    (SSet.toTop.map W.asSmallSSetIso.hom ≫
      SSet.toTop.map (sSetMap (changeWeak_exact N.asSmall))).hom
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, asSmallSSetIso_changeWeak]

/-- The homeomorphism of actual original fibers retains the source and entire path. -/
def asSmallChangeWeakFiberHomeomorph :
    HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint ≃ₜ
      HomotopyFiber (changeWeakMap N.asSmall) N.asSmall.coarse.kBasepoint :=
  (HomotopyFiber.homeomorphOfSquare (changeWeakMap N) (changeWeakMap N.asSmall)
    W.asSmallDeloopingHomeomorph N.coarse.asSmallDeloopingHomeomorph
    (asSmall_changeWeak_square N) N.coarse.kBasepoint).trans
      (HomotopyFiber.congrHomeomorph rfl N.coarse.asSmallDeloopingHomeomorph_basepoint)

@[simp] theorem asSmallChangeWeakFiberHomeomorph_source
    (z : HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) :
    (asSmallChangeWeakFiberHomeomorph N z).val.1 = W.asSmallDeloopingHomeomorph z.val.1 := rfl

@[simp] theorem asSmallChangeWeakFiberHomeomorph_path
    (z : HomotopyFiber (changeWeakMap N) N.coarse.kBasepoint) :
    (asSmallChangeWeakFiberHomeomorph N z).val.2 =
      N.coarse.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun.comp z.val.2 := rfl

/-- The exact original canonical comparison square, including its full stored path. -/
theorem asSmall_canonicalFiberMap_square :
    (asSmallChangeWeakFiberHomeomorph N).toHomotopyEquiv.toFun.comp (canonicalFiberMap N) =
      (canonicalFiberMap N.asSmall).comp (acyclicSmallDeloopingHomeomorph
        N).toHomotopyEquiv.toFun := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · have hs := congrArg (fun f ↦ (SSet.toTop.map f).hom) (acyclicSmallSSetIso_inclusion N)
    rw [SSet.toTop.map_comp, SSet.toTop.map_comp] at hs
    exact ContinuousMap.congr_fun hs x
  · apply ContinuousMap.ext
    intro t
    exact acyclicSmallNullhomotopy N t x

/-- Weakness in the common-universe model implies weakness of the unchanged original map. -/
theorem canonicalFiberMap_isWeakHomotopyEquivalence_of_asSmall
    (h : IsWeakHomotopyEquivalence (canonicalFiberMap N.asSmall)) :
    IsWeakHomotopyEquivalence (canonicalFiberMap N) := by
  have hh := h.comp (isWeakHomotopyEquivalence_of_homotopyEquiv
    (acyclicSmallDeloopingHomeomorph N).toHomotopyEquiv)
  rw [← asSmall_canonicalFiberMap_square] at hh
  exact hh.of_comp_right (isWeakHomotopyEquivalence_of_homotopyEquiv
    (asSmallChangeWeakFiberHomeomorph N).toHomotopyEquiv)

end CategoryTheory.Waldhausen.Fibration
