/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.AllWeak.AcyclicInclusion
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformationNaturality
public import Colib.Topology.Realization.HomotopyNaturality

/-! # The entire original acyclic nullhomotopy

The all-weak zero-to-identity cylinder, precomposed with the original
change-of-weak map and postcomposed with the original acyclic inclusion,
is exactly the original zero-to-acyclic-inclusion cylinder. Realization
naturality retains the entire path, including its reversal convention.
No fibration or fiber equivalence is an input.


Implementation provenance:
`Quillen/Waldhausen/Fibration/AllWeak/NullhomotopyNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite MonoidalCategory
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.AllWeak
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- The strict square of the actual original simplicial cylinders. -/
theorem acyclicCylinder_square :
    sSetMap (changeWeak_exact (nested (acyclicStructure N))) ▷ Δ[1] ≫
      weakNaturalTransformationCylinder (waldhausenStructure (acyclicStructure N))
        (waldhausenStructure (acyclicStructure N)) (zeroFunctor_isExact _ _) (IsExact.id _ _)
        (zeroToIdentity (acyclicStructure N)) (fun _ ↦ trivial) ≫
          sSetMap (AllWeak.acyclicInclusion_exact N) =
      weakNaturalTransformationCylinder (acyclicStructure N) N.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
        (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N) := by
  ext n z : 4
  apply Subtype.ext
  change nerveCylinderDiagram (whiskerLeft z.1.val (zeroToIdentity (acyclicStructure N))) z.2.down ⋙
      Fibration.acyclicInclusion N =
    nerveCylinderDiagram (whiskerLeft z.1.val (zeroToAcyclicInclusion N)) z.2.down
  rw [nerveCylinderDiagram_postcomp]
  apply nerveCylinderDiagram_congr_app _ _ _ rfl _
  · refine CategoryTheory.Functor.ext (fun _ ↦ N.zero_eq.symm) ?_
    intro i j f
    exact V.isZero.eq_of_src _ _
  · intro p
    exact (heq_of_eq (zeroToIdentity_acyclicInclusion_app N (z.1.val.obj p))).trans
      (eqToHom_comp_heq ((zeroToAcyclicInclusion N).app (z.1.val.obj p)) N.zero_eq.symm)

/-- Every time and point of the original reversed acyclic nullhomotopy is
exactly the postcomposed all-weak contraction, with its original source map. -/
theorem contraction_acyclicNullhomotopy (t : unitInterval)
    (x : (acyclicStructure N).Delooping) :
    deloopingMap (AllWeak.acyclicInclusion_exact N)
      (contraction (acyclicStructure N)
        (t, changeWeakMap (nested (acyclicStructure N)) x)) = acyclicNullhomotopy N (t, x) := by
  exact SSet.realizationSimplicialHomotopy_naturality
    (weakNaturalTransformationHomotopy (waldhausenStructure (acyclicStructure N))
      (waldhausenStructure (acyclicStructure N)) (zeroFunctor_isExact _ _) (IsExact.id _ _)
      (zeroToIdentity (acyclicStructure N)) (fun _ ↦ trivial))
    (weakNaturalTransformationHomotopy (acyclicStructure N) N.coarse
      (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
      (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N))
    (sSetMap (changeWeak_exact (nested (acyclicStructure N))))
    (sSetMap (AllWeak.acyclicInclusion_exact N)) (acyclicCylinder_square N) (unitInterval.symm t) x

end CategoryTheory.Waldhausen.Fibration.AllWeak
