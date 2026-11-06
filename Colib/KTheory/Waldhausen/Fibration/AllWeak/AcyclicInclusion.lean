/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Fibration.AllWeak.Basic

/-! # The actual acyclic inclusion from the all-weak source

Coarse two-out-of-three proves that every actual acyclic-to-acyclic map is
coarse weak. Thus the original inclusion is exact even when every source
map is declared weak. The original S-map triangle and the original
zero-transformation components are retained explicitly.


Implementation provenance:
`Quillen/Waldhausen/Fibration/AllWeak/AcyclicInclusion.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory CategoryTheory.Limits
open scoped Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.AllWeak
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) [N.coarse.weq.HasTwoOutOfThreeProperty]

/-- The original inclusion is exact from the actual all-weak acyclic structure. -/
theorem acyclicInclusion_exact :
    IsExact (waldhausenStructure (acyclicStructure N)).cof
      (waldhausenStructure (acyclicStructure N)).weq N.coarse.cof N.coarse.weq
      (Fibration.acyclicInclusion N) where
  zero h := (acyclicInclusion_coarse_exact N).zero h
  cofibration f hf := (acyclicInclusion_coarse_exact N).cofibration f hf
  weak {X Y} f _ := weak_of_acyclic N.coarse f.hom X.property Y.property
  pushout hf h := (acyclicInclusion_coarse_exact N).pushout hf h

/-- The unchanged exact functors give a strict original S-map triangle. -/
@[simp] theorem changeWeak_acyclicInclusion_sSetMap :
    sSetMap (changeWeak_exact (nested (acyclicStructure N))) ≫
        sSetMap (acyclicInclusion_exact N) = sSetMap (acyclicInclusion_coarse_exact N) := by
  ext n A
  rfl

/-- The realization triangle retains exactly the original continuous maps. -/
theorem changeWeak_acyclicInclusion_realized :
    (deloopingMap (acyclicInclusion_exact N)).hom.comp
      (changeWeakMap (nested (acyclicStructure N))) =
        (changeWeakMap N).comp (acyclicInclusionMap N) := by
  have h := congrArg (fun f ↦ (SSet.toTop.map f).hom)
    (changeWeak_acyclicInclusion_sSetMap N)
  rw [SSet.toTop.map_comp, TopCat.hom_comp] at h
  exact h.trans (congrArg TopCat.Hom.hom
    (deloopingMap_comp_deloopingMap (Fibration.acyclicInclusion_exact N) (changeWeak_exact N)).symm)

omit [N.coarse.weq.HasTwoOutOfThreeProperty] in
/-- The original zero-to-identity component maps to the original acyclic
nullhomotopy component, with only the given chosen-zero equality inserted. -/
theorem zeroToIdentity_acyclicInclusion_app (X : AcyclicCategory N) :
    (Fibration.acyclicInclusion N).map ((zeroToIdentity (acyclicStructure N)).app X) =
      eqToHom N.zero_eq.symm ≫ (zeroToAcyclicInclusion N).app X :=
  V.isZero.eq_of_src _ _

omit [N.coarse.weq.HasTwoOutOfThreeProperty] in
/-- Its actual chosen zero is the original coarse chosen zero via N's given equality. -/
theorem acyclicInclusion_zero :
    (Fibration.acyclicInclusion N).obj (waldhausenStructure (acyclicStructure N)).zero =
      N.coarse.zero := N.zero_eq.symm

end CategoryTheory.Waldhausen.Fibration.AllWeak
