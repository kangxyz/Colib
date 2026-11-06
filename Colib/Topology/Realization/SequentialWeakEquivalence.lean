/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Category.TopCat.SequentialColimit.Compact
public import Colib.Topology.HELP.StrictFiniteCriterion

/-!
# Complete weak invariance of sequential closed-embedding colimits

Compact cube and full-boundary maps factor through a common actual stage.
Stage injectivity retains the exact boundary square; finite strict HELP
then produces the original colimit map's complete weak equivalence.
Only stagewise weakness, T1 separation and closed embeddings are assumed.

Implementation provenance:
`Quillen/Topology/Realization/SequentialWeakEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section

open Topology


noncomputable section
open Topology TopCat
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.SequentialColimit

/-- Objectwise complete weak equivalences of sequential closed-embedding
systems induce complete weakness on their original colimit map. -/
theorem colimitMap_isWeakHomotopyEquivalence
    {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G)
    (c : Cocone F) (hc : IsColimit c) (d : Cocone G) (hd : IsColimit d)
    [∀ n, T1Space (F.obj n)] [∀ n, T1Space (G.obj n)]
    (hF : ∀ n, IsClosedEmbedding (F.map (homOfLE (Nat.le_succ n))))
    (hG : ∀ n, IsClosedEmbedding (G.map (homOfLE (Nat.le_succ n))))
    (hη : ∀ n, IsWeakHomotopyEquivalence (η.app n).hom) :
    IsWeakHomotopyEquivalence (hc.map d η).hom := by
  apply FiniteCubeStrictHELP.isWeakHomotopyEquivalence
  intro q a b w
  let : CompactSpace (CubicalTests.boundaryPresentation.{u} q).space :=
    (CubicalTests.boundaryPresentation q).compact
  let : CompactSpace (CubicalTests.boundary.{u} q) :=
    (CubicalTests.boundaryPresentationHomeomorph q).compactSpace
  obtain ⟨m, am, ham⟩ := continuousMap_factors hc hF a
  obtain ⟨n, hmn, bn, hbn⟩ := continuousMap_factors_above hd hG b m
  let an := (F.map (homOfLE hmn)).hom.comp am
  have han : (c.ι.app n).hom.comp an = a := by
    ext x
    exact (ConcreteCategory.congr_hom (c.w (homOfLE hmn)) (am x)).trans (ham x)
  have hmap (k : ℕ) : (hc.map d η).hom.comp (c.ι.app k).hom =
      (d.ι.app k).hom.comp (η.app k).hom :=
    congrArg TopCat.Hom.hom (hc.ι_map d η k)
  have wn : (η.app n).hom.comp an = bn.comp (CubicalTests.boundaryInclusion q).hom := by
    ext x
    apply (stage_isClosedEmbedding hd hG n).injective
    exact (ContinuousMap.congr_fun (hmap n) (an x)).symm.trans
      ((congrArg (hc.map d η) (ContinuousMap.congr_fun han x)).trans
        ((ContinuousMap.congr_fun w x).trans (hbn ((CubicalTests.boundaryInclusion q) x)).symm))
  obtain ⟨cn, hcn, ⟨H⟩⟩ := (hη n).cube_strictHELP q an bn wn
  refine ⟨(c.ι.app n).hom.comp cn, ?_, ⟨(H.compContinuousMap (d.ι.app n).hom).cast ?_ ?_⟩⟩
  · rw [ContinuousMap.comp_assoc, hcn, han]
  · rw [← ContinuousMap.comp_assoc, ← hmap, ContinuousMap.comp_assoc]
  · ext x
    exact hbn x

end TopCat.SequentialColimit
