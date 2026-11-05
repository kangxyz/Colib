/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.PrismGluing
public import Colib.Topology.Realization.SimplicialColimits
public import Colib.Topology.Realization.Cylinder

/-! # Realization preserves the simplicial interval cylinder -/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/Realization/CylinderIso.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The canonical maps, equality hypotheses,
endpoint orientation, independent universes and `ULift` direction are retained.
The representable comparison uses the established finite-simplex coordinate
adapter at the pinned Mathlib boundary. The extension to arbitrary simplicial
sets uses their actual colimit of representables, not general preservation of
products by geometric realization.
-/
@[expose] public section

noncomputable section

open Convexity CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial Topology unitInterval

universe u

namespace SSet

/-- The canonical cylinder comparison is a homeomorphism on representable simplicial sets. -/
instance realizationCylinderComparison_standard_isIso (n : ℕ) :
    IsIso (realizationCylinderComparison (Δ[n] : SSet.{u})) := by
  let e : |(Δ[n] ⊗ Δ[1] : SSet.{u})| ≃ₜ (|(Δ[n] : SSet.{u})| × TopCat.I.{u}) :=
    (realizationPrismHomeomorph n).trans
      ((FiniteSimplexAdapter.toTopHomeomorph ⦋n⦌).symm.prodCongr TopCat.I.homeomorph.symm)
  have heq : realizationCylinderComparison (Δ[n] : SSet.{u}) =
      (TopCat.isoOfHomeo e).hom := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    apply Prod.ext
    · exact ((FiniteSimplexAdapter.toTopHomeomorph ⦋n⦌).symm_apply_apply _).symm
    · exact (FiniteSimplexAdapter.realization_interval_compat
        (SSet.toTop.map (snd Δ[n] Δ[1]) x)).symm
  rw [heq]
  infer_instance

/-- The canonical cylinder comparison as a natural transformation. -/
def realizationCylinderComparisonNatTrans :
    tensorRight (Δ[1] : SSet.{u}) ⋙ SSet.toTop ⟶ SSet.toTop ⋙ tensorRight TopCat.I where
  app := realizationCylinderComparison
  naturality _ _ f := realizationCylinderComparison_naturality f

/-- Geometric realization takes the simplicial cylinder to the actual topological cylinder. -/
instance realizationCylinderComparison_isIso (X : SSet.{u}) :
    IsIso (realizationCylinderComparison X) := by
  let K := Presheaf.functorToRepresentables X
  have : ∀ j, IsIso ((Functor.whiskerLeft K realizationCylinderComparisonNatTrans).app j) := by
    intro j
    change IsIso (realizationCylinderComparison (SSet.stdSimplex.obj j.unop.1.unop))
    cases j.unop.1.unop using SimplexCategory.rec with
    | _ n => exact realizationCylinderComparison_standard_isIso n
  have := NatIso.isIso_of_isIso_app (Functor.whiskerLeft K realizationCylinderComparisonNatTrans)
  have : PreservesColimit K (tensorRight (Δ[1] : SSet.{u})) := by infer_instance
  have : PreservesColimit (K ⋙ tensorRight (Δ[1] : SSet.{u})) SSet.toTop := by infer_instance
  have : PreservesColimit K SSet.toTop := by infer_instance
  have : PreservesColimit (K ⋙ SSet.toTop) (tensorRight TopCat.I.{u}) := by infer_instance
  exact isIso_app_coconePt_of_preservesColimit K realizationCylinderComparisonNatTrans
    (Presheaf.coconeOfRepresentable X) (Presheaf.colimitOfRepresentable X)

/-- The natural cylinder isomorphism in `TopCat`. -/
def realizationCylinderIso (X : SSet.{u}) : |X ⊗ Δ[1]| ≅ |X| ⊗ TopCat.I :=
  asIso (realizationCylinderComparison X)

end SSet

attribute [colib_tag "COL-0068",
  colib_ref "WeibelKBook" "IV, Characterization 3.1(6)" "background"
    "Compactly generated product background; here only the ordinary topological interval factor",
  colib_ref "HatcherAT" "Section 2.1, proof of Theorem 2.10, prism subdivision, page 112"
    "ingredient" "Finite prism input; extension to arbitrary simplicial sets uses colimits here"]
  SSet.realizationCylinderComparison_isIso
  SSet.realizationCylinderIso
  SSet.realizationCylinderComparisonNatTrans
