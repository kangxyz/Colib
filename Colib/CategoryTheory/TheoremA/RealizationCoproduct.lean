/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.CoproductHomotopy
public import Colib.Topology.Realization.SimplexBoundaryHEP

/-! Source: Quillen/CategoryTheory/TheoremA/RealizationCoproduct.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-! # Coproducts of actual homotopy-extension maps -/
@[expose] public section

noncomputable section

open SSet TopCat CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace CategoryTheory.TheoremA

/-- The continuous disjoint union of a family of maps. -/
def topologicalSigmaMap {ι : Type u} {A B : ι → TopCat.{u}} (i : ∀ a, A a ⟶ B a) :
    TopCat.of (Σ a, A a) ⟶ TopCat.of (Σ a, B a) :=
  TopCat.ofHom (ContinuousMap.sigmaContinuousMap fun a ↦ (i a).hom)

@[reassoc (attr := simp)]
theorem topologicalSigmaMap_ι {ι : Type u} {A B : ι → TopCat.{u}}
    (i : ∀ a, A a ⟶ B a) (a : ι) :
    TopCat.sigmaι A a ≫ topologicalSigmaMap i = i a ≫ TopCat.sigmaι B a := rfl

/-- An arbitrary disjoint union of maps with HEP has HEP. -/
theorem homotopyExtensionProperty_sigma {ι : Type u} {A B : ι → TopCat.{u}}
    (i : ∀ a, A a ⟶ B a) (hi : ∀ a, TopCat.HomotopyExtensionProperty (i a)) :
    TopCat.HomotopyExtensionProperty (topologicalSigmaMap i) := by
  intro Z f H hzero
  have hstart (a : ι) : TopCat.ι₀ ≫ (TopCat.sigmaι A a ▷ TopCat.I) ≫ H =
      i a ≫ TopCat.sigmaι B a ≫ f := by
    rw [← Category.assoc, TopCat.ι₀_comp, Category.assoc, hzero,
      ← Category.assoc, topologicalSigmaMap_ι, Category.assoc]
  choose K hK₀ hK using fun a ↦
    hi a Z (TopCat.sigmaι B a ≫ f) ((TopCat.sigmaι A a ▷ TopCat.I) ≫ H) (hstart a)
  let hc := isColimitCofanMkObjOfIsColimit (tensorRight TopCat.I) B
    (TopCat.sigmaι B) (TopCat.sigmaCofanIsColimit B)
  let L := Cofan.IsColimit.desc hc K
  have hL (a : ι) : (TopCat.sigmaι B a ▷ TopCat.I) ≫ L = K a :=
    Cofan.IsColimit.fac hc K a
  refine ⟨L, ?_, ?_⟩
  · apply (TopCat.sigmaCofanIsColimit B).hom_ext
    intro ⟨a⟩
    change TopCat.sigmaι B a ≫ TopCat.ι₀ ≫ L = TopCat.sigmaι B a ≫ f
    rw [← Category.assoc, ← TopCat.ι₀_comp, Category.assoc, hL, hK₀]
  · apply (isColimitCofanMkObjOfIsColimit (tensorRight TopCat.I) A
      (TopCat.sigmaι A) (TopCat.sigmaCofanIsColimit A)).hom_ext
    intro ⟨a⟩
    change (TopCat.sigmaι A a ▷ TopCat.I) ≫ (topologicalSigmaMap i ▷ TopCat.I) ≫ L =
      (TopCat.sigmaι A a ▷ TopCat.I) ≫ H
    rw [← Category.assoc, ← comp_whiskerRight, topologicalSigmaMap_ι,
      comp_whiskerRight, Category.assoc, hL, hK]

/-- An arbitrary family of parametrized simplex boundaries gives a genuine
cofibration after taking its actual topological disjoint union. -/
theorem homotopyExtensionProperty_sigmaSimplexBoundary {ι : Type u}
    (X : ι → TopCat.{u}) (n : ι → ℕ) :
    TopCat.HomotopyExtensionProperty
      (topologicalSigmaMap fun a ↦ TopCat.parameterizedSimplexBoundaryInclusion (X a) (n a)) :=
  homotopyExtensionProperty_sigma _ fun a ↦ TopCat.homotopyExtensionProperty_simplexBoundary (X a)
    (n a)

end CategoryTheory.TheoremA
