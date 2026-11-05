/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# Homology of arbitrary coproducts of module complexes

Exactness of module coproducts and the already proved exact-colimit comparison
give the canonical homology isomorphism. Its inverse retains the original
homology maps of the coproduct inclusions.

Adapted from Quillen.Aglib.Algebra.Category.ModuleCat.CoproductHomology at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Exact-colimit preservation is supplied
by the pinned Stacks API; the comparisons use Mathlib coproduct maps.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits
universe u v w
namespace ModuleCat

variable (R : Type v) [Ring R] (ι : Type u) {α : Type w} (c : ComplexShape α) (n : α)

/-- Homology of module complexes preserves arbitrary coproducts of the module universe. -/
theorem homologyFunctor_preservesCoproducts :
    PreservesColimitsOfShape (Discrete ι)
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c n) := by
  have := ab5.{u} R
  have : AB4 (ModuleCat.{u} R) := AB4.of_AB5 _
  exact Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor c n

/-- Canonical decomposition of the homology of an actual coproduct of complexes. -/
def coproductHomologyIso (K : ι → HomologicalComplex (ModuleCat.{u} R) c) :
    (∐ K).homology n ≅ ∐ fun i ↦ (K i).homology n := by
  let := homologyFunctor_preservesCoproducts R ι c n
  exact PreservesCoproduct.iso (HomologicalComplex.homologyFunctor _ c n) K

/-- The inverse is the actual coproduct comparison for the homology functor. -/
@[simp]
theorem coproductHomologyIso_inv (K : ι → HomologicalComplex (ModuleCat.{u} R) c) :
    (coproductHomologyIso R ι c n K).inv =
      sigmaComparison (HomologicalComplex.homologyFunctor _ c n) K := rfl

/-- Each original summand enters by the homology map of its original inclusion. -/
@[reassoc]
theorem coproductHomologyIso_ι_inv (K : ι → HomologicalComplex (ModuleCat.{u} R) c) (i : ι) :
    Sigma.ι (fun j ↦ (K j).homology n) i ≫ (coproductHomologyIso R ι c n K).inv =
      HomologicalComplex.homologyMap (Sigma.ι K i) n := by
  rw [coproductHomologyIso_inv]
  exact ι_comp_sigmaComparison (HomologicalComplex.homologyFunctor _ c n) K i

/-- The original coproduct homology comparison is natural in every summand map. -/
@[reassoc]
theorem coproductHomologyIso_naturality
    {K L : ι → HomologicalComplex (ModuleCat.{u} R) c} (f : ∀ i, K i ⟶ L i) :
    Limits.Sigma.map (fun i ↦ HomologicalComplex.homologyMap (f i) n) ≫
        (coproductHomologyIso R ι c n L).inv =
      (coproductHomologyIso R ι c n K).inv ≫
        HomologicalComplex.homologyMap (Limits.Sigma.map f) n := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c n
  change Limits.Sigma.map (fun i ↦ H.map (f i)) ≫ sigmaComparison H L =
    sigmaComparison H K ≫ H.map (Limits.Sigma.map f)
  apply Sigma.hom_ext
  intro i
  simp only [Sigma.ι_map_assoc, ι_comp_sigmaComparison_assoc,
    ι_comp_sigmaComparison]
  rw [← Functor.map_comp, ← Functor.map_comp, Sigma.ι_map]

/-- Arbitrary coproducts preserve quasi-isomorphisms of actual module chain maps. -/
theorem quasiIso_sigma_map {K L : ι → HomologicalComplex (ModuleCat.{u} R) c}
    (f : ∀ i, K i ⟶ L i) [∀ i, QuasiIso (f i)] : QuasiIso (Limits.Sigma.map f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have : ∀ i, IsIso (HomologicalComplex.homologyMap (f i) n) := fun _ ↦ inferInstance
  have := (Limits.Sigma.mapIso (fun i ↦ asIso (HomologicalComplex.homologyMap (f i) n))).isIso_hom
  exact IsIso.of_isIso_fac_left (coproductHomologyIso_naturality R ι c n f).symm

end ModuleCat

attribute [colib_tag "COL-0148",
  stacks 04B0 "Exact direct sums as an ingredient for canonical homology comparisons"]
  ModuleCat.homologyFunctor_preservesCoproducts
  ModuleCat.coproductHomologyIso
  ModuleCat.coproductHomologyIso_inv
  ModuleCat.coproductHomologyIso_ι_inv
  ModuleCat.coproductHomologyIso_naturality
  ModuleCat.quasiIso_sigma_map
