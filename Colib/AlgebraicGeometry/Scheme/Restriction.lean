/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.AlgebraicGeometry.Scheme.VectorBundle.Exact
public import Colib.AlgebraicGeometry.Scheme.Coherent.Exact
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact

/-!
# Actual open restriction of vector bundles and coherent sheaves

Both functors below lift the native `Scheme.Modules.restrictFunctor`. In particular their
underlying module objects and morphisms are definitionally the actual geometric restriction,
not a chosen pullback or an equivalent surrogate. Its exactness is the native preservation
of finite limits and colimits. Identity and composition comparisons lift the native
`restrictFunctorId` and `restrictFunctorComp`, retaining their actual components.

Implementation provenance: the categorical restriction maps used in
`Quillen/AlgebraicGeometry/Scheme/VectorBundle/Restriction.lean` and
`Quillen/AlgebraicGeometry/Scheme/Coherent/Restriction.lean` at `c561118b`, with Aglib
foundations at `2c34f185fa859e862661f939cd216b07bcccfb26`. The categories here are the
existing native `Scheme.Vect` and native `CoherentModules`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] AlgebraicGeometry.Modules.preservesFiniteLimits_restrictFunctor
attribute [local instance] AlgebraicGeometry.Modules.preservesColimits_restrictFunctor
attribute [local instance] AlgebraicGeometry.Modules.preservesZeroMorphisms_restrictFunctor

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Actual open restriction preserves the native finite local freeness predicate. -/
theorem isFiniteLocallyFree_restrictFunctor (M : X.Modules)
    (hM : SheafOfModules.IsFiniteLocallyFree.{u, u, u} M) :
    SheafOfModules.IsFiniteLocallyFree.{u, u, u} ((restrictFunctor j).obj M) :=
  (isFiniteLocallyFree_iff _).1 (((isFiniteLocallyFree_iff M).2 hM).restrict j)

/-- Coherence is preserved by actual restriction along any open immersion. -/
theorem isCoherent_restrictFunctor (M : X.Modules) (hM : M.IsCoherent) :
    ((restrictFunctor j).obj M).IsCoherent := by
  obtain ⟨hft, hker⟩ := (AlgebraicGeometry.Modules.isCoherent_iff M).1 hM
  refine (AlgebraicGeometry.Modules.isCoherent_iff _).2
    ⟨AlgebraicGeometry.Modules.isFiniteType_restrict j M hft, fun W => ?_⟩
  exact AlgebraicGeometry.Modules.kernelIsFiniteType_of_iso
    ((restrictFunctorComp W.ι j).app M)
    (AlgebraicGeometry.Modules.kernelIsFiniteType_restrict M hker (W.ι ≫ j))

/-- The lift of actual module restriction to the native vector-bundle categories. -/
def vectorBundleRestrict : X.Vect ⥤ U.Vect :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ restrictFunctor j)
    (fun M => isFiniteLocallyFree_restrictFunctor j M.obj M.property)

instance vectorBundleRestrict_additive : (vectorBundleRestrict j).Additive := by
  dsimp [vectorBundleRestrict]
  infer_instance

/-- The lift of actual module restriction to the native coherent categories. -/
def coherentRestrict : SheafOfModules.CoherentModules X.ringCatSheaf ⥤
    SheafOfModules.CoherentModules U.ringCatSheaf :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ restrictFunctor j)
    (fun M => isCoherent_restrictFunctor j M.obj M.property)

instance coherentRestrict_additive : (coherentRestrict j).Additive where
  map_add {M N f g} := by
    apply ObjectProperty.hom_ext
    exact (restrictFunctor j).map_add

@[simp]
theorem vectorBundleRestrict_obj (M : X.Vect) :
    ((vectorBundleRestrict j).obj M).obj = (restrictFunctor j).obj M.obj := rfl

@[simp]
theorem vectorBundleRestrict_map {M N : X.Vect} (f : M ⟶ N) :
    ((vectorBundleRestrict j).map f).hom = (restrictFunctor j).map f.hom := rfl

@[simp]
theorem coherentRestrict_obj (M : SheafOfModules.CoherentModules X.ringCatSheaf) :
    ((coherentRestrict j).obj M).obj = (restrictFunctor j).obj M.obj := rfl

@[simp]
theorem coherentRestrict_map {M N : SheafOfModules.CoherentModules X.ringCatSheaf}
    (f : M ⟶ N) :
    ((coherentRestrict j).map f).hom = (restrictFunctor j).map f.hom := rfl

/-- Actual open restriction of vector bundles is exact for ambient short exact sequences. -/
def vectorBundleExactRestrict :
    ExactFunctor (vectorBundleExactStructure X) (vectorBundleExactStructure U) where
  toFunctor := vectorBundleRestrict j
  map_conflation S hS := by
    exact hS.map_of_exact (restrictFunctor j)

/-- Actual open restriction of coherent module sheaves is exact. -/
def coherentRestrictionExact :
    ExactFunctor (coherentExactStructure X) (coherentExactStructure U) where
  toFunctor := coherentRestrict j
  map_conflation S hS := by
    apply (coherent_shortExact_iff_map U _).2
    exact ((coherent_shortExact_iff_map X S).1 hS).map_of_exact (restrictFunctor j)

/-- The native identity restriction isomorphism lifted to vector bundles. -/
def vectorBundleRestrictId (X : Scheme.{u}) :
    vectorBundleRestrict (𝟙 X) ≅ 𝟭 X.Vect :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((restrictFunctorId (X := X)).app M.obj)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (restrictFunctorId (X := X)).hom.naturality f.hom)

/-- The native identity restriction isomorphism lifted to coherent sheaves. -/
def coherentRestrictId (X : Scheme.{u}) :
    coherentRestrict (𝟙 X) ≅ 𝟭 (SheafOfModules.CoherentModules X.ringCatSheaf) :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((restrictFunctorId (X := X)).app M.obj)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (restrictFunctorId (X := X)).hom.naturality f.hom)

@[simp]
theorem vectorBundleRestrictId_hom_app (X : Scheme.{u}) (M : X.Vect) :
    ((vectorBundleRestrictId X).hom.app M).hom =
      (restrictFunctorId (X := X)).hom.app M.obj := rfl

@[simp]
theorem vectorBundleRestrictId_inv_app (X : Scheme.{u}) (M : X.Vect) :
    ((vectorBundleRestrictId X).inv.app M).hom =
      (restrictFunctorId (X := X)).inv.app M.obj := rfl

@[simp]
theorem coherentRestrictId_hom_app (X : Scheme.{u})
    (M : SheafOfModules.CoherentModules X.ringCatSheaf) :
    ((coherentRestrictId X).hom.app M).hom =
      (restrictFunctorId (X := X)).hom.app M.obj := rfl

@[simp]
theorem coherentRestrictId_inv_app (X : Scheme.{u})
    (M : SheafOfModules.CoherentModules X.ringCatSheaf) :
    ((coherentRestrictId X).inv.app M).hom =
      (restrictFunctorId (X := X)).inv.app M.obj := rfl

/-- The native composition comparison lifted to actual vector-bundle restriction. -/
def vectorBundleRestrictComp {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    vectorBundleRestrict (i ≫ j) ≅ vectorBundleRestrict j ⋙ vectorBundleRestrict i :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((restrictFunctorComp i j).app M.obj)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (restrictFunctorComp i j).hom.naturality f.hom)

/-- The native composition comparison lifted to actual coherent restriction. -/
def coherentRestrictComp {V U X : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ X)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    coherentRestrict (i ≫ j) ≅ coherentRestrict j ⋙ coherentRestrict i :=
  NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _ ((restrictFunctorComp i j).app M.obj)) (by
      intro M N f
      apply ObjectProperty.hom_ext
      exact (restrictFunctorComp i j).hom.naturality f.hom)

@[simp]
theorem vectorBundleRestrictComp_hom_app {V U X : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] (M : X.Vect) :
    ((vectorBundleRestrictComp i j).hom.app M).hom =
      (restrictFunctorComp i j).hom.app M.obj := rfl

@[simp]
theorem vectorBundleRestrictComp_inv_app {V U X : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j] (M : X.Vect) :
    ((vectorBundleRestrictComp i j).inv.app M).hom =
      (restrictFunctorComp i j).inv.app M.obj := rfl

@[simp]
theorem coherentRestrictComp_hom_app {V U X : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (M : SheafOfModules.CoherentModules X.ringCatSheaf) :
    ((coherentRestrictComp i j).hom.app M).hom =
      (restrictFunctorComp i j).hom.app M.obj := rfl

@[simp]
theorem coherentRestrictComp_inv_app {V U X : Scheme.{u}}
    (i : V ⟶ U) (j : U ⟶ X) [IsOpenImmersion i] [IsOpenImmersion j]
    (M : SheafOfModules.CoherentModules X.ringCatSheaf) :
    ((coherentRestrictComp i j).inv.app M).hom =
      (restrictFunctorComp i j).inv.app M.obj := rfl

end AlgebraicGeometry.Scheme.Modules
