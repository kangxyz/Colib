/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectWaldhausen
public import Colib.Topology.Sheaves.Cohomology.PerfectComplexes.Restriction
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Exact restriction of native perfect complexes

The ordinary scheme restriction functor restricts the full subcategory cut out by Stacks
perfectness. Its action on complexes and maps remains the original degreewise restriction.
It preserves the inherited Waldhausen structure: actual zero objects, monomorphisms,
quasi-isomorphisms and displayed pushouts along monomorphisms.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable (X : Scheme.{u}) (U : X.Opens)

/-- Ordinary scheme restriction preserves the native perfect-complex predicate. -/
@[stacks 08CM "Restriction of the native perfect-complex predicate to an open subscheme"]
theorem Complex.isPerfectComplex_restrictFunctor (K : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K) :
    RingedSpace.IsPerfectComplex (X := U.toScheme.toRingedSpace)
      (((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  have : (show StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace ⥤
      StrictlyPerfect.OXMod.{u, u, u} (X.toRingedSpace.restrict U.isOpenEmbedding) from
        restrictFunctor U.ι).PreservesZeroMorphisms :=
    ⟨fun _ _ => by ext _ _; rfl⟩
  exact (hK.restrict U).of_iso
    ((NatIso.mapHomologicalComplex (RingedSpace.restrictModulesIsoRestrictFunctor X U)
      (ComplexShape.up ℤ)).app K)

/-- The ordinary degreewise restriction on the full subcategories of native perfect complexes. -/
def perfectComplexesRestrictFunctor :
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) ⥤
      ObjectProperty.FullSubcategory
        (RingedSpace.IsPerfectComplex (X := U.toScheme.toRingedSpace)) :=
  ObjectProperty.lift (RingedSpace.IsPerfectComplex (X := U.toScheme.toRingedSpace))
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) ⋙
      (restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => Complex.isPerfectComplex_restrictFunctor X U K.obj K.property)

/-- The underlying complex is its actual scheme restriction. -/
@[simp]
theorem perfectComplexesRestrictFunctor_obj
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    ((perfectComplexesRestrictFunctor X U).obj K).obj =
      ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj := rfl

/-- The underlying map is its actual degreewise restriction. -/
@[simp]
theorem perfectComplexesRestrictFunctor_map
    {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (f : K ⟶ L) :
    ((perfectComplexesRestrictFunctor X U).map f).hom =
      ((restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Ordinary restriction is exact for the native perfect-complex Waldhausen structures. -/
@[colib_tag "COL-0229",
  colib_ref "Waldhausen1985" "Sections 1.1-1.2, pp.321 and 327"
  "background" "Exactness of ordinary open restriction with ambient Mono and QuasiIso"]
theorem perfectComplexesRestrictFunctor_isExact :
    Waldhausen.IsExact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (RingedSpace.perfectComplexesWaldhausen U.toScheme.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen U.toScheme.toRingedSpace).weq
      (perfectComplexesRestrictFunctor X U) := by
  let F := (restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)
  let P : ObjectProperty (CochainComplex X.Modules ℤ) :=
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
  let Q : ObjectProperty (CochainComplex U.toScheme.Modules ℤ) :=
    RingedSpace.IsPerfectComplex (X := U.toScheme.toRingedSpace)
  have : PreservesFiniteLimits (show X.Modules ⥤ U.toScheme.Modules from
      RingedSpace.restrictModules.{u, u} X.toRingedSpace U) :=
    RingedSpace.restrictModules_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (restrictFunctor U.ι) :=
    preservesFiniteLimits_of_natIso (RingedSpace.restrictModulesIsoRestrictFunctor X U)
  refine { zero := ?_, cofibration := ?_, weak := ?_, pushout := ?_ }
  · intro Z hZ
    apply IsZero.of_full_of_faithful_of_isZero Q.ι
    exact F.map_isZero
      ((Waldhausen.CofibrationClosedSubcategory.inclusion_exact
        (Waldhausen.complexes X.Modules) P
        (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace)).zero hZ)
  · intro K L f hf
    change Mono (F.map f.hom)
    have : Mono (C := CochainComplex X.Modules ℤ) f.hom := hf
    infer_instance
  · intro K L f hf
    change QuasiIso (F.map f.hom)
    have : QuasiIso (C := X.Modules) f.hom := hf
    infer_instance
  · intro A B D T i f g j hi h
    apply IsPushout.of_map_of_faithful Q.ι
    exact (Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes X.Modules) P
      (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace) hi h).map F

end AlgebraicGeometry.Scheme.Modules
