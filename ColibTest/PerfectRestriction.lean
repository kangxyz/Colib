module

import Colib.KTheory.Waldhausen.PerfectRestriction

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

variable (X : Scheme.{u}) (U : X.Opens)

example (K : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K) :
    RingedSpace.IsPerfectComplex (X := U.toScheme.toRingedSpace)
      (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  Scheme.Modules.Complex.isPerfectComplex_restrictFunctor X U K hK

example (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    (n : ℤ) :
    (((Scheme.Modules.perfectComplexesRestrictFunctor X U).obj K).obj).X n =
      (Scheme.Modules.restrictFunctor U.ι).obj (K.obj.X n) := rfl

example {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (f : K ⟶ L) (n : ℤ) :
    (((Scheme.Modules.perfectComplexesRestrictFunctor X U).map f).hom).f n =
      (Scheme.Modules.restrictFunctor U.ι).map (f.hom.f n) := rfl

example {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (f : K ⟶ L) (hf : QuasiIso f.hom) :
    QuasiIso (((Scheme.Modules.perfectComplexesRestrictFunctor X U).map f).hom) :=
  (Scheme.Modules.perfectComplexesRestrictFunctor_isExact X U).weak f hf

example {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (f : K ⟶ L) [Mono f.hom] :
    Mono (((Scheme.Modules.perfectComplexesRestrictFunctor X U).map f).hom) :=
  (Scheme.Modules.perfectComplexesRestrictFunctor_isExact X U).cofibration f
    (show Mono f.hom from inferInstance)

example (Z : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
    (hZ : IsZero Z) : IsZero ((Scheme.Modules.perfectComplexesRestrictFunctor X U).obj Z) :=
  (Scheme.Modules.perfectComplexesRestrictFunctor_isExact X U).zero hZ

example {A B D T :
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ T} {j : D ⟶ T} [Mono i.hom]
    (h : IsPushout i f g j) :
    IsPushout ((Scheme.Modules.perfectComplexesRestrictFunctor X U).map i)
      ((Scheme.Modules.perfectComplexesRestrictFunctor X U).map f)
      ((Scheme.Modules.perfectComplexesRestrictFunctor X U).map g)
      ((Scheme.Modules.perfectComplexesRestrictFunctor X U).map j) :=
  (Scheme.Modules.perfectComplexesRestrictFunctor_isExact X U).pushout
    (show Mono i.hom from inferInstance) h

example (n : ℕ) : Scheme.Modules.perfectComplexesRestrictKMap X U n =
    Waldhausen.KMap (Scheme.Modules.perfectComplexesRestrictFunctor_isExact X U) n := rfl

#print axioms AlgebraicGeometry.RingedSpace.IsPerfectComplex.restrict
#print axioms AlgebraicGeometry.Scheme.Modules.perfectComplexesRestrictFunctor_isExact
#print axioms AlgebraicGeometry.Scheme.Modules.perfectComplexesRestrictKMap
