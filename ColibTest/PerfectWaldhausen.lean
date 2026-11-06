module

import Colib.AlgebraicGeometry.Modules.PerfectWaldhausen

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StrictlyPerfect
open scoped ZeroObject

universe u

variable (X : RingedSpace.{u, u})

-- The category is the upstream predicate's full subcategory, with no second model.
example : (RingedSpace.perfectComplexesWaldhausen X).zero.obj = 0 := rfl

example : IsZero (RingedSpace.perfectComplexesWaldhausen X).zero :=
  (RingedSpace.perfectComplexesWaldhausen X).isZero

example {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X))} (f : K ⟶ L) :
    (RingedSpace.perfectComplexesWaldhausen X).cof f ↔ Mono f.hom := Iff.rfl

example {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X))} (f : K ⟶ L) :
    (RingedSpace.perfectComplexesWaldhausen X).weq f ↔ QuasiIso f.hom := Iff.rfl

example {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X))} (f : K ⟶ L) :
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X))).map f = f.hom := rfl

-- The ambient cone-to-quotient argument keeps the actual short exact sequence.
example {S : ShortComplex (CochainComplex (OXMod.{u, u, u} X) ℤ)} (hS : S.ShortExact)
    (h₁ : RingedSpace.IsPerfectComplex S.X₁) (h₂ : RingedSpace.IsPerfectComplex S.X₂) :
    RingedSpace.IsPerfectComplex S.X₃ :=
  RingedSpace.isPerfectComplex_X₃_of_shortExact hS h₁ h₂

example {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X))}
    (f : K ⟶ L) [Mono f.hom] : RingedSpace.IsPerfectComplex (cokernel f.hom) :=
  RingedSpace.isPerfectComplex_X₃_of_shortExact
    (show (ShortComplex.mk f.hom (cokernel.π f.hom) (cokernel.condition f.hom)).ShortExact
      from { exact := ShortComplex.cokernelSequence_exact f.hom }) K.property L.property

-- Closure and inclusion preserve every displayed pushout, not only a selected one.
example {A B D Q : CochainComplex (OXMod.{u, u, u} X) ℤ}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ Q} {j : D ⟶ Q} [Mono i]
    (h : IsPushout i f g j) (hA : RingedSpace.IsPerfectComplex A)
    (hB : RingedSpace.IsPerfectComplex B) (hD : RingedSpace.IsPerfectComplex D) :
    RingedSpace.IsPerfectComplex Q :=
  RingedSpace.isPerfectComplex_of_isPushout h hA hB hD

example {A B D Q : (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X)))}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ Q} {j : D ⟶ Q}
    (hi : (RingedSpace.perfectComplexesWaldhausen X).cof i) (h : IsPushout i f g j) :
    IsPushout i.hom f.hom g.hom j.hom :=
  Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
    (Waldhausen.complexes (OXMod.{u, u, u} X)) (RingedSpace.IsPerfectComplex (X := X))
    (RingedSpace.perfectComplexes_cofibrationClosed X) hi h

example : Waldhausen.IsExact
    (RingedSpace.perfectComplexesWaldhausen X).cof
    (RingedSpace.perfectComplexesWaldhausen X).weq
    (Waldhausen.complexes (OXMod.{u, u, u} X)).cof
    (Waldhausen.complexes (OXMod.{u, u, u} X)).weq
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X))) :=
  Waldhausen.CofibrationClosedSubcategory.inclusion_exact
    (Waldhausen.complexes (OXMod.{u, u, u} X)) (RingedSpace.IsPerfectComplex (X := X))
    (RingedSpace.perfectComplexes_cofibrationClosed X)

-- Schemes use precisely this ringed-space construction, without an adapter.
example (Y : Scheme.{u}) : Waldhausen.Structure
    (ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace))) :=
  RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace
