/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.QConstruction.Core
import Colib.CategoryTheory.ExactCategory.Functor.QIsomorphisms

/-!
# Q-isomorphisms and core equivalence regression tests

The tests retain independent source and target object/hom universes and only
exact-structure hypotheses. No balancedness or ambient abelian assumption occurs.
The equivalence is checked against its actual identity-left-leg span map.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

universe v v' u u'

noncomputable section

section Core

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

example {X Y : C} (e : X ≅ Y) : E.inflation e.hom := E.inflation_of_iso e

example {X Y : C} (e : X ≅ Y) : E.deflation e.hom := E.deflation_of_iso e

example {X Y : C} (f : X ⟶ Y) [Mono f] (hf : E.deflation f) : IsIso f :=
  E.isIso_of_deflation_of_mono f hf

example {X Y : C} (e : X ≅ Y) :
    (E.qIsoOfIso e).hom = QConstruction.mkHom E.deflation E.inflation
      { apex := X
        l := 𝟙 X
        r := e.hom
        wl := E.deflation_id X
        wr := E.inflation_of_iso e } := rfl

example (X : C) :
    E.qIsoOfIso (Iso.refl X) = Iso.refl (QConstruction.of E.deflation E.inflation X) := by
  simp

example {X Y Z : C} (e : X ≅ Y) (f : Y ≅ Z) :
    E.qIsoOfIso (e ≪≫ f) = E.qIsoOfIso e ≪≫ E.qIsoOfIso f := by
  simp

example {X Y : C} (s : Span E.deflation E.inflation X Y)
    [IsIso (QConstruction.mkHom E.deflation E.inflation s)] : IsIso s.l ∧ IsIso s.r :=
  E.qSpan_isIso_legs s

example {X Y : C} (s : Span E.deflation E.inflation X Y) [IsIso s.l] [IsIso s.r] :
    QConstruction.mkHom E.deflation E.inflation s =
      (E.qIsoOfIso ((asIso s.l).symm ≪≫ asIso s.r)).hom := E.qSpan_eq_qIsoOfIso s

example {X Y : C} : Function.Bijective (E.qIsoOfIso : (X ≅ Y) → _) :=
  E.qIsoOfIso_bijective

example : E.qCoreFunctor.Faithful := inferInstance

example : E.qCoreFunctor.Full := inferInstance

example : E.qCoreFunctor.EssSurj := inferInstance

example : E.qCoreFunctor.IsEquivalence := inferInstance

example (X : Core C) :
    (E.qCoreFunctor.obj X).of = QConstruction.of E.deflation E.inflation X.of := rfl

example {X Y : Core C} (f : X ⟶ Y) :
    (E.qCoreFunctor.map f).iso = E.qIsoOfIso f.iso := rfl

example {X Y : Core C} (f : X ⟶ Y) :
    (E.qCoreEquivalence.functor.map f).iso = E.qIsoOfIso f.iso :=
  E.qCoreEquivalence_map f

end Core

section ExactFunctor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')

example {X Y : C} (e : X ≅ Y) :
    F.mapQ.mapIso (E.qIsoOfIso e) = E'.qIsoOfIso (F.toFunctor.mapIso e) :=
  F.mapQ_qIsoOfIso e

example {X Y : C} (e : X ≅ Y) :
    F.mapQ.map (E.qIsoOfIso e).hom = (E'.qIsoOfIso (F.toFunctor.mapIso e)).hom :=
  congrArg Iso.hom (F.mapQ_qIsoOfIso e)

end ExactFunctor
