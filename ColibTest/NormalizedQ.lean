/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.CategoryTheory.ExactCategory.Functor.NormalizedQ

/-!
# Normalized Q-functor composition regression tests

These checks identify the actual categorical comparison and its base component.
They do not assert homotopy invariance or composition of Quillen K-maps.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

universe v u

noncomputable section

section Rebase

variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]
  (F : C ⥤ D) (G : D ⥤ T) (c : C) (d : D) (t : T)
  (e : F.obj c ≅ d) (f : G.obj d ≅ t)

example : (rebaseFunctorIso F c d e).hom.app c =
    e.hom ≫ eqToHom (rebaseFunctor_obj_base F c d e).symm :=
  rebaseFunctorIso_hom_base F c d e

example : rebaseFunctor (F ⋙ G) c t (G.mapIso e ≪≫ f) ≅
    (rebaseFunctor F c d e) ⋙ rebaseFunctor G d t f :=
  rebaseFunctorCompIso F G c d t e f

example : (rebaseFunctorCompIso F G c d t e f).hom.app c =
    eqToHom (rebaseFunctorCompIso_obj_base F G c d t e f) :=
  rebaseFunctorCompIso_hom_base F G c d t e f

example : (rebaseFunctorCompRightIso F G c d t e f).hom.app c ≫
    eqToHom (rebaseFunctor_comp_obj_base F G c d t e f) = G.map e.hom ≫ f.hom :=
  rebaseFunctorCompRightIso_hom_base F G c d t e f

example : ((rebaseFunctor F c d e) ⋙ rebaseFunctor G d t f).obj c = t :=
  rebaseFunctor_comp_obj_base F G c d t e f

end Rebase

section Exact

variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]
  [Preadditive C] [Preadditive D] [Preadditive T]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D] [HasFiniteBiproducts T]
  {E : ExactStructure C} {E' : ExactStructure D} {E'' : ExactStructure T}
  (F : ExactFunctor E E') (G : ExactFunctor E' E'')

example : (F.comp G).toFunctor.mapZeroObject =
    G.toFunctor.mapIso F.toFunctor.mapZeroObject ≪≫ G.toFunctor.mapZeroObject := by
  apply Iso.ext
  apply Subsingleton.elim

example : E''.qIsoOfIso (F.comp G).toFunctor.mapZeroObject =
    G.mapQ.mapIso (E'.qIsoOfIso F.toFunctor.mapZeroObject) ≪≫
      E''.qIsoOfIso G.toFunctor.mapZeroObject := F.comp_qZeroIso G

example : F.normalizedQ = rebaseFunctor F.mapQ
    (QConstruction.of E.deflation E.inflation (0 : C))
    (QConstruction.of E'.deflation E'.inflation (0 : D))
    (E'.qIsoOfIso F.toFunctor.mapZeroObject) := rfl

example : F.normalizedQ.obj (QConstruction.of E.deflation E.inflation (0 : C)) =
    QConstruction.of E'.deflation E'.inflation (0 : D) :=
  rebaseFunctor_obj_base F.mapQ _ _ _

example : (F.comp G).normalizedQ ≅ F.normalizedQ ⋙ G.normalizedQ := F.normalizedQCompIso G

example : (F.normalizedQCompIso G).hom.app
    (QConstruction.of E.deflation E.inflation (0 : C)) =
      eqToHom (F.normalizedQCompIso_obj_base G) := F.normalizedQCompIso_hom_base G

example : (F.comp G).normalizedQ =
    rebaseFunctor (F.mapQ ⋙ G.mapQ) (QConstruction.of E.deflation E.inflation (0 : C))
      (QConstruction.of E''.deflation E''.inflation (0 : T))
      (G.mapQ.mapIso (E'.qIsoOfIso F.toFunctor.mapZeroObject) ≪≫
        E''.qIsoOfIso G.toFunctor.mapZeroObject) := F.normalizedQ_comp_eq G

end Exact
