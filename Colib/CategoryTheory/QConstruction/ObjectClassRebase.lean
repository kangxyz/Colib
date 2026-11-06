/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.QConstruction.ObjectClassFunctoriality
public import Colib.CategoryTheory.Functor.Rebase.Composition
public import Mathlib.CategoryTheory.Conj

/-!
# Q-object classes under rebasing

Adapted from `Quillen/KTheory/GrothendieckComparison/Naturality.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original maps, specified basepoint equalities and multiplication order are retained.
-/

@[expose] public noncomputable section

universe u v
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Naturally isomorphic Q-groupoid functors give conjugate object-loop classes. -/
lemma qObjectClass_natIso {D : Type*} [Groupoid D]
    {F G : E.QCategory ⥤ D} (η : F ≅ G) (X : C) :
    E.qObjectClass G X = (η.app E.qZero).conj (E.qObjectClass F X) := by
  simp only [qObjectClass, Iso.conj_apply, Iso.app_hom, Iso.app_inv]
  apply (cancel_mono (G.map (E.fromZero (QConstruction.of E.deflation E.inflation X)))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← η.hom.naturality (E.fromZero (QConstruction.of E.deflation E.inflation X))]
  simp only [IsIso.inv_hom_id_assoc]
  exact (NatIso.naturality_1 η (E.fromZeroTotal (QConstruction.of E.deflation E.inflation X))).symm

/-- Rebasing a Q-functor replaces transport along a categorical isomorphism
by transport along the resulting literal basepoint equality. -/
lemma rebase_qObjectClass {D : Type u} {T : Type*} [Category.{max u v} D] [Groupoid T]
    (F : E.QCategory ⥤ D) (d : D) (e : F.obj E.qZero ≅ d)
    (H : D ⥤ T) (X : C) :
    (H.mapIso (eqToIso (rebaseFunctor_obj_base F E.qZero d e))).conj
      (E.qObjectClass (rebaseFunctor F E.qZero d e ⋙ H) X) =
    (H.mapIso e).conj (E.qObjectClass (F ⋙ H) X) := by
  rw [E.qObjectClass_natIso (Functor.isoWhiskerRight (rebaseFunctorIso F E.qZero d e) H) X]
  erw [← Iso.trans_conj]
  congr 1
  apply congrArg Iso.conj
  apply Iso.ext
  change H.map ((rebaseFunctorIso F E.qZero d e).hom.app E.qZero) ≫
      H.map (eqToHom (rebaseFunctor_obj_base F E.qZero d e)) = H.map e.hom
  rw [← H.map_comp, rebaseFunctorIso_hom_base]
  simp

end CategoryTheory.ExactCategory.ExactStructure
