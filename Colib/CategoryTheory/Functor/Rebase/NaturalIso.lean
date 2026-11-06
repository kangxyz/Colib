/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Functor.Rebase.Composition

/-! # Natural isomorphisms of rebased functors

Adapted from `Quillen/KTheory/Map/NaturalIso.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original functors,
canonical zero isomorphisms and based homotopies.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe v u v₁ v₂ u₁ u₂

namespace CategoryTheory

section RebaseNaturalIso
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {F G : C ⥤ D}

/-- A natural isomorphism compares two independently normalized functors. -/
def rebaseFunctorNatIso (α : F ≅ G) (c : C) (d : D)
    (e : F.obj c ≅ d) (f : G.obj c ≅ d) :
    rebaseFunctor F c d e ≅ rebaseFunctor G c d f :=
  (rebaseFunctorIso F c d e).symm ≪≫ α ≪≫ rebaseFunctorIso G c d f

/-- The source and target of the normalized comparison agree at the base. -/
theorem rebaseFunctorNatIso_obj_base (c : C) (d : D)
    (e : F.obj c ≅ d) (f : G.obj c ≅ d) :
    (rebaseFunctor F c d e).obj c = (rebaseFunctor G c d f).obj c :=
  (rebaseFunctor_obj_base F c d e).trans (rebaseFunctor_obj_base G c d f).symm

/-- A comparison compatible with the supplied base isomorphisms has identity
component after normalization, with all object transports explicit. -/
theorem rebaseFunctorNatIso_hom_base (α : F ≅ G) (c : C) (d : D)
    (e : F.obj c ≅ d) (f : G.obj c ≅ d) (h : α.app c ≪≫ f = e) :
    (rebaseFunctorNatIso α c d e f).hom.app c =
      eqToHom (rebaseFunctorNatIso_obj_base c d e f) := by
  apply (cancel_mono (eqToHom (rebaseFunctor_obj_base G c d f))).mp
  have hh : α.hom.app c ≫ f.hom = e.hom := congrArg Iso.hom h
  have he : e.hom = (rebaseFunctorIso F c d e).hom.app c ≫
      eqToHom (rebaseFunctor_obj_base F c d e) := by
    rw [rebaseFunctorIso_hom_base]
    simp
  dsimp only [rebaseFunctorNatIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [rebaseFunctorIso_hom_base]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  rw [hh, he]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end RebaseNaturalIso

/-- Replacing an object by its equal image does not change the functor. -/
theorem rebaseFunctor_eq_of_eq {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d)
    (h : F.obj c = d) (he : e = eqToIso h) : rebaseFunctor F c d e = F := by
  subst d
  rw [he]
  exact rebaseFunctor_refl F c


end CategoryTheory
