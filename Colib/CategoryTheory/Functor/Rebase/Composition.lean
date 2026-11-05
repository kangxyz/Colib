/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.Functor.Rebase

/-!
# Composition of functors rebased at chosen objects

The comparison from rebasing a composite to composing rebased functors has a
specified component at the chosen base object: it is exactly `eqToHom` of the
proved equality of base objects. An arbitrary natural isomorphism would not
supply this equation.

## Implementation provenance

Extracted from `Quillen/KTheory/Map/CoherenceData.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors, specified
base isomorphisms, object equalities and component equations are retained.
Source and target share the source's object universe `u` and morphism universe `v`.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory

namespace CategoryTheory

section RebaseComposition

variable {C D T : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} T]

/-- The base component of the normalization is precisely the supplied
isomorphism, with the object equality made explicit. -/
theorem rebaseFunctorIso_hom_base (F : C ⥤ D) (c : C) (d : D) (e : F.obj c ≅ d) :
    (rebaseFunctorIso F c d e).hom.app c =
      e.hom ≫ eqToHom (rebaseFunctor_obj_base F c d e).symm := by
  classical
  dsimp only [rebaseFunctorIso, NatIso.ofComponents, rebaseObjIso]
  simp
  rfl

/-- The composite of two rebased functors sends the chosen base object to the
chosen final base object. -/
theorem rebaseFunctor_comp_obj_base (F : C ⥤ D) (G : D ⥤ T)
    (c : C) (d : D) (t : T) (e : F.obj c ≅ d) (f : G.obj d ≅ t) :
    ((rebaseFunctor F c d e) ⋙ rebaseFunctor G d t f).obj c = t :=
  (congrArg (rebaseFunctor G d t f).obj (rebaseFunctor_obj_base F c d e)).trans
    (rebaseFunctor_obj_base G d t f)

/-- Comparison from the original composite to the composite of its two
normalized functors. -/
def rebaseFunctorCompRightIso (F : C ⥤ D) (G : D ⥤ T)
    (c : C) (d : D) (t : T) (e : F.obj c ≅ d) (f : G.obj d ≅ t) :
    F ⋙ G ≅ (rebaseFunctor F c d e) ⋙ rebaseFunctor G d t f :=
  Functor.isoWhiskerRight (rebaseFunctorIso F c d e) G ≪≫
    Functor.isoWhiskerLeft (rebaseFunctor F c d e) (rebaseFunctorIso G d t f)

/-- At the base object, the comparison to the composite of normalized
functors is exactly the composite of the two specified base isomorphisms. -/
theorem rebaseFunctorCompRightIso_hom_base (F : C ⥤ D) (G : D ⥤ T)
    (c : C) (d : D) (t : T) (e : F.obj c ≅ d) (f : G.obj d ≅ t) :
    (rebaseFunctorCompRightIso F G c d t e f).hom.app c ≫
      eqToHom (rebaseFunctor_comp_obj_base F G c d t e f) = G.map e.hom ≫ f.hom := by
  have hn := (rebaseFunctorIso G d t f).hom.naturality
    (eqToHom (rebaseFunctor_obj_base F c d e))
  dsimp only [rebaseFunctorCompRightIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rw [rebaseFunctorIso_hom_base, G.map_comp]
  have hb : eqToHom (rebaseFunctor_comp_obj_base F G c d t e f) =
      (rebaseFunctor G d t f).map (eqToHom (rebaseFunctor_obj_base F c d e)) ≫
        eqToHom (rebaseFunctor_obj_base G d t f) := by
    simp only [eqToHom_map, eqToHom_trans]
  rw [hb]
  simp only [Category.assoc]
  rw [← Category.assoc ((rebaseFunctorIso G d t f).hom.app _), ← hn,
    rebaseFunctorIso_hom_base]
  simp [eqToHom_map]

/-- The natural comparison between normalizing a composite and composing the
two normalized functors. -/
def rebaseFunctorCompIso (F : C ⥤ D) (G : D ⥤ T)
    (c : C) (d : D) (t : T) (e : F.obj c ≅ d) (f : G.obj d ≅ t) :
    rebaseFunctor (F ⋙ G) c t (G.mapIso e ≪≫ f) ≅
      (rebaseFunctor F c d e) ⋙ rebaseFunctor G d t f :=
  (rebaseFunctorIso (F ⋙ G) c t (G.mapIso e ≪≫ f)).symm ≪≫
    rebaseFunctorCompRightIso F G c d t e f

/-- The two normalized composites have the same base object. -/
theorem rebaseFunctorCompIso_obj_base (F : C ⥤ D) (G : D ⥤ T)
    (c : C) (d : D) (t : T) (e : F.obj c ≅ d) (f : G.obj d ≅ t) :
    (rebaseFunctor (F ⋙ G) c t (G.mapIso e ≪≫ f)).obj c =
      ((rebaseFunctor F c d e) ⋙ rebaseFunctor G d t f).obj c :=
  (rebaseFunctor_obj_base (F ⋙ G) c t (G.mapIso e ≪≫ f)).trans
    (rebaseFunctor_comp_obj_base F G c d t e f).symm

/-- The natural comparison fixes the base object: its component is the
identity after the displayed object equality. This is the exact input needed
by the based nerve-cylinder theorem. -/
theorem rebaseFunctorCompIso_hom_base (F : C ⥤ D) (G : D ⥤ T)
    (c : C) (d : D) (t : T) (e : F.obj c ≅ d) (f : G.obj d ≅ t) :
    (rebaseFunctorCompIso F G c d t e f).hom.app c =
      eqToHom (rebaseFunctorCompIso_obj_base F G c d t e f) := by
  apply (cancel_mono (eqToHom (rebaseFunctor_comp_obj_base F G c d t e f))).mp
  dsimp only [rebaseFunctorCompIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, rebaseFunctorCompRightIso_hom_base]
  have hh : (rebaseFunctorIso (F ⋙ G) c t (G.mapIso e ≪≫ f)).hom.app c ≫
      eqToHom (rebaseFunctor_obj_base (F ⋙ G) c t (G.mapIso e ≪≫ f)) =
      G.map e.hom ≫ f.hom := by
    rw [rebaseFunctorIso_hom_base]
    simp
  rw [← hh]
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp, eqToHom_trans]

/-- Rebasing is unchanged by equal functors and the corresponding equal
base isomorphisms. -/
theorem rebaseFunctor_congr {F G : C ⥤ D} (h : F = G) (c : C) (d : D)
    (e : F.obj c ≅ d) (f : G.obj c ≅ d) (he : HEq e f) :
    rebaseFunctor F c d e = rebaseFunctor G c d f := by
  subst G
  obtain rfl := eq_of_heq he
  rfl

/-- Transporting the source functor of a based comparison preserves its
identity base component. -/
theorem eqToIso_trans_hom_base {F G H : C ⥤ D} (h : F = G) (e : G ≅ H)
    (c : C) (hc : G.obj c = H.obj c) (he : e.hom.app c = eqToHom hc) :
    (eqToIso h ≪≫ e).hom.app c =
      eqToHom ((congrArg (fun K : C ⥤ D => K.obj c) h).trans hc) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_app, he, eqToHom_trans]

end RebaseComposition

end CategoryTheory

attribute [colib_tag "COL-0056",
  colib_ref "WeibelKBook" "IV, Homotopy-theoretic properties 3.2" "background"
    "Natural-transformation background, not a source for this explicit rebasing comparison"]
  CategoryTheory.rebaseFunctorCompIso
  CategoryTheory.rebaseFunctorCompIso_hom_base
