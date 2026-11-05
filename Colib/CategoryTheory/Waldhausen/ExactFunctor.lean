/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.Waldhausen.Basic

/-!
# Structural exactness for Waldhausen categories

Preservation of actual zero objects, the two specified morphism classes, and
pushouts along cofibrations. No K-theory, realization, or comparison is assumed.
Implementation provenance: adapted from `Quillen/Waldhausen/Functor.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This isolated draft has not been compiled.

-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u v' u' v'' u''

namespace CategoryTheory.Waldhausen

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]

/-- The structural properties needed to map S-constructions. -/
structure IsExact (cof weq : MorphismProperty C) (cof' weq' : MorphismProperty D)
    (F : C ⥤ D) : Prop where
  /-- Zero objects are preserved. -/
  zero {Z : C} : IsZero Z → IsZero (F.obj Z)
  /-- Cofibrations are preserved. -/
  cofibration {X Y : C} (f : X ⟶ Y) : cof f → cof' (F.map f)
  /-- Weak equivalences are preserved. -/
  weak {X Y : C} (f : X ⟶ Y) : weq f → weq' (F.map f)
  /-- Pushouts along cofibrations are preserved. -/
  pushout {A B D P : C} {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ P} {j : D ⟶ P} :
    cof i → IsPushout i f g j → IsPushout (F.map i) (F.map f) (F.map g) (F.map j)

namespace IsExact

/-- The identity functor is exact. -/
theorem id (cof weq : MorphismProperty C) : IsExact cof weq cof weq (𝟭 C) where
  zero h := h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h

/-- Exactness is stable under composition. -/
theorem comp {cof weq : MorphismProperty C} {cof' weq' : MorphismProperty D}
    {cof'' weq'' : MorphismProperty E} {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact cof weq cof' weq' F) (hG : IsExact cof' weq' cof'' weq'' G) :
    IsExact cof weq cof'' weq'' (F ⋙ G) where
  zero h := hG.zero (hF.zero h)
  cofibration f h := hG.cofibration _ (hF.cofibration f h)
  weak f h := hG.weak _ (hF.weak f h)
  pushout h hP := hG.pushout (hF.cofibration _ h) (hF.pushout h hP)

end IsExact

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0144",
  colib_ref "Waldhausen1985" "Sections 1.1-1.2, pp.321 and 327"
    "background" "Zero-object-preserving exactness and its identity and composition laws"]
  CategoryTheory.Waldhausen.IsExact
  CategoryTheory.Waldhausen.IsExact.id
  CategoryTheory.Waldhausen.IsExact.comp
