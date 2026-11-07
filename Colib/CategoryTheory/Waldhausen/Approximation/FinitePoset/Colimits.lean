/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Limits.FinitePosetColimits
public import Colib.KTheory.Waldhausen.Map
public import Colib.CategoryTheory.Waldhausen.SMap
public import Colib.CategoryTheory.Waldhausen.ExactFunctor
public import Mathlib.Order.UpperLower.Basic

/-!
# Preserved colimits of finite-poset diagrams

Lower-ideal restrictions, cocones and their gluing describe preserved latching colimits,
    including the exact and Waldhausen functor specializations.

Implementation provenance: `Quillen/Waldhausen/Approximation/FinitePoset/Colimits.lean` at Quillen
commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe w w' z u v u' v'

namespace CategoryTheory.Limits.FinitePosetLatching
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  (G : J ⥤ C)

variable {G} {A B : Set J}
  (cA : Cocone (restriction G A)) (cB : Cocone (restriction G B))
  (cI : Cocone (restriction G (A ∩ B)))
  (i : cI.pt ⟶ cA.pt) (j : cI.pt ⟶ cB.pt)
  (hi : ∀ x : (A ∩ B : Set J), cI.ι.app x ≫ i = cA.ι.app ⟨x.val, x.property.1⟩)
  (hj : ∀ x : (A ∩ B : Set J), cI.ι.app x ≫ j = cB.ι.app ⟨x.val, x.property.2⟩)
  {P : C} (a : cA.pt ⟶ P) (b : cB.pt ⟶ P) (sq : IsPushout i j a b)

variable (hcover : ∀ x : J, x ∈ A ∨ x ∈ B)
variable (hA : IsLowerSet A) (hB : IsLowerSet B)

section Mapping
variable {D : Type u'} [Category.{v'} D] (F : C ⥤ D)

/-- Waldhausen exactness supplies preservation of the attaching pushout from
its genuine cofibration leg; no extra global colimit-preservation assumption
is imposed on the original exact functor. -/
def exactMappedGluedCoconeIsColimit
    (W : CategoryTheory.Waldhausen.Structure C) (V : CategoryTheory.Waldhausen.Structure D)
    (hF : CategoryTheory.Waldhausen.IsExact W.cof W.weq V.cof V.weq F)
    (hcof : W.cof i ∨ W.cof j)
    (hcA : IsColimit (F.mapCocone cA)) (hcB : IsColimit (F.mapCocone cB))
    (hcI : IsColimit (F.mapCocone cI)) :
    IsColimit (F.mapCocone (gluedCocone cA cB cI i j hi hj a b sq hcover hA hB)) :=
  mappedGluedCoconeIsColimit cA cB cI i j hi hj a b sq hcover hA hB F
    hcA hcB hcI (hcof.elim (fun h ↦ hF.pushout h sq)
      (fun h ↦ (hF.pushout h sq.flip).flip))

end Mapping

section Existence
variable {D : Type u'} [Category.{v'} D] (F : C ⥤ D)
  (W : CategoryTheory.Waldhausen.Structure C) (V : CategoryTheory.Waldhausen.Structure D)
  (hF : CategoryTheory.Waldhausen.IsExact W.cof W.weq V.cof V.weq F)
  (hcA : IsColimit cA) (hcB : IsColimit cB) (hcI : IsColimit cI)

include hF hcover hA hB hcA hcB in
/-- An actual cofibrant lower-ideal attachment constructs both the source
colimit and its preserved image from the three already-constructed lower
colimits. This is a finite-induction step, not an assumed coning endpoint. -/
theorem exists_preserved_gluedColimit
    (hcof : W.cof (intersectionToLeft cA cI hcI) ∨
      W.cof (intersectionToRight cB cI hcI))
    (hFA : IsColimit (F.mapCocone cA)) (hFB : IsColimit (F.mapCocone cB))
    (hFI : IsColimit (F.mapCocone cI)) :
    ∃ c : Cocone G, Nonempty (IsColimit c) ∧ Nonempty (IsColimit (F.mapCocone c)) := by
  let i := intersectionToLeft cA cI hcI
  let j := intersectionToRight cB cI hcI
  have hi (x : (A ∩ B : Set J)) :
      cI.ι.app x ≫ i = cA.ι.app ⟨x.val, x.property.1⟩ := hcI.fac _ x
  have hj (x : (A ∩ B : Set J)) :
      cI.ι.app x ≫ j = cB.ι.app ⟨x.val, x.property.2⟩ := hcI.fac _ x
  have hp : ∃ (P : C) (a : cA.pt ⟶ P) (b : cB.pt ⟶ P), IsPushout i j a b := by
    rcases hcof with h | h
    · exact W.pushout_exists i j h
    · obtain ⟨P, b, a, hp⟩ := W.pushout_exists j i h
      exact ⟨P, a, b, hp.flip⟩
  obtain ⟨P, a, b, hp⟩ := hp
  refine ⟨gluedCocone cA cB cI i j hi hj a b hp hcover hA hB,
    ⟨gluedCoconeIsColimit cA cB cI i j hi hj a b hp hcover hA hB hcA hcB hcI⟩, ?_⟩
  exact ⟨exactMappedGluedCoconeIsColimit cA cB cI i j hi hj a b hp hcover hA hB
    F W V hF hcof hFA hFB hFI⟩
end Existence

end CategoryTheory.Limits.FinitePosetLatching

end
