/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.Waldhausen.ExactFunctor
public import Colib.CategoryTheory.Waldhausen.SConstruction

/-!
# Exact functors act on the actual diagonal S-construction

Maps are literal postcomposition of quotient diagrams. The simplicial-map
interface retains the source's same-universe restriction.
Implementation provenance: adapted from `Quillen/Waldhausen/Functor.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
This isolated draft has not been compiled.

-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe v u v' u'

namespace CategoryTheory.Waldhausen

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable {cof weq : MorphismProperty C} {cof' weq' : MorphismProperty D}
    {F : C ⥤ D} (hF : IsExact cof weq cof' weq' F)

include hF in
/-- Exact functors take S-simplices to S-simplices. -/
theorem IsSimplex.postcomp {n : SimplexCategory} {A : Grid n ⥤ C}
    (hA : IsSimplex cof weq A) : IsSimplex cof' weq' (A ⋙ F) where
  zero t i := hF.zero (hA.zero t i)
  cofibration t i j k hij hjk := hF.cofibration _ (hA.cofibration t i j k hij hjk)
  quotient t i j k hij hjk := hF.pushout (hA.cofibration t i j k hij hjk)
    (hA.quotient t i j k hij hjk)
  weak s t i j hst hij := hF.weak _ (hA.weak s t i j hst hij)

section SameUniverses

variable {D : Type u} [Category.{v} D] {cof' weq' : MorphismProperty D}
    {F : C ⥤ D} (hF : IsExact cof weq cof' weq' F)

/-- The actual map of diagonal S-constructions. -/
def sSetMap : sSet cof weq ⟶ sSet cof' weq' where
  app _ := ↾fun A ↦ ⟨A.1 ⋙ F, A.2.postcomp hF⟩
  naturality _ _ _ := by ext A; rfl

/-- The original S-map preserves the identity functor exactly. -/
@[simp] theorem sSetMap_id.{u₁, v₁} {C : Type u₁} [Category.{v₁} C]
    (V : Structure C) :
    sSetMap (IsExact.id V.cof V.weq) = 𝟙 (sSet V.cof V.weq) := by
  ext n A
  rfl

/-- Postcomposition on diagrams preserves composition of exact functors. -/
theorem sSetMap_comp {E : Type u} [Category.{v} E]
    {cof'' weq'' : MorphismProperty E} {G : D ⥤ E}
    (hG : IsExact cof' weq' cof'' weq'' G) :
    sSetMap (hF.comp hG) = sSetMap hF ≫ sSetMap hG := by
  ext n A
  rfl

end SameUniverses

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0146",
  colib_ref "Waldhausen1985" "Section 1.3, p.330"
    "background" "Exact postcomposition on the unnormalized model, not homotopy functoriality"]
  CategoryTheory.Waldhausen.IsSimplex.postcomp
  CategoryTheory.Waldhausen.sSetMap
  CategoryTheory.Waldhausen.sSetMap_id
  CategoryTheory.Waldhausen.sSetMap_comp
