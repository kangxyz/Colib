/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Products.Basic

/-! # Limits in binary product categories

Adapted from the product-category portion of
`Quillen/Aglib/CategoryTheory/ExactCategory/Product.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The native categories, projections,
cones, cocones and independent universes are retained.
-/
@[expose] public noncomputable section

open CategoryTheory.Limits
universe v₁ v₂ u₁ u₂ w w'

namespace CategoryTheory.Prod

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- Pair cones over the two projections of one diagram. -/
def pairCone {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    (c : Cone (F ⋙ fst C D)) (d : Cone (F ⋙ snd C D)) : Cone F where
  pt := (c.pt, d.pt)
  π := { app := fun j => (c.π.app j, d.π.app j)
         naturality := fun i j f => by
           exact _root_.Prod.ext (by simpa using (c.w f).symm)
             (by simpa using (d.w f).symm) }

/-- Pair cocones over the two projections of one diagram. -/
def pairCocone {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    (c : Cocone (F ⋙ fst C D)) (d : Cocone (F ⋙ snd C D)) : Cocone F where
  pt := (c.pt, d.pt)
  ι := { app := fun j => (c.ι.app j, d.ι.app j)
         naturality := fun i j f => by
           exact _root_.Prod.ext (by simpa using c.w f) (by simpa using d.w f) }

/-- A cone in a product is limiting when both projections are limiting. -/
def isLimitOfProjections {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    {c : Cone F} (hc : IsLimit ((fst C D).mapCone c))
    (hd : IsLimit ((snd C D).mapCone c)) : IsLimit c where
  lift s := (hc.lift ((fst C D).mapCone s), hd.lift ((snd C D).mapCone s))
  fac s j := _root_.Prod.ext (hc.fac ((fst C D).mapCone s) j) (hd.fac ((snd C D).mapCone s) j)
  uniq s m hm := _root_.Prod.ext
    (hc.uniq ((fst C D).mapCone s) m.1 (fun j => congrArg _root_.Prod.fst (hm j)))
    (hd.uniq ((snd C D).mapCone s) m.2 (fun j => congrArg _root_.Prod.snd (hm j)))

/-- A cocone in a product is colimiting when both projections are colimiting. -/
def isColimitOfProjections {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    {c : Cocone F} (hc : IsColimit ((fst C D).mapCocone c))
    (hd : IsColimit ((snd C D).mapCocone c)) : IsColimit c where
  desc s := (hc.desc ((fst C D).mapCocone s), hd.desc ((snd C D).mapCocone s))
  fac s j := _root_.Prod.ext (hc.fac ((fst C D).mapCocone s) j)
    (hd.fac ((snd C D).mapCocone s) j)
  uniq s m hm := _root_.Prod.ext
    (hc.uniq ((fst C D).mapCocone s) m.1 (fun j => congrArg _root_.Prod.fst (hm j)))
    (hd.uniq ((snd C D).mapCocone s) m.2 (fun j => congrArg _root_.Prod.snd (hm j)))

instance hasLimit {J : Type w} [Category.{w'} J] (F : J ⥤ C × D)
    [HasLimit (F ⋙ fst C D)] [HasLimit (F ⋙ snd C D)] : HasLimit F :=
  ⟨⟨pairCone (limit.cone _) (limit.cone _),
    isLimitOfProjections (limit.isLimit _) (limit.isLimit _)⟩⟩

instance hasColimit {J : Type w} [Category.{w'} J] (F : J ⥤ C × D)
    [HasColimit (F ⋙ fst C D)] [HasColimit (F ⋙ snd C D)] : HasColimit F :=
  ⟨⟨pairCocone (colimit.cocone _) (colimit.cocone _),
    isColimitOfProjections (colimit.isColimit _) (colimit.isColimit _)⟩⟩

instance hasLimitsOfShape {J : Type w} [Category.{w'} J]
    [HasLimitsOfShape J C] [HasLimitsOfShape J D] : HasLimitsOfShape J (C × D) where
  has_limit _ := inferInstance

instance hasColimitsOfShape {J : Type w} [Category.{w'} J]
    [HasColimitsOfShape J C] [HasColimitsOfShape J D] : HasColimitsOfShape J (C × D) where
  has_colimit _ := inferInstance

/-- First projection preserves a displayed limit. -/
def isLimitFst {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    {c : Cone F} (h : IsLimit c) : IsLimit ((fst C D).mapCone c) where
  lift s := (h.lift (pairCone s ((snd C D).mapCone c))).1
  fac s j := congrArg _root_.Prod.fst (h.fac (pairCone s ((snd C D).mapCone c)) j)
  uniq s m hm := congrArg _root_.Prod.fst (h.uniq
    (pairCone s ((snd C D).mapCone c)) (m, 𝟙 c.pt.2)
    (fun j => _root_.Prod.ext (hm j) (Category.id_comp _)))

/-- Second projection preserves a displayed limit. -/
def isLimitSnd {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    {c : Cone F} (h : IsLimit c) : IsLimit ((snd C D).mapCone c) where
  lift s := (h.lift (pairCone ((fst C D).mapCone c) s)).2
  fac s j := congrArg _root_.Prod.snd (h.fac (pairCone ((fst C D).mapCone c) s) j)
  uniq s m hm := congrArg _root_.Prod.snd (h.uniq
    (pairCone ((fst C D).mapCone c) s) (𝟙 c.pt.1, m)
    (fun j => _root_.Prod.ext (Category.id_comp _) (hm j)))

/-- First projection preserves a displayed colimit. -/
def isColimitFst {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    {c : Cocone F} (h : IsColimit c) : IsColimit ((fst C D).mapCocone c) where
  desc s := (h.desc (pairCocone s ((snd C D).mapCocone c))).1
  fac s j := congrArg _root_.Prod.fst (h.fac (pairCocone s ((snd C D).mapCocone c)) j)
  uniq s m hm := congrArg _root_.Prod.fst (h.uniq
    (pairCocone s ((snd C D).mapCocone c)) (m, 𝟙 c.pt.2)
    (fun j => _root_.Prod.ext (hm j) (Category.comp_id _)))

/-- Second projection preserves a displayed colimit. -/
def isColimitSnd {J : Type w} [Category.{w'} J] {F : J ⥤ C × D}
    {c : Cocone F} (h : IsColimit c) : IsColimit ((snd C D).mapCocone c) where
  desc s := (h.desc (pairCocone ((fst C D).mapCocone c) s)).2
  fac s j := congrArg _root_.Prod.snd (h.fac (pairCocone ((fst C D).mapCocone c) s) j)
  uniq s m hm := congrArg _root_.Prod.snd (h.uniq
    (pairCocone ((fst C D).mapCocone c) s) (𝟙 c.pt.1, m)
    (fun j => _root_.Prod.ext (Category.comp_id _) (hm j)))

instance fst_preservesLimit {J : Type w} [Category.{w'} J] (F : J ⥤ C × D) :
    PreservesLimit F (fst C D) where
  preserves h := ⟨isLimitFst h⟩

instance snd_preservesLimit {J : Type w} [Category.{w'} J] (F : J ⥤ C × D) :
    PreservesLimit F (snd C D) where
  preserves h := ⟨isLimitSnd h⟩

instance fst_preservesColimit {J : Type w} [Category.{w'} J] (F : J ⥤ C × D) :
    PreservesColimit F (fst C D) where
  preserves h := ⟨isColimitFst h⟩

instance snd_preservesColimit {J : Type w} [Category.{w'} J] (F : J ⥤ C × D) :
    PreservesColimit F (snd C D) where
  preserves h := ⟨isColimitSnd h⟩

end CategoryTheory.Prod
