/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal
/-!
Adapted from `Quillen/Aglib/CategoryTheory/Grothendieck/Terminal.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original categorical maps.


# A terminal fiber of the actual Grothendieck construction

A terminal object in the indexing category gives an explicit projection to its
fiber. The fiber inclusion is a strict right inverse. There is a genuine natural
transformation from the identity to projection followed by inclusion, and every
other fiber projects by its original transition functor. These are the finite
categorical telescope retraction data, without a topological model comparison.
-/

@[expose] public section

open CategoryTheory Limits
noncomputable section
universe u
namespace CategoryTheory.Grothendieck.Terminal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {J : Type u} [SmallCategory J] (F : J ⥤ Cat.{u, u})
  {t : J} (ht : IsTerminal t)

/-- The original transition functor to the terminal fiber. -/
def fiberProjection (j : J) : F.obj j ⥤ F.obj t := (F.map (ht.from j)).toFunctor

theorem fiberProjection_eq {j k : J} (a : j ⟶ k) :
    fiberProjection F ht j = (F.map a).toFunctor ⋙ fiberProjection F ht k := by
  change (F.map (ht.from j)).toFunctor = (F.map a ≫ F.map (ht.from k)).toFunctor
  rw [← F.map_comp, ht.hom_ext (ht.from j) (a ≫ ht.from k)]

/-- The coherent comparison between terminal transitions. -/
def fiberComparison {j k : J} (a : j ⟶ k) :
    fiberProjection F ht j ⟶ (F.map a).toFunctor ⋙ fiberProjection F ht k :=
  eqToHom (fiberProjection_eq F ht a)

theorem fiberComparison_id (j : J) :
    fiberComparison F ht (𝟙 j) = eqToHom (by simp only [F.map_id]; rfl) := rfl

theorem fiberComparison_comp (j k l : J) (a : j ⟶ k) (b : k ⟶ l) :
    fiberComparison F ht (a ≫ b) =
      fiberComparison F ht a ≫ Functor.whiskerLeft (F.map a).toFunctor
        (fiberComparison F ht b) ≫ eqToHom (by simp only [F.map_comp]; rfl) := by
  ext x
  simp [fiberComparison]

/-- Project the Grothendieck construction by its original terminal transitions. -/
def projection : Grothendieck F ⥤ F.obj t where
  obj X := (fiberProjection F ht X.base).obj X.fiber
  map {X Y} f := (fiberComparison F ht f.base).app X.fiber ≫
    (fiberProjection F ht Y.base).map f.fiber
  map_id X := by simp [fiberComparison_id, eqToHom_map]
  map_comp f g := by simp [fiberComparison_comp, eqToHom_map]

/-- Projection restricted to a fiber is canonically the original transition. -/
def inclusionProjectionIso (j : J) :
    Grothendieck.ι F j ⋙ projection F ht ≅ (F.map (ht.from j)).toFunctor :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun f ↦ by
    simp [projection, Grothendieck.ι, fiberComparison_id, eqToHom_map, fiberProjection])

/-- The base terminal arrow gives the explicit deformation natural transformation. -/
def projectionInclusionUnit : 𝟭 (Grothendieck F) ⟶ projection F ht ⋙ Grothendieck.ι F t where
  app X := { base := ht.from X.base, fiber := 𝟙 _ }
  naturality {X Y} f := by
    apply Grothendieck.ext _ _ (ht.hom_ext _ _)
    simp [projection, Grothendieck.ι, fiberComparison,
      fiberProjection, Grothendieck.comp_fiber]


theorem inclusion_projection (j : J) :
    Grothendieck.ι F j ⋙ projection F ht = (F.map (ht.from j)).toFunctor := by
  refine Functor.ext (F := Grothendieck.ι F j ⋙ projection F ht)
    (G := (F.map (ht.from j)).toFunctor) (fun _ ↦ rfl) ?_
  intro X Y f
  have h := (inclusionProjectionIso F ht j).hom.naturality f
  change (Grothendieck.ι F j ⋙ projection F ht).map f ≫
      𝟙 ((F.map (ht.from j)).toFunctor.obj Y) =
    𝟙 ((F.map (ht.from j)).toFunctor.obj X) ≫ (F.map (ht.from j)).toFunctor.map f at h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))

theorem terminal_inclusion_projection :
    Grothendieck.ι F t ⋙ projection F ht = 𝟭 (F.obj t) := by
  rw [inclusion_projection, ht.hom_ext (ht.from t) (𝟙 t), F.map_id]
  rfl

/-- The terminal fiber inclusion is a strict section of the projection. -/
def counitIso : Grothendieck.ι F t ⋙ projection F ht ≅ 𝟭 (F.obj t) :=
  eqToIso (terminal_inclusion_projection F ht)

end CategoryTheory.Grothendieck.Terminal
