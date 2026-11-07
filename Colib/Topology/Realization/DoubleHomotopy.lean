/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.HomotopySquare

/-! The actual double-cylinder coordinate swap and its realization. A genuine simplicial
    two-time square gives the complete realized interchange equation. -/
/-! Implementation source: `Quillen/Topology/Realization/DoubleHomotopy.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual cylinder isomorphisms,
simultaneous interval coordinates and both projection maps are unchanged. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace SSet

/-- Swap the two simplicial interval coordinates of the double cylinder. -/
def simplicialCylinderSwap (X : SSet.{u}) : (X ⊗ Δ[1]) ⊗ Δ[1] ⟶ (X ⊗ Δ[1]) ⊗ Δ[1] :=
  lift (lift (fst (X ⊗ Δ[1]) Δ[1] ≫ fst X Δ[1]) (snd (X ⊗ Δ[1]) Δ[1]))
    (fst (X ⊗ Δ[1]) Δ[1] ≫ snd X Δ[1])

/-- Realize the double simplicial cylinder as the double topological cylinder. -/
def realizationDoubleCylinderIso (X : SSet.{u}) :
    |(X ⊗ Δ[1]) ⊗ Δ[1]| ≅ (|X| ⊗ TopCat.I) ⊗ TopCat.I :=
  realizationCylinderIso (X ⊗ Δ[1]) ≪≫
    (MonoidalCategory.tensorRight TopCat.I).mapIso (realizationCylinderIso X)

/-- Swap the two topological interval coordinates of the double cylinder. -/
def topologicalCylinderSwap (X : TopCat.{u}) : (X ⊗ TopCat.I) ⊗ TopCat.I ⟶
    (X ⊗ TopCat.I) ⊗ TopCat.I :=
  lift (lift (fst (X ⊗ TopCat.I) TopCat.I ≫ fst X TopCat.I)
    (snd (X ⊗ TopCat.I) TopCat.I)) (fst (X ⊗ TopCat.I) TopCat.I ≫ snd X TopCat.I)

@[simp] lemma topologicalCylinderSwap_apply (X : TopCat.{u})
    (x : X) (s t : TopCat.I.{u}) :
    topologicalCylinderSwap X ((x,s),t) = ((x,t),s) := rfl

lemma realizationDoubleCylinderSwap (X : SSet.{u}) :
    SSet.toTop.map (simplicialCylinderSwap X) ≫ (realizationDoubleCylinderIso X).hom =
      (realizationDoubleCylinderIso X).hom ≫ topologicalCylinderSwap |X| := by
  apply CartesianMonoidalCategory.hom_ext
  · apply CartesianMonoidalCategory.hom_ext
    · simp [realizationDoubleCylinderIso, realizationCylinderIso, realizationCylinderComparison,
        simplicialCylinderSwap, topologicalCylinderSwap, ← Functor.map_comp]
    · simp [realizationDoubleCylinderIso, realizationCylinderIso, realizationCylinderComparison,
        simplicialCylinderSwap, topologicalCylinderSwap, ← Functor.map_comp]
      simp only [← Category.assoc, ← Functor.map_comp]
      simp
  · simp [realizationDoubleCylinderIso, realizationCylinderIso, realizationCylinderComparison,
      simplicialCylinderSwap, topologicalCylinderSwap, ← Functor.map_comp]

lemma realizationDoubleCylinderSwap_inv (X : SSet.{u})
    (x : |X|) (s t : TopCat.I.{u}) :
    SSet.toTop.map (simplicialCylinderSwap X)
      ((realizationCylinderIso (X ⊗ Δ[1])).inv ((realizationCylinderIso X).inv (x,s),t)) =
    (realizationCylinderIso (X ⊗ Δ[1])).inv ((realizationCylinderIso X).inv (x,t),s) := by
  apply (TopCat.homeoOfIso (realizationDoubleCylinderIso X)).injective
  have h := congrArg (fun f ↦ f ((realizationDoubleCylinderIso X).inv ((x,s),t)))
    (realizationDoubleCylinderSwap X)
  change (realizationDoubleCylinderIso X).hom
    (SSet.toTop.map (simplicialCylinderSwap X)
      ((realizationDoubleCylinderIso X).inv ((x,s),t))) =
    (realizationDoubleCylinderIso X).hom ((realizationDoubleCylinderIso X).inv ((x,t),s))
  simpa only [TopCat.comp_app, Iso.inv_hom_id_apply, topologicalCylinderSwap_apply] using h

/-- A genuine commuting square of two simplicial time parameters retains the
entire two-time realized homotopy, in the original coordinates. -/
theorem realizationSimplicialHomotopy_interchange
    {X Y X' Y' : SSet.{u}}
    {f g : X ⟶ Y} {k l : X ⟶ X'} {f' g' : X' ⟶ Y'} {k' l' : Y ⟶ Y'}
    (H : SSet.Homotopy f g) (K : SSet.Homotopy k l)
    (H' : SSet.Homotopy f' g') (K' : SSet.Homotopy k' l')
    (hs : K.h ▷ Δ[1] ≫ H'.h =
      simplicialCylinderSwap X ≫ H.h ▷ Δ[1] ≫ K'.h)
    (s t : unitInterval) (x : |X|) :
    realizationSimplicialHomotopy H' (s, realizationSimplicialHomotopy K (t,x)) =
      realizationSimplicialHomotopy K' (t, realizationSimplicialHomotopy H (s,x)) := by
  let p := (realizationCylinderIso (X ⊗ Δ[1])).inv
    ((realizationCylinderIso X).inv (x,ULift.up t),ULift.up s)
  have hK := ConcreteCategory.congr_hom (realizationCylinderIso_inv_naturality K.h)
    ((realizationCylinderIso X).inv (x,ULift.up t),ULift.up s)
  have hH := ConcreteCategory.congr_hom (realizationCylinderIso_inv_naturality H.h)
    ((realizationCylinderIso X).inv (x,ULift.up s),ULift.up t)
  change SSet.toTop.map (K.h ▷ Δ[1]) p =
    (realizationCylinderIso X').inv
      (SSet.toTop.map K.h ((realizationCylinderIso X).inv (x,ULift.up t)),ULift.up s) at hK
  change SSet.toTop.map (H.h ▷ Δ[1])
      ((realizationCylinderIso (X ⊗ Δ[1])).inv
        ((realizationCylinderIso X).inv (x,ULift.up s),ULift.up t)) =
    (realizationCylinderIso Y).inv
      (SSet.toTop.map H.h ((realizationCylinderIso X).inv (x,ULift.up s)),ULift.up t) at hH
  change SSet.toTop.map H'.h ((realizationCylinderIso X').inv
      (SSet.toTop.map K.h ((realizationCylinderIso X).inv (x,ULift.up t)),ULift.up s)) =
    SSet.toTop.map K'.h ((realizationCylinderIso Y).inv
      (SSet.toTop.map H.h ((realizationCylinderIso X).inv (x,ULift.up s)),ULift.up t))
  rw [← hK, ← hH, ← realizationDoubleCylinderSwap_inv X x (ULift.up t) (ULift.up s)]
  change (SSet.toTop.map (K.h ▷ Δ[1]) ≫ SSet.toTop.map H'.h) p =
    (SSet.toTop.map (simplicialCylinderSwap X) ≫
      SSet.toTop.map (H.h ▷ Δ[1]) ≫ SSet.toTop.map K'.h) p
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hs]

end SSet
