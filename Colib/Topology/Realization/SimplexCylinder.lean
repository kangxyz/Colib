/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.ProductSimplex
public import Colib.Topology.Realization.HomotopySquare

/-!
# Realization interchange for a simplex and an independent interval

The actual product-simplex and cylinder homeomorphisms preserve the coordinate swap. A proved
simplicial interchange square therefore retains its independent realized simplex and interval
coordinates; no arbitrary product-of-quotient assertion is used.
-/
/-! Implementation provenance: `Quillen/Topology/Realization/SimplexCylinder.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original product comparisons,
actual coordinate swap, and independent realized simplex and interval parameters are retained. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u

namespace SSet

/-- Swap a simplicial interval and the independent simplex parameter. -/
def simplicialSimplexCylinderSwap (X : SSet.{u}) (k : ℕ) :
    (X ⊗ Δ[1]) ⊗ Δ[k] ⟶ (X ⊗ Δ[k]) ⊗ Δ[1] :=
  lift (lift (fst (X ⊗ Δ[1]) Δ[k] ≫ fst X Δ[1]) (snd (X ⊗ Δ[1]) Δ[k]))
    (fst (X ⊗ Δ[1]) Δ[k] ≫ snd X Δ[1])

/-- The actual interval-then-simplex realization comparison. -/
def realizationCylinderSimplexIso (X : SSet.{u}) (k : ℕ) :
    |(X ⊗ Δ[1]) ⊗ Δ[k]| ≅ (|X| ⊗ TopCat.I) ⊗ |(Δ[k] : SSet.{u})| :=
  realizationProductSimplexIso (X ⊗ Δ[1]) k ≪≫
    (MonoidalCategory.tensorRight |(Δ[k] : SSet.{u})|).mapIso (realizationCylinderIso X)

/-- The actual simplex-then-interval realization comparison. -/
def realizationSimplexCylinderIso (X : SSet.{u}) (k : ℕ) :
    |(X ⊗ Δ[k]) ⊗ Δ[1]| ≅ (|X| ⊗ |(Δ[k] : SSet.{u})|) ⊗ TopCat.I :=
  realizationCylinderIso (X ⊗ Δ[k]) ≪≫
    (MonoidalCategory.tensorRight TopCat.I).mapIso (realizationProductSimplexIso X k)

/-- Swap the actual topological interval and simplex coordinates. -/
def topologicalSimplexCylinderSwap (X : TopCat.{u}) (k : ℕ) :
    (X ⊗ TopCat.I) ⊗ |(Δ[k] : SSet.{u})| ⟶ (X ⊗ |(Δ[k] : SSet.{u})|) ⊗ TopCat.I :=
  lift (lift (fst (X ⊗ TopCat.I) |(Δ[k] : SSet.{u})| ≫ fst X TopCat.I)
    (snd (X ⊗ TopCat.I) |(Δ[k] : SSet.{u})|))
    (fst (X ⊗ TopCat.I) |(Δ[k] : SSet.{u})| ≫ snd X TopCat.I)

@[simp]
lemma topologicalSimplexCylinderSwap_apply (X : TopCat.{u}) (k : ℕ)
    (x : X) (t : TopCat.I.{u}) (z : |(Δ[k] : SSet.{u})|) :
    topologicalSimplexCylinderSwap X k ((x, t), z) = ((x, z), t) := rfl

/-- Realization carries the genuine mixed-coordinate swap to the literal topological swap. -/
theorem realizationSimplexCylinderSwap (X : SSet.{u}) (k : ℕ) :
    SSet.toTop.map (simplicialSimplexCylinderSwap X k) ≫
        (realizationSimplexCylinderIso X k).hom =
      (realizationCylinderSimplexIso X k).hom ≫ topologicalSimplexCylinderSwap |X| k := by
  apply CartesianMonoidalCategory.hom_ext
  · apply CartesianMonoidalCategory.hom_ext
    · simp [realizationSimplexCylinderIso, realizationCylinderSimplexIso,
        realizationCylinderIso, realizationCylinderComparison, simplicialSimplexCylinderSwap,
        topologicalSimplexCylinderSwap, ← Functor.map_comp]
    · simp [realizationSimplexCylinderIso, realizationCylinderSimplexIso,
        realizationCylinderIso, realizationCylinderComparison, simplicialSimplexCylinderSwap,
        topologicalSimplexCylinderSwap, ← Functor.map_comp]
  · simp [realizationSimplexCylinderIso, realizationCylinderSimplexIso,
      realizationCylinderIso, realizationCylinderComparison, simplicialSimplexCylinderSwap,
      topologicalSimplexCylinderSwap, ← Functor.map_comp]

/-- The actual inverse comparisons preserve every mixed pair of coordinates. -/
theorem realizationSimplexCylinderSwap_inv (X : SSet.{u}) (k : ℕ)
    (x : |X|) (t : TopCat.I.{u}) (z : |(Δ[k] : SSet.{u})|) :
    SSet.toTop.map (simplicialSimplexCylinderSwap X k)
      ((realizationProductSimplexIso (X ⊗ Δ[1]) k).inv
        ((realizationCylinderIso X).inv (x, t), z)) =
      (realizationCylinderIso (X ⊗ Δ[k])).inv
        ((realizationProductSimplexIso X k).inv (x, z), t) := by
  apply (TopCat.homeoOfIso (realizationSimplexCylinderIso X k)).injective
  have h := congrArg (fun f ↦ f ((realizationCylinderSimplexIso X k).inv ((x, t), z)))
    (realizationSimplexCylinderSwap X k)
  change (realizationSimplexCylinderIso X k).hom
    (SSet.toTop.map (simplicialSimplexCylinderSwap X k)
      ((realizationCylinderSimplexIso X k).inv ((x, t), z))) =
    (realizationSimplexCylinderIso X k).hom
      ((realizationSimplexCylinderIso X k).inv ((x, z), t))
  simpa only [TopCat.comp_app, Iso.inv_hom_id_apply,
    topologicalSimplexCylinderSwap_apply] using h

/-- A genuine simplex-parameterized simplicial map realized using the actual product comparison. -/
def realizationSimplexFamily {X Y : SSet.{u}} {k : ℕ} (H : X ⊗ Δ[k] ⟶ Y) :
    C(|X| × |(Δ[k] : SSet.{u})|, |Y|) :=
  (SSet.toTop.map H).hom.comp (realizationProductSimplexIso X k).inv.hom

/-- Naturality of the original inverse product-simplex comparison under source maps. -/
theorem realizationProductSimplexIso_inv_whisker {X Y : SSet.{u}} (f : X ⟶ Y) (k : ℕ) :
    (realizationProductSimplexIso X k).inv ≫ SSet.toTop.map (f ▷ Δ[k]) =
      (SSet.toTop.map f ▷ |(Δ[k] : SSet.{u})|) ≫ (realizationProductSimplexIso Y k).inv := by
  have h := realizationProductSimplexIso_naturality f (𝟙 ⦋k⦌)
  simpa using (CommSq.vert_inv (CommSq.mk h)).w.symm

/-- A proved simplicial interval/simplex square gives actual independent-coordinate interchange. -/
theorem realizationSimplexFamily_interchange {X Y X' Y' : SSet.{u}} {k : ℕ}
    (H : X ⊗ Δ[k] ⟶ Y) (H' : X' ⊗ Δ[k] ⟶ Y')
    {f g : X ⟶ X'} {f' g' : Y ⟶ Y'}
    (K : SSet.Homotopy f g) (K' : SSet.Homotopy f' g')
    (hs : K.h ▷ Δ[k] ≫ H' =
      simplicialSimplexCylinderSwap X k ≫ H ▷ Δ[1] ≫ K'.h)
    (z : |(Δ[k] : SSet.{u})|) (t : unitInterval) (x : |X|) :
    realizationSimplexFamily H' (realizationSimplicialHomotopy K (t, x), z) =
      realizationSimplicialHomotopy K' (t, realizationSimplexFamily H (x, z)) := by
  let p := (realizationProductSimplexIso (X ⊗ Δ[1]) k).inv
    ((realizationCylinderIso X).inv (x, ULift.up t), z)
  have hK := ConcreteCategory.congr_hom (realizationProductSimplexIso_inv_whisker K.h k)
    ((realizationCylinderIso X).inv (x, ULift.up t), z)
  have hH := ConcreteCategory.congr_hom (realizationCylinderIso_inv_naturality H)
    ((realizationProductSimplexIso X k).inv (x, z), ULift.up t)
  change SSet.toTop.map (K.h ▷ Δ[k]) p =
    (realizationProductSimplexIso X' k).inv
      (SSet.toTop.map K.h ((realizationCylinderIso X).inv (x, ULift.up t)), z) at hK
  change SSet.toTop.map (H ▷ Δ[1])
    ((realizationCylinderIso (X ⊗ Δ[k])).inv
      ((realizationProductSimplexIso X k).inv (x, z), ULift.up t)) =
    (realizationCylinderIso Y).inv
      (SSet.toTop.map H ((realizationProductSimplexIso X k).inv (x, z)), ULift.up t) at hH
  change SSet.toTop.map H' ((realizationProductSimplexIso X' k).inv
      (SSet.toTop.map K.h ((realizationCylinderIso X).inv (x, ULift.up t)), z)) =
    SSet.toTop.map K'.h ((realizationCylinderIso Y).inv
      (SSet.toTop.map H ((realizationProductSimplexIso X k).inv (x, z)), ULift.up t))
  rw [← hK, ← hH, ← realizationSimplexCylinderSwap_inv X k x (ULift.up t) z]
  change (SSet.toTop.map (K.h ▷ Δ[k]) ≫ SSet.toTop.map H') p =
    (SSet.toTop.map (simplicialSimplexCylinderSwap X k) ≫
      SSet.toTop.map (H ▷ Δ[1]) ≫ SSet.toTop.map K'.h) p
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hs]

end SSet
