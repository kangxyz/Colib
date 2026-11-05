/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.IntervalArrows
public import Colib.CategoryTheory.Waldhausen.Additivity.SplitSequence

/-! # Actual endpoint isomorphisms of the interval pushout deformation

Implementation provenance: `Quillen/Waldhausen/Additivity/IntervalEndpoints.lean`
at commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual maps, hypotheses and
universes are retained; no subdivision realization equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v u' v'

namespace CategoryTheory.Waldhausen.Additivity

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (V : Structure C) (W : Structure D) {F G H : C ⥤ D}
variable (a : F ⟶ G) (hc : IsCofibrationTransformation W a V)
variable {n p m : SimplexCategory}

/-- Equal outer restrictions give identity arrows in the source category. -/
theorem intervalArrows_identity_hom (α : n ⟶ p) (A : Grid₂ p m ⥤ C) (x : Grid₂ n m) :
    ((intervalArrows α α (fun _ ↦ le_rfl) A).obj x).hom =
      𝟙 (A.obj ((gridMap₂ α (𝟙 m)).obj x)) := by
  change A.map (𝟙 _) = _
  exact A.map_id _

/-- The identity endpoint of the interval deformation is the middle functor,
via the actual source inclusions of the pushouts. -/
def identityDeformationIso (α : n ⟶ p) (A : Grid₂ p m ⥤ C) :
    deformedGrid V W a hc α α (fun _ ↦ le_rfl) A ≅ gridMap₂ α (𝟙 m) ⋙ A ⋙ G := by
  let T := intervalArrows α α (fun _ ↦ le_rfl) A
  let η := Functor.whiskerLeft T (sourceιNatTrans W a hc.app_cof)
  have hη (x : Grid₂ n m) : IsIso (η.app x) := by
    change IsIso (sourceι W a hc.app_cof (T.obj x))
    let : IsIso (F.map (T.obj x).hom) := by
      change IsIso (F.map (A.map (𝟙 ((gridMap₂ α (𝟙 m)).obj x))))
      rw [A.map_id, F.map_id]
      infer_instance
    exact (pushoutFunctor_isPushout W a hc.app_cof (T.obj x)).isIso_inl_of_isIso
  letI : ∀ x, IsIso (η.app x) := hη
  letI : IsIso η := NatIso.isIso_of_isIso_app η
  exact (asIso η).symm

variable (α β : n ⟶ p) (h : ∀ i, α.toOrderHom i ≤ β.toOrderHom i)
variable (hsep : ∀ i j, α.toOrderHom j ≤ β.toOrderHom i)

include hsep in
/-- When every first-copy vertex precedes every second-copy vertex, the
actual comparison of intervals is the canonical zero map. -/
theorem intervalArrows_separated_hom {A : Grid₂ p m ⥤ C}
    (hA : IsSimplex₂ V.cof V.weq A) (x : Grid₂ n m) :
    ((intervalArrows α β h A).obj x).hom =
      zeroMorphism V (A.obj ((gridMap₂ α (𝟙 m)).obj x))
        (A.obj ((gridMap₂ β (𝟙 m)).obj x)) := by
  let z : Grid₂ p m := grid₂ x.1 (α.toOrderHom x.2.1.2) (α.toOrderHom x.2.1.2) le_rfl
  let f₀ : (gridMap₂ α (𝟙 m)).obj x ⟶ z :=
    homOfLE ⟨le_rfl, α.toOrderHom.monotone x.2.2, le_rfl⟩
  let g₀ : z ⟶ (gridMap₂ β (𝟙 m)).obj x :=
    homOfLE ⟨le_rfl, hsep x.2.1.1 x.2.1.2, hsep x.2.1.2 x.2.1.2⟩
  change A.map _ = _
  exact (congrArg A.map (show _ = f₀ ≫ g₀ from Subsingleton.elim _ _)).trans
    ((A.map_comp f₀ g₀).trans (comp_through_isZero V
      (hA.zero x.1 (α.toOrderHom x.2.1.2)) (A.map f₀) (A.map g₀)))

variable [HasBinaryCoproducts D]
variable (b : G ⟶ H) (hs : IsCofibrationSequence V W a b)

/-- The separated endpoint is naturally the sum of the quotient on the first
restriction and the subobject functor on the second restriction. -/
def separatedDeformationIso {A : Grid₂ p m ⥤ C} (hA : IsSimplex₂ V.cof V.weq A) :
    deformedGrid V W a hs.cofibration α β h A ≅
      sumFunctor (gridMap₂ α (𝟙 m) ⋙ A ⋙ H) (gridMap₂ β (𝟙 m) ⋙ A ⋙ F) :=
  NatIso.ofComponents (fun x ↦ cofiberEndpointIso W a hs.cofibration.app_cof
    ((intervalArrows α β h A).obj x) (b.app _) (hs.cofiber _) (by
      rw [intervalArrows_separated_hom V α β h hsep hA x]
      exact map_zeroMorphism V W hs.exactF _ _)) (by
        intro x y f
        apply (pushoutFunctor_isPushout W a hs.cofibration.app_cof
          ((intervalArrows α β h A).obj x)).hom_ext
        · simp only [deformedGrid, Functor.comp_map, sourceι_naturality_assoc,
            sourceι_cofiberEndpointIso, sourceι_cofiberEndpointIso_assoc]
          change G.map (A.map ((gridMap₂ α (𝟙 m)).map f)) ≫ b.app _ ≫ coprod.inl =
            b.app _ ≫ coprod.inl ≫ coprod.map
              (H.map (A.map ((gridMap₂ α (𝟙 m)).map f)))
              (F.map (A.map ((gridMap₂ β (𝟙 m)).map f)))
          rw [coprod.inl_map, ← Category.assoc, b.naturality, Category.assoc]
        · simp only [deformedGrid, Functor.comp_map, targetι_naturality_assoc,
            targetι_cofiberEndpointIso, targetι_cofiberEndpointIso_assoc]
          change F.map (A.map ((gridMap₂ β (𝟙 m)).map f)) ≫ coprod.inr =
            coprod.inr ≫ coprod.map
              (H.map (A.map ((gridMap₂ α (𝟙 m)).map f)))
              (F.map (A.map ((gridMap₂ β (𝟙 m)).map f)))
          rw [coprod.inr_map])

end CategoryTheory.Waldhausen.Additivity
