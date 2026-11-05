/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.PushoutEndpoints

/-! # Cofibrations under the additivity pushout functor

The proof factors a commutative square into change of target and change of
source. Each resulting pushout-functor map is a genuine cobase change: first
of the target cofibration, then of the structural relative-cofibration map.


## Implementation provenance

Adapted from `Quillen/Waldhausen/Additivity/PushoutCofibrations.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original objects, maps,
universes and hypotheses are retained. This categorical input is not an
additivity theorem on realizations or K-groups.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v u' v'

namespace CategoryTheory.Waldhausen.Additivity

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (W : Structure D) {F G : C ⥤ D} (a : F ⟶ G)
variable (ha : ∀ X, W.cof (a.app X))

/-- The square changing only the target of an arrow. -/
def postcomposeArrow {X Y Z : C} (f : X ⟶ Y) (v : Y ⟶ Z) :
    Arrow.mk f ⟶ Arrow.mk (f ≫ v) := Arrow.homMk (𝟙 X) v (by simp)

/-- The square changing only the source of an arrow. -/
def precomposeArrow {X Y Z : C} (u : X ⟶ Y) (g : Y ⟶ Z) :
    Arrow.mk (u ≫ g) ⟶ Arrow.mk g := Arrow.homMk u (𝟙 Z) (by simp)

/-- Changing the target gives the actual cobase-change square. -/
theorem postcompose_isPushout {X Y Z : C} (f : X ⟶ Y) (v : Y ⟶ Z) :
    IsPushout (targetι W a ha (Arrow.mk f)) (F.map v)
      ((pushoutFunctor W a ha).map (postcomposeArrow f v))
      (targetι W a ha (Arrow.mk (f ≫ v))) := by
  have hs := pushoutFunctor_isPushout W a ha (Arrow.mk (f ≫ v))
  have h₁ := sourceι_naturality W a ha (postcomposeArrow f v)
  change sourceι W a ha (Arrow.mk f) ≫ _ = G.map (𝟙 X) ≫ _ at h₁
  rw [G.map_id, Category.id_comp] at h₁
  change IsPushout (a.app X) (F.map (f ≫ v)) _ _ at hs
  rw [F.map_comp, ← h₁] at hs
  exact hs.of_top (targetι_naturality W a ha (postcomposeArrow f v))
    (pushoutFunctor_isPushout W a ha (Arrow.mk f))

/-- The commutativity needed to paste the source-change pushout. -/
theorem source_change_comm {X Y Z : C} (u : X ⟶ Y) (g : Y ⟶ Z) :
    comparison W a ha (Arrow.mk u) ≫ sourceι W a ha (Arrow.mk g) =
      (pushoutFunctor W a ha).map (postcomposeArrow u g) ≫
        (pushoutFunctor W a ha).map (precomposeArrow u g) := by
  apply (pushoutFunctor_isPushout W a ha (Arrow.mk u)).hom_ext
  · rw [sourceι_comparison_assoc, sourceι_naturality_assoc, sourceι_naturality]
    change G.map u ≫ _ = G.map (𝟙 X) ≫ G.map u ≫ _
    rw [G.map_id, Category.id_comp]
  · rw [targetι_comparison_assoc, targetι_naturality_assoc, targetι_naturality]
    change a.app Y ≫ sourceι W a ha (Arrow.mk g) =
      F.map g ≫ F.map (𝟙 Z) ≫ targetι W a ha (Arrow.mk g)
    rw [F.map_id, Category.id_comp]
    exact (pushoutFunctor_isPushout W a ha (Arrow.mk g)).w

/-- Changing the source is the cobase change of the actual relative comparison. -/
theorem precompose_isPushout {X Y Z : C} (u : X ⟶ Y) (g : Y ⟶ Z) :
    IsPushout (comparison W a ha (Arrow.mk u))
      ((pushoutFunctor W a ha).map (postcomposeArrow u g))
      (sourceι W a ha (Arrow.mk g))
      ((pushoutFunctor W a ha).map (precomposeArrow u g)) := by
  have hs := pushoutFunctor_isPushout W a ha (Arrow.mk g)
  have h₂ := targetι_naturality W a ha (precomposeArrow u g)
  change targetι W a ha (Arrow.mk (u ≫ g)) ≫ _ = F.map (𝟙 Z) ≫ _ at h₂
  rw [F.map_id, Category.id_comp] at h₂
  have h₁ : targetι W a ha (Arrow.mk u) ≫ comparison W a ha (Arrow.mk u) = a.app Y :=
    targetι_comparison W a ha (Arrow.mk u)
  change IsPushout (a.app Y) (F.map g) _ _ at hs
  rw [← h₁, ← h₂] at hs
  exact hs.of_left (source_change_comm W a ha u g)
    (postcompose_isPushout W a ha u g)

variable (V : Structure C)
variable (hF : IsExact V.cof V.weq W.cof W.weq F)
variable (hG : IsExact V.cof V.weq W.cof W.weq G)
variable (h : IsCofibrationTransformation W a V)

include hF hG in
/-- A pointwise weak-equivalence square is carried to an actual weak equivalence. -/
theorem pushoutFunctor_map_weak_of_exact {f g : Arrow C} (φ : f ⟶ g)
    (hleft : V.weq φ.left) (hright : V.weq φ.right) :
    W.weq ((pushoutFunctor W a h.app_cof).map φ) :=
  pushoutFunctor_map_weak W a h.app_cof φ
    (hF.weak _ hleft) (hG.weak _ hleft) (hF.weak _ hright)

include hF in
/-- Changing a cofibrant target gives a cofibration by actual cobase change. -/
theorem postcompose_cof {X Y Z : C} (f : X ⟶ Y) (v : Y ⟶ Z) (hv : V.cof v) :
    W.cof ((pushoutFunctor W a h.app_cof).map (postcomposeArrow f v)) :=
  W.cof_pushout (hF.cofibration v hv) (postcompose_isPushout W a h.app_cof f v).flip

/-- Changing a cofibrant source gives a cofibration by the relative condition. -/
theorem precompose_cof {X Y Z : C} (u : X ⟶ Y) (g : Y ⟶ Z) (hu : V.cof u) :
    W.cof ((pushoutFunctor W a h.app_cof).map (precomposeArrow u g)) :=
  W.cof_pushout (h.relative_cof u hu) (precompose_isPushout W a h.app_cof u g)

include hF in
/-- The genuine pushout functor preserves every pointwise cofibration square. -/
theorem pushoutFunctor_map_cof {f g : Arrow C} (φ : f ⟶ g)
    (hleft : V.cof φ.left) (hright : V.cof φ.right) :
    W.cof ((pushoutFunctor W a h.app_cof).map φ) := by
  let e : Arrow.mk (f.hom ≫ φ.right) ≅ Arrow.mk (φ.left ≫ g.hom) :=
    eqToIso (congrArg (fun k ↦ Arrow.mk k) φ.w.symm)
  have he : postcomposeArrow f.hom φ.right ≫ e.hom ≫ precomposeArrow φ.left g.hom = φ := by
    apply Arrow.hom_ext <;> simp [e, postcomposeArrow, precomposeArrow, Arrow.eqToHom_left,
      Arrow.eqToHom_right]
  rw [← he, Functor.map_comp, Functor.map_comp]
  apply W.cof.comp_mem
  · exact postcompose_cof W a V hF h f.hom φ.right hright
  · apply W.cof.comp_mem
    · exact W.cof_iso _ (by infer_instance)
    · exact precompose_cof W a V h φ.left g.hom hleft

end CategoryTheory.Waldhausen.Additivity
