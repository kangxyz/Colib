/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.TranslationTelescopeStages
public import Colib.CategoryTheory.Monoidal.Action.RightTensorLinear

/-! # Original stage transitions retain their actual action compatibility -/

/-!
Implementation provenance: adapted from
`Quillen/CategoryTheory/Monoidal/TranslationTelescopeTransitions.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section
open CategoryTheory MonoidalCategory Grothendieck
open scoped MonoidalLeftAction
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)
attribute [local instance] monoidalLeftAction

/-- The actual original stage arrow, including its full iterated right stabilization. -/
def stageTransition {n m : ℕ} (h : n ⟶ m) :
    stageInclusion e n ⟶
      EndofunctorTelescope.iterate (tensorRight e) (m - n) ⋙ stageInclusion e m :=
  Functor.whiskerLeft AsSmall.up (Grothendieck.ιNatTrans (F := diagram e) h)

/-- The genuine composite linear structure at the target of a stage transition. -/
@[instance_reducible]
def stageTransitionTargetLinear (n m : ℕ) :
    (EndofunctorTelescope.iterate (tensorRight e) (m - n) ⋙
      stageInclusion e m).LaxLeftLinear C := by
  letI := rightIterateLinear e (m - n)
  exact Functor.LaxLeftLinear.composition _ _

/-- Forgetting the common-universe wrapper preserves the actual stage arrow. -/
theorem stageArrow_forward (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (modelEquivalence e).functor.map (stageArrow e n f) =
      (Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight e)) n).map f :=
  eq_of_heq (CategoryTheory.Functor.hcongr_hom (inclusion_forward e n) (AsSmall.up.map f))

/-- The original transition is unchanged by the actual common-universe equivalence. -/
theorem stageTransition_forward {n m : ℕ} (h : n ⟶ m) (X : C) :
    (modelEquivalence e).functor.map ((stageTransition e h).app X) =
      (Grothendieck.ιNatTrans (F := EndofunctorTelescope.diagram (tensorRight e)) h).app X := by
  refine Grothendieck.ext _ _ rfl ?_
  simp [stageTransition, modelEquivalence]
  rfl

/-- Forgetting the wrapper commutes with the original translation on arrows. -/
theorem leftTranslation_forward_map (P : C) {X Y : Model e} (f : X ⟶ Y) :
    (modelEquivalence e).functor.map ((leftTranslation e P).map f) =
      (EndofunctorTelescope.map (leftStep e P)).map ((modelEquivalence e).functor.map f) := rfl

/-- The stage arrow is compatible with the original action, with the iterated
inverse-associator lineator explicitly retained. -/
theorem stageTransition_action {n m : ℕ} (h : n ⟶ m) (P X : C) :
    (stageTransition e h).app (P ⊗ X) =
      (leftTranslation e P).map ((stageTransition e h).app X) ≫
        stageArrow e m (rightIterateLineator e (m - n) P X) := by
  apply (modelEquivalence e).functor.map_injective
  rw [Functor.map_comp]
  rw [leftTranslation_forward_map, stageTransition_forward, stageTransition_forward,
    stageArrow_forward]
  change (Grothendieck.ιNatTrans (F := EndofunctorTelescope.diagram (tensorRight e)) h).app
      (MonoidalCategory.tensorObj (C := C) P X) =
    (EndofunctorTelescope.map (leftStep e P)).map
      ((Grothendieck.ιNatTrans (F := EndofunctorTelescope.diagram (tensorRight e)) h).app X) ≫
      (Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight e)) m).map
        (rightIterateLineator e (m - n) P X)
  refine Grothendieck.ext _ _ ?_ ?_
  · change h = h ≫ 𝟙 m
    exact (Category.comp_id h).symm
  · simp only [EndofunctorTelescope.map, EndofunctorTelescope.diagram,
      Functor.comp_obj, Functor.toCatHom_toFunctor, Functor.map_id,
      Grothendieck.ι_obj, curriedTensor_obj_obj,
      Grothendieck.ι_map, Grothendieck.comp_base, Grothendieck.ιNatTrans_app_base,
      eqToHom_refl, Grothendieck.ιNatTrans_app_fiber, Category.comp_id,
      Grothendieck.comp_fiber]
    rw [EndofunctorTelescope.iterate_map_of_eq_zero _ (Nat.sub_self m)]
    simp only [← Category.assoc, eqToHom_trans]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    exact (commuteIterate_rightIterateLineator e (m - n) P X).symm


end CategoryTheory.MonoidalCategory.TranslationTelescope
