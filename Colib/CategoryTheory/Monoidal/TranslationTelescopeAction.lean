/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.TranslationTelescopeCoherence
public import Mathlib.CategoryTheory.Monoidal.Action.Basic

/-!
Adapted from `Quillen/CategoryTheory/Monoidal/TranslationTelescopeAction.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual
stagewise tensor maps, unitors and associators.
 # The genuine monoidal action on the original translation telescope -/

@[expose] public section
open CategoryTheory MonoidalCategory Grothendieck
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A morphism of translating objects acts by its original tensor morphism. -/
def leftTranslationNatTrans (e : C) {P Q : C} (f : P ⟶ Q) :
    leftTranslation e P ⟶ leftTranslation e Q :=
  Functor.whiskerLeft (modelEquivalence e).functor
    (Functor.whiskerRight
      (EndofunctorTelescope.mapNatTrans (leftStep e P) (leftStep e Q)
        ((curriedTensor C).map f) (by
          intro X
          dsimp [leftStep]
          exact associator_naturality_left f X e))
      (modelEquivalence e).inverse)

/-- The parameter action is the original map in its literal stage. -/
theorem leftTranslationNatTrans_app (e : C) {P Q : C} (f : P ⟶ Q) (X : Model e) :
    (leftTranslationNatTrans e f).app X =
      (Grothendieck.ι (diagram e) X.base).map
        (AsSmall.up.map (f ▷ (AsSmall.down.obj X.fiber : C))) := by
  refine Grothendieck.ext _ _ ?_ ?_
  · rfl
  · simp [leftTranslationNatTrans, modelEquivalence,
      EndofunctorTelescope.mapNatTrans, Grothendieck.ι, diagram, eqToHom_map]

/-- On the unlifted telescope the unit is literally the stage unitor. -/
theorem originalUnitIso_hom_app (e : C)
    (X : EndofunctorTelescope.Model (tensorRight e)) :
    (originalUnitIso e).hom.app X =
      (Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight e)) X.base).map
        (MonoidalCategory.leftUnitor (C := C) X.fiber).hom := by
  simp only [originalUnitIso, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  change (Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight e)) X.base).map
    (MonoidalCategory.leftUnitor (C := C) X.fiber).hom ≫
    eqToHom _ = _
  simp only [eqToHom_refl, Category.comp_id]

/-- On the unlifted telescope the associator is literally the stage associator. -/
theorem originalTensorIso_hom_app (e P Q : C)
    (X : EndofunctorTelescope.Model (tensorRight e)) :
    (originalTensorIso e P Q).hom.app X =
      (Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight e)) X.base).map
        (α_ P Q X.fiber).hom := by
  simp only [originalTensorIso, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  change (Grothendieck.ι (EndofunctorTelescope.diagram (tensorRight e)) X.base).map
    (α_ P Q X.fiber).hom ≫ eqToHom _ = _
  simp only [eqToHom_refl, Category.comp_id]

/-- The unit constraint is the original left unitor at that stage. -/
theorem leftTranslationUnit_hom_app (e : C) (X : Model e) :
    (leftTranslationUnit e).hom.app X =
      (Grothendieck.ι (diagram e) X.base).map
        (AsSmall.up.map (λ_ (AsSmall.down.obj X.fiber : C)).hom) := by
  change (modelEquivalence e).inverse.map
    ((originalUnitIso e).hom.app ((modelEquivalence e).functor.obj X)) ≫ 𝟙 _ = _
  rw [Category.comp_id, originalUnitIso_hom_app]
  refine Grothendieck.ext _ _ rfl ?_
  simp [modelEquivalence, Grothendieck.ι, diagram, eqToHom_map]

/-- The action associator is the original tensor associator at that stage. -/
theorem leftTranslationTensor_hom_app (e P Q : C) (X : Model e) :
    (leftTranslationTensor e P Q).hom.app X =
      (Grothendieck.ι (diagram e) X.base).map
        (AsSmall.up.map (α_ P Q (AsSmall.down.obj X.fiber : C)).hom) := by
  change (modelEquivalence e).inverse.map
    ((originalTensorIso e P Q).hom.app ((modelEquivalence e).functor.obj X)) ≫
      (modelEquivalence e).inverse.map ((EndofunctorTelescope.map (leftStep e P)).map (𝟙 _)) = _
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [originalTensorIso_hom_app]
  refine Grothendieck.ext _ _ rfl ?_
  simp [modelEquivalence, Grothendieck.ι, diagram, eqToHom_map]

/-- The original stage arrow associated with an actual morphism of the actor. -/
def stageArrow (e : C) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (Grothendieck.ι (diagram e) n).obj (AsSmall.up.obj X) ⟶
      (Grothendieck.ι (diagram e) n).obj (AsSmall.up.obj Y) :=
  (Grothendieck.ι (diagram e) n).map (AsSmall.up.map f)

@[simp]
theorem stageArrow_id (e : C) (n : ℕ) (X : C) :
    stageArrow e n (𝟙 X) = 𝟙 _ := by
  exact (AsSmall.up ⋙ Grothendieck.ι (diagram e) n).map_id X

@[simp]
theorem stageArrow_comp (e : C) (n : ℕ) {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    stageArrow e n (f ≫ g) = stageArrow e n f ≫ stageArrow e n g := by
  exact (AsSmall.up ⋙ Grothendieck.ι (diagram e) n).map_comp f g

/-- Action on a stage arrow is exactly tensoring its original morphism. -/
theorem leftTranslation_map_stageArrow (e P : C) (n : ℕ) {X Y : C} (f : X ⟶ Y) :
    (leftTranslation e P).map (stageArrow e n f) = stageArrow e n (P ◁ f) :=
  eq_of_heq (CategoryTheory.Functor.hcongr_hom (inclusion_leftTranslation e P n)
    (AsSmall.up.map f))

/-- Parameter identities act as the actual identity transformations. -/
theorem leftTranslationNatTrans_id (e P : C) :
    leftTranslationNatTrans e (𝟙 P) = 𝟙 (leftTranslation e P) := by
  apply NatTrans.ext
  funext X
  rw [leftTranslationNatTrans_app]
  change stageArrow e X.base (𝟙 P ▷ (AsSmall.down.obj X.fiber : C)) = _
  rw [id_whiskerRight, stageArrow_id]
  rfl

/-- Parameter composition is literal composition of natural transformations. -/
theorem leftTranslationNatTrans_comp (e : C) {P Q V : C} (f : P ⟶ Q) (g : Q ⟶ V) :
    leftTranslationNatTrans e (f ≫ g) =
      leftTranslationNatTrans e f ≫ leftTranslationNatTrans e g := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, leftTranslationNatTrans_app, comp_whiskerRight,
    Functor.map_comp]


/-- The inverse action associator retains the inverse tensor associator. -/
theorem leftTranslationTensor_inv_app (e P Q : C) (X : Model e) :
    (leftTranslationTensor e P Q).inv.app X =
      stageArrow e X.base (α_ P Q (AsSmall.down.obj X.fiber : C)).inv := by
  have h : (leftTranslationTensor e P Q).app X =
      (AsSmall.up ⋙ Grothendieck.ι (diagram e) X.base).mapIso
        (α_ P Q (AsSmall.down.obj X.fiber : C)) :=
    Iso.ext (leftTranslationTensor_hom_app e P Q X)
  exact congrArg Iso.inv h

/-- The original telescope translations form a genuine coherent monoidal action. -/
@[instance_reducible]
def monoidalLeftAction (e : C) : MonoidalLeftAction C (Model e) where
  actionObj P X := (leftTranslation e P).obj X
  actionHomLeft f X := (leftTranslationNatTrans e f).app X
  actionHomRight P {_ _} f := (leftTranslation e P).map f
  actionAssocIso P Q X := (leftTranslationTensor e P Q).app X
  actionUnitIso X := (leftTranslationUnit e).app X
  actionHomRight_id P X := (leftTranslation e P).map_id X
  id_actionHomLeft P X := by
    rw [leftTranslationNatTrans_id]
    rfl
  actionHom_comp f₁ f₂ g₁ g₂ := by
    change (leftTranslationNatTrans e (f₁ ≫ f₂)).app _ ≫
      (leftTranslation e _).map (g₁ ≫ g₂) = _
    rw [leftTranslationNatTrans_comp, NatTrans.comp_app, Functor.map_comp]
    simp only [Category.assoc]
    rw [(leftTranslationNatTrans e f₂).naturality_assoc]
  actionAssocIso_hom_naturality {P P' Q Q'} {X Y} f g h := by
    dsimp
    simp only [Functor.map_comp, Category.assoc]
    rw [(leftTranslationTensor e P' Q').hom.naturality h]
    suffices ht : (leftTranslationNatTrans e (f ⊗ₘ g)).app X ≫
        (leftTranslationTensor e P' Q').hom.app X =
      (leftTranslationTensor e P Q).hom.app X ≫
        (leftTranslationNatTrans e f).app ((leftTranslation e Q).obj X) ≫
          (leftTranslation e P').map ((leftTranslationNatTrans e g).app X) by
      simpa only [Functor.comp_map, Category.assoc] using congrArg
        (fun z ↦ z ≫ (leftTranslation e P').map ((leftTranslation e Q').map h)) ht
    rw [leftTranslationNatTrans_app, leftTranslationTensor_hom_app,
      leftTranslationTensor_hom_app, leftTranslationNatTrans_app, leftTranslationNatTrans_app]
    change stageArrow e X.base ((f ⊗ₘ g) ▷ (AsSmall.down.obj X.fiber : C)) ≫
      stageArrow e X.base (α_ P' Q' (AsSmall.down.obj X.fiber : C)).hom =
      stageArrow e X.base (α_ P Q (AsSmall.down.obj X.fiber : C)).hom ≫
        stageArrow e X.base (f ▷ (Q ⊗ (AsSmall.down.obj X.fiber : C))) ≫
          (leftTranslation e P').map (stageArrow e X.base
            (g ▷ (AsSmall.down.obj X.fiber : C)))
    rw [leftTranslation_map_stageArrow, ← stageArrow_comp, ← stageArrow_comp,
      ← stageArrow_comp]
    apply congrArg (stageArrow e X.base)
    simpa only [tensorHom_def, whiskerLeft_id, Category.comp_id] using
      associator_naturality f g (𝟙 (AsSmall.down.obj X.fiber : C))
  actionUnitIso_hom_naturality f := (leftTranslationUnit e).hom.naturality f |>.symm
  whiskerLeft_actionHomLeft P {Q Q'} f X := by
    dsimp
    rw [leftTranslationNatTrans_app, leftTranslationTensor_hom_app,
      leftTranslationNatTrans_app, leftTranslationTensor_inv_app]
    change stageArrow e X.base ((P ◁ f) ▷ (AsSmall.down.obj X.fiber : C)) =
      stageArrow e X.base (α_ P Q (AsSmall.down.obj X.fiber : C)).hom ≫
        (leftTranslation e P).map (stageArrow e X.base
          (f ▷ (AsSmall.down.obj X.fiber : C))) ≫
        stageArrow e X.base (α_ P Q' (AsSmall.down.obj X.fiber : C)).inv
    rw [leftTranslation_map_stageArrow, ← stageArrow_comp, ← stageArrow_comp]
    apply congrArg (stageArrow e X.base)
    simp
  whiskerRight_actionHomLeft {P P'} Q f X := by
    dsimp
    rw [leftTranslationNatTrans_app, leftTranslationTensor_hom_app,
      leftTranslationNatTrans_app, leftTranslationTensor_inv_app]
    change stageArrow e X.base (f ▷ Q ▷ (AsSmall.down.obj X.fiber : C)) =
      stageArrow e X.base (α_ P Q (AsSmall.down.obj X.fiber : C)).hom ≫
        stageArrow e X.base (f ▷ (Q ⊗ (AsSmall.down.obj X.fiber : C))) ≫
        stageArrow e X.base (α_ P' Q (AsSmall.down.obj X.fiber : C)).inv
    rw [← stageArrow_comp, ← stageArrow_comp]
    apply congrArg (stageArrow e X.base)
    simp
  associator_actionHom P Q V X := by
    dsimp
    rw [leftTranslationNatTrans_app, leftTranslationTensor_hom_app,
      leftTranslationTensor_hom_app, leftTranslationTensor_hom_app,
      leftTranslationTensor_hom_app]
    change stageArrow e X.base ((α_ P Q V).hom ▷ (AsSmall.down.obj X.fiber : C)) ≫
      stageArrow e X.base (α_ P (Q ⊗ V) (AsSmall.down.obj X.fiber : C)).hom ≫
        (leftTranslation e P).map (stageArrow e X.base
          (α_ Q V (AsSmall.down.obj X.fiber : C)).hom) =
      stageArrow e X.base (α_ (P ⊗ Q) V (AsSmall.down.obj X.fiber : C)).hom ≫
        stageArrow e X.base (α_ P Q (V ⊗ (AsSmall.down.obj X.fiber : C))).hom
    rw [leftTranslation_map_stageArrow, ← stageArrow_comp, ← stageArrow_comp,
      ← stageArrow_comp]
    exact congrArg (stageArrow e X.base) (pentagon P Q V _)
  leftUnitor_actionHom P X := by
    dsimp
    rw [leftTranslationNatTrans_app, leftTranslationTensor_hom_app,
      leftTranslationUnit_hom_app]
    change stageArrow e X.base ((λ_ P).hom ▷ (AsSmall.down.obj X.fiber : C)) =
      stageArrow e X.base (α_ (𝟙_ C) P (AsSmall.down.obj X.fiber : C)).hom ≫
        stageArrow e X.base (λ_ (P ⊗ (AsSmall.down.obj X.fiber : C))).hom
    rw [← stageArrow_comp]
    apply congrArg (stageArrow e X.base)
    rw [leftUnitor_tensor_hom]
    simp
  rightUnitor_actionHom P X := by
    dsimp
    rw [leftTranslationNatTrans_app, leftTranslationTensor_hom_app,
      leftTranslationUnit_hom_app]
    change stageArrow e X.base ((ρ_ P).hom ▷ (AsSmall.down.obj X.fiber : C)) =
      stageArrow e X.base (α_ P (𝟙_ C) (AsSmall.down.obj X.fiber : C)).hom ≫
        (leftTranslation e P).map (stageArrow e X.base
          (λ_ (AsSmall.down.obj X.fiber : C)).hom)
    rw [leftTranslation_map_stageArrow, ← stageArrow_comp]
    exact congrArg (stageArrow e X.base) (triangle P (AsSmall.down.obj X.fiber)).symm


/-- The packaged action retains exactly the original telescope endofunctor. -/
theorem actionLeft_eq_leftTranslation (e P : C) :
    letI := monoidalLeftAction e
    MonoidalLeftAction.actionLeft (Model e) P = leftTranslation e P := rfl


end CategoryTheory.MonoidalCategory.TranslationTelescope
