/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.GroupCompletion.DiagonalAction
public import Colib.CategoryTheory.GroupCompletion.Functoriality
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
Implementation provenance:
`Quillen/CategoryTheory/GroupCompletion/Monoidal.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Tensor multiplication on Grayson's category

The multiplication uses the braided middle-four interchange on both coordinates
and tensors the translating objects. Quotient compatibility is proved with the
same tensor product of isomorphisms on both coordinates.
-/

@[expose] public section

universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalLeftAction

namespace CategoryTheory.GroupCompletion.Localization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Coordinatewise tensor product of pairs. -/
abbrev tensorPair (X Y : C × C) : C × C := (X.1 ⊗ Y.1, X.2 ⊗ Y.2)

/-- Multiply two actual translated representatives using middle-four interchange. -/
def tensorRep {X Y X' Y' : C × C}
    (f : ActionLocalization.HomRep (C := C) X Y)
    (g : ActionLocalization.HomRep (C := C) X' Y') :
    ActionLocalization.HomRep (C := C) (tensorPair X X') (tensorPair Y Y') :=
  ⟨f.denom ⊗ g.denom,
    (tensorμ f.denom g.denom X.1 X'.1 ≫ (f.map.1 ⊗ₘ g.map.1),
      tensorμ f.denom g.denom X.2 X'.2 ≫ (f.map.2 ⊗ₘ g.map.2))⟩

lemma tensorRep_rel {X Y X' Y' : C × C}
    {f f' : ActionLocalization.HomRep (C := C) X Y}
    {g g' : ActionLocalization.HomRep (C := C) X' Y'}
    (hf : ActionLocalization.HomRep.Rel f f')
    (hg : ActionLocalization.HomRep.Rel g g') :
    ActionLocalization.HomRep.Rel (tensorRep f g) (tensorRep f' g') := by
  obtain ⟨e, he⟩ := hf
  obtain ⟨d, hd⟩ := hg
  have he₁ : e.hom ▷ X.1 ≫ f'.map.1 = f.map.1 := congrArg _root_.Prod.fst he
  have he₂ : e.hom ▷ X.2 ≫ f'.map.2 = f.map.2 := congrArg _root_.Prod.snd he
  have hd₁ : d.hom ▷ X'.1 ≫ g'.map.1 = g.map.1 := congrArg _root_.Prod.fst hd
  have hd₂ : d.hom ▷ X'.2 ≫ g'.map.2 = g.map.2 := congrArg _root_.Prod.snd hd
  refine ⟨e ⊗ᵢ d, ?_⟩
  apply Prod.ext
  · change (e.hom ⊗ₘ d.hom) ▷ (X.1 ⊗ X'.1) ≫
      tensorμ f'.denom g'.denom X.1 X'.1 ≫ (f'.map.1 ⊗ₘ g'.map.1) =
      tensorμ f.denom g.denom X.1 X'.1 ≫ (f.map.1 ⊗ₘ g.map.1)
    rw [tensorμ_natural_left_assoc, tensorHom_comp_tensorHom, he₁, hd₁]
  · change (e.hom ⊗ₘ d.hom) ▷ (X.2 ⊗ X'.2) ≫
      tensorμ f'.denom g'.denom X.2 X'.2 ≫ (f'.map.2 ⊗ₘ g'.map.2) =
      tensorμ f.denom g.denom X.2 X'.2 ≫ (f.map.2 ⊗ₘ g.map.2)
    rw [tensorμ_natural_left_assoc, tensorHom_comp_tensorHom, he₂, hd₂]

private lemma tensor_comp_coherence {a b c d x x' y y' z z' : C}
    (f : a ⊗ x ⟶ y) (g : b ⊗ y ⟶ z)
    (f' : c ⊗ x' ⟶ y') (g' : d ⊗ y' ⟶ z') :
    tensorμ b d a c ▷ (x ⊗ x') ≫ tensorμ (b ⊗ a) (d ⊗ c) x x' ≫
      (((α_ b a x).hom ≫ b ◁ f ≫ g) ⊗ₘ ((α_ d c x').hom ≫ d ◁ f' ≫ g')) =
    (α_ (b ⊗ d) (a ⊗ c) (x ⊗ x')).hom ≫
      (b ⊗ d) ◁ (tensorμ a c x x' ≫ (f ⊗ₘ f')) ≫
        tensorμ b d y y' ≫ (g ⊗ₘ g') := by
  simp only [← tensorHom_comp_tensorHom, Category.assoc, whiskerLeft_comp]
  rw [tensor_associativity_assoc, tensorμ_natural_right_assoc]

lemma tensorRep_comp_rel {X Y Z X' Y' Z' : C × C}
    (f : ActionLocalization.HomRep (C := C) X Y)
    (g : ActionLocalization.HomRep (C := C) Y Z)
    (f' : ActionLocalization.HomRep (C := C) X' Y')
    (g' : ActionLocalization.HomRep (C := C) Y' Z') :
    ActionLocalization.HomRep.Rel
      ((tensorRep f f').comp (tensorRep g g')) (tensorRep (f.comp g) (f'.comp g')) := by
  refine ⟨⟨tensorμ g.denom g'.denom f.denom f'.denom,
    tensorδ g.denom g'.denom f.denom f'.denom,
    tensorμ_tensorδ _ _ _ _, tensorδ_tensorμ _ _ _ _⟩, ?_⟩
  exact Prod.ext (tensor_comp_coherence f.map.1 g.map.1 f'.map.1 g'.map.1)
    (tensor_comp_coherence f.map.2 g.map.2 f'.map.2 g'.map.2)

private lemma tensor_identity_coherence (X Y : C) :
    (λ_ (𝟙_ C)).hom ▷ (X ⊗ Y) ≫ (λ_ (X ⊗ Y)).hom =
      tensorμ (𝟙_ C) (𝟙_ C) X Y ≫ ((λ_ X).hom ⊗ₘ (λ_ Y).hom) := by
  simpa only [Category.assoc, hom_inv_whiskerRight_assoc] using
    congrArg ((λ_ (𝟙_ C)).hom ▷ (X ⊗ Y) ≫ ·) (tensor_left_unitality X Y)

lemma tensorRep_id_rel (X Y : C × C) :
    ActionLocalization.HomRep.Rel
      (tensorRep (ActionLocalization.HomRep.id (C := C) X)
        (ActionLocalization.HomRep.id (C := C) Y))
      (ActionLocalization.HomRep.id (C := C) (tensorPair X Y)) :=
  ⟨λ_ (𝟙_ C), Prod.ext (tensor_identity_coherence X.1 Y.1)
    (tensor_identity_coherence X.2 Y.2)⟩

/-- Actual tensor multiplication on arrows, descended through both quotients. -/
def tensorHom {X Y X' Y' : Localization C C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    (⟨tensorPair X.obj X'.obj⟩ : Localization C C) ⟶ ⟨tensorPair Y.obj Y'.obj⟩ :=
  Quotient.map₂ tensorRep (fun _ _ hf _ _ hg ↦ tensorRep_rel hf hg) f g

lemma tensorHom_comp {X Y Z X' Y' Z' : Localization C C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z') :
    tensorHom (f ≫ g) (f' ≫ g') = tensorHom f f' ≫ tensorHom g g' := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      induction f' using Quotient.inductionOn with
      | _ f' =>
        induction g' using Quotient.inductionOn with
        | _ g' =>
          exact Quotient.sound (ActionLocalization.HomRep.rel_symm (tensorRep_comp_rel f g f' g'))

@[simp]
lemma tensorHom_id (X Y : Localization C C) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (⟨tensorPair X.obj Y.obj⟩ : Localization C C) :=
  Quotient.sound (tensorRep_id_rel X.obj Y.obj)

/-- The actual multiplication bifunctor on Grayson's category. -/
def multiplication : Localization C C × Localization C C ⥤ Localization C C where
  obj X := ⟨tensorPair X.1.obj X.2.obj⟩
  map f := tensorHom f.1 f.2
  map_id X := tensorHom_id X.1 X.2
  map_comp f g := tensorHom_comp f.1 g.1 f.2 g.2

lemma tensorHom_ofHom {X Y X' Y' : C × C} (f : X ⟶ Y) (g : X' ⟶ Y') :
    tensorHom (ActionLocalization.ofHom (C := C) f)
      (ActionLocalization.ofHom (C := C) g) =
      ActionLocalization.ofHom (C := C)
        (X := tensorPair X X') (Y := tensorPair Y Y') (f.1 ⊗ₘ g.1, f.2 ⊗ₘ g.2) := by
  apply Quotient.sound
  refine ⟨λ_ (𝟙_ C), ?_⟩
  apply Prod.ext
  · change (λ_ (𝟙_ C)).hom ▷ (X.1 ⊗ X'.1) ≫
      (λ_ (X.1 ⊗ X'.1)).hom ≫ (f.1 ⊗ₘ g.1) =
      tensorμ (𝟙_ C) (𝟙_ C) X.1 X'.1 ≫
        (((λ_ X.1).hom ≫ f.1) ⊗ₘ ((λ_ X'.1).hom ≫ g.1))
    rw [← Category.assoc, tensor_identity_coherence, Category.assoc,
      tensorHom_comp_tensorHom]
  · change (λ_ (𝟙_ C)).hom ▷ (X.2 ⊗ X'.2) ≫
      (λ_ (X.2 ⊗ X'.2)).hom ≫ (f.2 ⊗ₘ g.2) =
      tensorμ (𝟙_ C) (𝟙_ C) X.2 X'.2 ≫
        (((λ_ X.2).hom ≫ f.2) ⊗ₘ ((λ_ X'.2).hom ≫ g.2))
    rw [← Category.assoc, tensor_identity_coherence, Category.assoc,
      tensorHom_comp_tensorHom]

private lemma left_unit_coherence {s x y : C} (f : s ⊗ x ⟶ y) :
    (λ_ s).hom ▷ (𝟙_ C ⊗ x) ≫ s ◁ (λ_ x).hom ≫ f =
      tensorμ (𝟙_ C) s (𝟙_ C) x ≫ ((λ_ (𝟙_ C)).hom ⊗ₘ f) ≫ (λ_ y).hom := by
  simp only [tensorHom_def, Category.assoc]
  rw [leftUnitor_naturality]
  have h := leftUnitor_monoidal s x
  rw [tensorHom_def] at h
  simpa only [Category.assoc] using congrArg (· ≫ f) h


/-- The unit pair of Grayson's multiplication. -/
abbrev unit : Localization C C := ⟨𝟙_ C, 𝟙_ C⟩

/-- The left unitor retains the actual unitors in the two original coordinates. -/
def leftUnitIso (X : Localization C C) :
    (⟨tensorPair (unit (C := C)).obj X.obj⟩ : Localization C C) ≅ X :=
  (ActionLocalization.ofFunctor (C := C)).mapIso ((λ_ X.obj.1).prod (λ_ X.obj.2))

lemma leftUnitIso_naturality {X Y : Localization C C} (f : X ⟶ Y) :
    tensorHom (𝟙 (unit (C := C))) f ≫ (leftUnitIso Y).hom =
      (leftUnitIso X).hom ≫ f := by
  induction f using Quotient.inductionOn with
  | _ f =>
    change ActionLocalization.mkHom (tensorRep (ActionLocalization.HomRep.id _) f) ≫
      ActionLocalization.ofHom _ = ActionLocalization.ofHom _ ≫ ActionLocalization.mkHom f
    rw [ActionLocalization.mkHom_comp_ofHom, ActionLocalization.ofHom_comp_mkHom]
    apply Quotient.sound
    refine ⟨λ_ f.denom, ?_⟩
    apply Prod.ext
    · change (λ_ f.denom).hom ▷ (𝟙_ C ⊗ X.obj.1) ≫
        f.denom ◁ (λ_ X.obj.1).hom ≫ f.map.1 =
        (tensorμ (𝟙_ C) f.denom (𝟙_ C) X.obj.1 ≫
          ((λ_ (𝟙_ C)).hom ⊗ₘ f.map.1)) ≫ (λ_ Y.obj.1).hom
      simpa only [Category.assoc] using left_unit_coherence f.map.1
    · change (λ_ f.denom).hom ▷ (𝟙_ C ⊗ X.obj.2) ≫
        f.denom ◁ (λ_ X.obj.2).hom ≫ f.map.2 =
        (tensorμ (𝟙_ C) f.denom (𝟙_ C) X.obj.2 ≫
          ((λ_ (𝟙_ C)).hom ⊗ₘ f.map.2)) ≫ (λ_ Y.obj.2).hom
      simpa only [Category.assoc] using left_unit_coherence f.map.2

private lemma right_unit_coherence {s x y : C} (f : s ⊗ x ⟶ y) :
    (ρ_ s).hom ▷ (x ⊗ 𝟙_ C) ≫ s ◁ (ρ_ x).hom ≫ f =
      tensorμ s (𝟙_ C) x (𝟙_ C) ≫ (f ⊗ₘ (λ_ (𝟙_ C)).hom) ≫ (ρ_ y).hom := by
  simp only [tensorHom_def', Category.assoc]
  rw [rightUnitor_naturality]
  have h := rightUnitor_monoidal s x
  rw [tensorHom_def] at h
  simpa only [Category.assoc] using congrArg (· ≫ f) h

/-- The right unitor retains the actual unitors in the two original coordinates. -/
def rightUnitIso (X : Localization C C) :
    (⟨tensorPair X.obj (unit (C := C)).obj⟩ : Localization C C) ≅ X :=
  (ActionLocalization.ofFunctor (C := C)).mapIso ((ρ_ X.obj.1).prod (ρ_ X.obj.2))

lemma rightUnitIso_naturality {X Y : Localization C C} (f : X ⟶ Y) :
    tensorHom f (𝟙 (unit (C := C))) ≫ (rightUnitIso Y).hom =
      (rightUnitIso X).hom ≫ f := by
  induction f using Quotient.inductionOn with
  | _ f =>
    change ActionLocalization.mkHom (tensorRep f (ActionLocalization.HomRep.id _)) ≫
      ActionLocalization.ofHom _ = ActionLocalization.ofHom _ ≫ ActionLocalization.mkHom f
    rw [ActionLocalization.mkHom_comp_ofHom, ActionLocalization.ofHom_comp_mkHom]
    apply Quotient.sound
    refine ⟨ρ_ f.denom, ?_⟩
    apply Prod.ext
    · change (ρ_ f.denom).hom ▷ (X.obj.1 ⊗ 𝟙_ C) ≫
        f.denom ◁ (ρ_ X.obj.1).hom ≫ f.map.1 =
        (tensorμ f.denom (𝟙_ C) X.obj.1 (𝟙_ C) ≫
          (f.map.1 ⊗ₘ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ Y.obj.1).hom
      simpa only [Category.assoc] using right_unit_coherence f.map.1
    · change (ρ_ f.denom).hom ▷ (X.obj.2 ⊗ 𝟙_ C) ≫
        f.denom ◁ (ρ_ X.obj.2).hom ≫ f.map.2 =
        (tensorμ f.denom (𝟙_ C) X.obj.2 (𝟙_ C) ≫
          (f.map.2 ⊗ₘ (λ_ (𝟙_ C)).hom)) ≫ (ρ_ Y.obj.2).hom
      simpa only [Category.assoc] using right_unit_coherence f.map.2

private lemma associator_coherence {s t r x y z x' y' z' : C}
    (f : s ⊗ x ⟶ x') (g : t ⊗ y ⟶ y') (h : r ⊗ z ⟶ z') :
    (α_ s t r).hom ▷ ((x ⊗ y) ⊗ z) ≫ (s ⊗ t ⊗ r) ◁ (α_ x y z).hom ≫
      tensorμ s (t ⊗ r) x (y ⊗ z) ≫ (f ⊗ₘ (tensorμ t r y z ≫ (g ⊗ₘ h))) =
    (tensorμ (s ⊗ t) r (x ⊗ y) z ≫ ((tensorμ s t x y ≫ (f ⊗ₘ g)) ⊗ₘ h)) ≫
      (α_ x' y' z').hom := by
  have hf : f ⊗ₘ (tensorμ t r y z ≫ (g ⊗ₘ h)) =
      (s ⊗ x) ◁ tensorμ t r y z ≫ (f ⊗ₘ (g ⊗ₘ h)) := by
    rw [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp]
  have hh : (tensorμ s t x y ≫ (f ⊗ₘ g)) ⊗ₘ h =
      tensorμ s t x y ▷ (r ⊗ z) ≫ ((f ⊗ₘ g) ⊗ₘ h) := by
    rw [← MonoidalCategory.tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  rw [hf, hh]
  simp only [Category.assoc]
  rw [associator_naturality, ← tensorHom_def_assoc, associator_monoidal_assoc]

/-- The associator retains the actual associators in the two original coordinates. -/
def associatorIso (X Y Z : Localization C C) :
    (⟨tensorPair (tensorPair X.obj Y.obj) Z.obj⟩ : Localization C C) ≅
      ⟨tensorPair X.obj (tensorPair Y.obj Z.obj)⟩ :=
  (ActionLocalization.ofFunctor (C := C)).mapIso
    ((α_ X.obj.1 Y.obj.1 Z.obj.1).prod (α_ X.obj.2 Y.obj.2 Z.obj.2))

lemma associatorIso_naturality {X Y Z X' Y' Z' : Localization C C}
    (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z') :
    tensorHom (tensorHom f g) h ≫ (associatorIso X' Y' Z').hom =
      (associatorIso X Y Z).hom ≫ tensorHom f (tensorHom g h) := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      induction h using Quotient.inductionOn with
      | _ h =>
        change ActionLocalization.mkHom (tensorRep (tensorRep f g) h) ≫
          ActionLocalization.ofHom _ =
          ActionLocalization.ofHom _ ≫ ActionLocalization.mkHom (tensorRep f (tensorRep g h))
        rw [ActionLocalization.mkHom_comp_ofHom, ActionLocalization.ofHom_comp_mkHom]
        apply Quotient.sound
        refine ⟨α_ f.denom g.denom h.denom, ?_⟩
        apply Prod.ext
        · exact associator_coherence f.map.1 g.map.1 h.map.1
        · exact associator_coherence f.map.2 g.map.2 h.map.2

/-- The explicit coordinatewise monoidal data before checking its coherence. -/
@[instance_reducible]
def monoidalStruct : MonoidalCategoryStruct (Localization C C) where
  tensorObj X Y := ⟨tensorPair X.obj Y.obj⟩
  tensorHom := tensorHom
  whiskerLeft X _ _ f := tensorHom (𝟙 X) f
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorUnit := unit
  associator := associatorIso
  leftUnitor := leftUnitIso
  rightUnitor := rightUnitIso

instance monoidalCategory : MonoidalCategory (Localization C C) := by
  letI := monoidalStruct (C := C)
  refine MonoidalCategory.ofTensorHom
    (id_tensorHom_id := tensorHom_id)
    (id_tensorHom := fun _ _ _ _ ↦ rfl)
    (tensorHom_id := fun _ _ ↦ rfl)
    (tensorHom_comp_tensorHom := fun f g f' g' ↦ (tensorHom_comp f f' g g').symm)
    (associator_naturality := associatorIso_naturality)
    (leftUnitor_naturality := leftUnitIso_naturality)
    (rightUnitor_naturality := rightUnitIso_naturality)
    (pentagon := ?_) (triangle := ?_)
  · intro W X Y Z
    change tensorHom (ActionLocalization.ofHom _) (𝟙 Z) ≫
      ActionLocalization.ofHom _ ≫ tensorHom (𝟙 W) (ActionLocalization.ofHom _) =
      ActionLocalization.ofHom _ ≫ ActionLocalization.ofHom _
    rw [← ActionLocalization.ofHom_id Z.obj, ← ActionLocalization.ofHom_id W.obj,
      tensorHom_ofHom, tensorHom_ofHom, ← ActionLocalization.ofHom_comp,
      ← ActionLocalization.ofHom_comp, ← ActionLocalization.ofHom_comp]
    apply congrArg ActionLocalization.ofHom
    apply Prod.ext
    · change ((α_ W.obj.1 X.obj.1 Y.obj.1).hom ⊗ₘ 𝟙 Z.obj.1) ≫
        (α_ W.obj.1 (X.obj.1 ⊗ Y.obj.1) Z.obj.1).hom ≫
          (𝟙 W.obj.1 ⊗ₘ (α_ X.obj.1 Y.obj.1 Z.obj.1).hom) =
        (α_ (W.obj.1 ⊗ X.obj.1) Y.obj.1 Z.obj.1).hom ≫
          (α_ W.obj.1 X.obj.1 (Y.obj.1 ⊗ Z.obj.1)).hom
      simpa only [MonoidalCategory.tensorHom_id, id_tensorHom] using
        MonoidalCategory.pentagon W.obj.1 X.obj.1 Y.obj.1 Z.obj.1
    · change ((α_ W.obj.2 X.obj.2 Y.obj.2).hom ⊗ₘ 𝟙 Z.obj.2) ≫
        (α_ W.obj.2 (X.obj.2 ⊗ Y.obj.2) Z.obj.2).hom ≫
          (𝟙 W.obj.2 ⊗ₘ (α_ X.obj.2 Y.obj.2 Z.obj.2).hom) =
        (α_ (W.obj.2 ⊗ X.obj.2) Y.obj.2 Z.obj.2).hom ≫
          (α_ W.obj.2 X.obj.2 (Y.obj.2 ⊗ Z.obj.2)).hom
      simpa only [MonoidalCategory.tensorHom_id, id_tensorHom] using
        MonoidalCategory.pentagon W.obj.2 X.obj.2 Y.obj.2 Z.obj.2
  · intro X Y
    change ActionLocalization.ofHom _ ≫ tensorHom (𝟙 X) (ActionLocalization.ofHom _) =
      tensorHom (ActionLocalization.ofHom _) (𝟙 Y)
    rw [← ActionLocalization.ofHom_id X.obj, ← ActionLocalization.ofHom_id Y.obj,
      tensorHom_ofHom, tensorHom_ofHom, ← ActionLocalization.ofHom_comp]
    apply congrArg ActionLocalization.ofHom
    apply Prod.ext
    · change (α_ X.obj.1 (𝟙_ C) Y.obj.1).hom ≫
        (𝟙 X.obj.1 ⊗ₘ (λ_ Y.obj.1).hom) = ((ρ_ X.obj.1).hom ⊗ₘ 𝟙 Y.obj.1)
      simpa only [MonoidalCategory.tensorHom_id, id_tensorHom] using
        MonoidalCategory.triangle X.obj.1 Y.obj.1
    · change (α_ X.obj.2 (𝟙_ C) Y.obj.2).hom ≫
        (𝟙 X.obj.2 ⊗ₘ (λ_ Y.obj.2).hom) = ((ρ_ X.obj.2).hom ⊗ₘ 𝟙 Y.obj.2)
      simpa only [MonoidalCategory.tensorHom_id, id_tensorHom] using
        MonoidalCategory.triangle X.obj.2 Y.obj.2

/-- Swap the coordinates to obtain an inverse at the level of components. -/
def inverseObject (X : Localization C C) : Localization C C := ⟨X.obj.2, X.obj.1⟩

/-- An actual arrow from the unit to the product with the inverse object.
Its translating object is the tensor product of the two original coordinates. -/
def inverseArrow (X : Localization C C) : unit ⟶ X ⊗ inverseObject X :=
  mkHom (X.obj.1 ⊗ X.obj.2) (ρ_ (X.obj.1 ⊗ X.obj.2)).hom
    ((ρ_ (X.obj.1 ⊗ X.obj.2)).hom ≫ (β_ X.obj.1 X.obj.2).hom)

end CategoryTheory.GroupCompletion.Localization
