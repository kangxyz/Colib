/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionAction

/-!
Implementation provenance:
`Quillen/Algebra/Category/ModuleCat/FiniteProjectiveExtensionArrows.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Section and retraction coordinates for extension action-category arrows -/
@[expose] public section

open CategoryTheory.GroupCompletion

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalLeftAction
namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal extensionFiberDirectSumAction
open GroupCompletion ActionLocalization

/-- The section specified by a translated isomorphism. -/
def extensionRepSection {C : Category.{u, u} R} {p q : (exactStructure R).ExtensionFiber C}
    (f : HomRep (C := IsoCategory R) p q) : p.of.obj.left ⟶ q.of.obj.left :=
  coprod.inr ≫ f.map.iso.hom.hom.left

/-- The retraction specified by the same translated isomorphism. -/
def extensionRepRetraction {C : Category.{u, u} R} {p q : (exactStructure R).ExtensionFiber C}
    (f : HomRep (C := IsoCategory R) p q) : q.of.obj.left ⟶ p.of.obj.left :=
  f.map.iso.inv.hom.left ≫ coprod.desc 0 (𝟙 _)

/-- Section coordinates do not depend on the translating representative. -/
theorem extensionRepSection_rel {C : Category.{u, u} R}
    {p q : (exactStructure R).ExtensionFiber C} {f g : HomRep (C := IsoCategory R) p q}
    (h : HomRep.Rel f g) : extensionRepSection R f = extensionRepSection R g := by
  obtain ⟨e, he⟩ := h
  have h' := congrArg (fun k => coprod.inr ≫ k.iso.hom.hom.left) he
  change coprod.inr ≫ (coprod.map e.hom.iso.hom (𝟙 _) ≫ g.map.iso.hom.hom.left) =
    coprod.inr ≫ f.map.iso.hom.hom.left at h'
  simpa [extensionRepSection] using h'.symm

/-- Retraction coordinates do not depend on the translating representative. -/
theorem extensionRepRetraction_rel {C : Category.{u, u} R}
    {p q : (exactStructure R).ExtensionFiber C} {f g : HomRep (C := IsoCategory R) p q}
    (h : HomRep.Rel f g) : extensionRepRetraction R f = extensionRepRetraction R g := by
  obtain ⟨e, he⟩ := h
  have h' := congrArg (fun k => k.iso.inv.hom.left ≫ coprod.desc 0 (𝟙 _)) he
  change (g.map.iso.inv.hom.left ≫ coprod.map e.hom.iso.inv (𝟙 _)) ≫
    coprod.desc 0 (𝟙 _) = f.map.iso.inv.hom.left ≫ coprod.desc 0 (𝟙 _) at h'
  simpa [extensionRepRetraction, Category.assoc] using h'.symm

/-- The actual section coordinate of an action-category arrow. -/
def extensionActionSection {C : Category.{u, u} R} {p q : ExtensionActionCategory R C}
    (f : p ⟶ q) : p.obj.of.obj.left ⟶ q.obj.of.obj.left :=
  Quotient.lift (extensionRepSection R) (fun _ _ h => extensionRepSection_rel R h) f

/-- The actual retraction coordinate of an action-category arrow. -/
def extensionActionRetraction {C : Category.{u, u} R} {p q : ExtensionActionCategory R C}
    (f : p ⟶ q) : q.obj.of.obj.left ⟶ p.obj.of.obj.left :=
  Quotient.lift (extensionRepRetraction R) (fun _ _ h => extensionRepRetraction_rel R h) f

/-- Section coordinates compose in the original direction. -/
@[simp]
theorem extensionActionSection_comp {C : Category.{u, u} R}
    {p q r : ExtensionActionCategory R C} (f : p ⟶ q) (g : q ⟶ r) :
    extensionActionSection R (f ≫ g) = extensionActionSection R f ≫ extensionActionSection R g := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      change coprod.inr ≫ ((coprod.associator g.denom.of f.denom.of p.obj.of.obj.left).hom ≫
        coprod.map (𝟙 _) f.map.iso.hom.hom.left ≫ g.map.iso.hom.hom.left) =
        (coprod.inr ≫ f.map.iso.hom.hom.left) ≫ (coprod.inr ≫ g.map.iso.hom.hom.left)
      simp [Category.assoc]

/-- Retraction coordinates compose in the opposite direction. -/
@[simp]
theorem extensionActionRetraction_comp {C : Category.{u, u} R}
    {p q r : ExtensionActionCategory R C} (f : p ⟶ q) (g : q ⟶ r) :
    extensionActionRetraction R (f ≫ g) =
      extensionActionRetraction R g ≫ extensionActionRetraction R f := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g =>
      change (g.map.iso.inv.hom.left ≫ coprod.map (𝟙 _) f.map.iso.inv.hom.left ≫
        (coprod.associator g.denom.of f.denom.of p.obj.of.obj.left).inv) ≫
        coprod.desc 0 (𝟙 _) =
        (g.map.iso.inv.hom.left ≫ coprod.desc 0 (𝟙 _)) ≫
          (f.map.iso.inv.hom.left ≫ coprod.desc 0 (𝟙 _))
      simp [Category.assoc, coprod.desc_comp]

/-- An original extension isomorphism has its own map as section coordinate. -/
@[simp]
theorem extensionActionSection_ofHom {C : Category.{u, u} R}
    {p q : (exactStructure R).ExtensionFiber C} (f : p ⟶ q) :
    extensionActionSection R
      (GroupCompletion.ActionLocalization.ofHom (C := IsoCategory R) f) = f.iso.hom.hom.left := by
  change coprod.inr ≫ ((coprod.leftUnitor p.of.obj.left).hom ≫ f.iso.hom.hom.left) = _
  simp

/-- An original extension isomorphism has its inverse as retraction coordinate. -/
@[simp]
theorem extensionActionRetraction_ofHom {C : Category.{u, u} R}
    {p q : (exactStructure R).ExtensionFiber C} (f : p ⟶ q) :
    extensionActionRetraction R
      (GroupCompletion.ActionLocalization.ofHom (C := IsoCategory R) f) = f.iso.inv.hom.left := by
  change (f.iso.inv.hom.left ≫ (coprod.leftUnitor p.of.obj.left).inv) ≫
    coprod.desc 0 (𝟙 _) = _
  simp

/-- The identity arrow has identity section. -/
@[simp]
theorem extensionActionSection_id {C : Category.{u, u} R} (p : ExtensionActionCategory R C) :
    extensionActionSection R (𝟙 p) = 𝟙 p.obj.of.obj.left := by
  change coprod.inr ≫ (coprod.leftUnitor p.obj.of.obj.left).hom = _
  simp

/-- The identity arrow has identity retraction. -/
@[simp]
theorem extensionActionRetraction_id {C : Category.{u, u} R} (p : ExtensionActionCategory R C) :
    extensionActionRetraction R (𝟙 p) = 𝟙 p.obj.of.obj.left := by
  change (coprod.leftUnitor p.obj.of.obj.left).inv ≫ coprod.desc 0 (𝟙 _) = _
  simp

/-- Section coordinates preserve the original fixed quotient. -/
@[reassoc (attr := simp)]
theorem extensionActionSection_w {C : Category.{u, u} R}
    {p q : ExtensionActionCategory R C} (f : p ⟶ q) :
    extensionActionSection R f ≫ q.obj.of.obj.hom = p.obj.of.obj.hom := by
  induction f using Quotient.inductionOn with
  | _ f =>
    change (coprod.inr ≫ f.map.iso.hom.hom.left) ≫ q.obj.of.obj.hom = _
    rw [Category.assoc, Over.w]
    change coprod.inr ≫ coprod.desc 0 p.obj.of.obj.hom = _
    exact coprod.inr_desc _ _

/-- Retraction coordinates also preserve the original fixed quotient. -/
@[reassoc (attr := simp)]
theorem extensionActionRetraction_w {C : Category.{u, u} R}
    {p q : ExtensionActionCategory R C} (f : p ⟶ q) :
    extensionActionRetraction R f ≫ p.obj.of.obj.hom = q.obj.of.obj.hom := by
  induction f using Quotient.inductionOn with
  | _ f =>
    change (f.map.iso.inv.hom.left ≫ coprod.desc 0 (𝟙 _)) ≫ p.obj.of.obj.hom = _
    simp only [Category.assoc, coprod.desc_comp, zero_comp, Category.id_comp]
    exact Over.w f.map.iso.inv.hom

private theorem coprod_total (A B : Category.{u, u} R) :
    coprod.desc (𝟙 A) (0 : B ⟶ A) ≫ coprod.inl +
      coprod.desc (0 : A ⟶ B) (𝟙 B) ≫ coprod.inr = 𝟙 (A ⨿ B) := by
  apply coprod.hom_ext <;> simp [Preadditive.comp_add]

/-- A coproduct map which has zero second projection factors through its first
summand by the actual additive coproduct decomposition. -/
private theorem factor_coprod_inl {A B W : Category.{u, u} R} (h : W ⟶ A ⨿ B)
    (hh : h ≫ coprod.desc 0 (𝟙 B) = 0) :
    h ≫ coprod.desc (𝟙 A) 0 ≫ coprod.inl = h := by
  have ht := congrArg (fun k => h ≫ k) (coprod_total R A B)
  simpa only [Preadditive.comp_add, ← Category.assoc, hh, zero_comp, add_zero,
    Category.comp_id] using ht

/-- The section and retraction together determine the represented arrow.
No choice of a kernel complement is retained in the resulting equality. -/
theorem extensionRep_rel_of_coordinates {C : Category.{u, u} R}
    {p q : (exactStructure R).ExtensionFiber C} (f g : HomRep (C := IsoCategory R) p q)
    (hs : extensionRepSection R f = extensionRepSection R g)
    (hr : extensionRepRetraction R f = extensionRepRetraction R g) : HomRep.Rel f g := by
  let ef : f.denom.of ⨿ p.of.obj.left ≅ q.of.obj.left :=
    ((exactStructure R).extensionMiddle C).mapIso f.map.iso
  let eg : g.denom.of ⨿ p.of.obj.left ≅ q.of.obj.left :=
    ((exactStructure R).extensionMiddle C).mapIso g.map.iso
  change coprod.inr ≫ ef.hom = coprod.inr ≫ eg.hom at hs
  change ef.inv ≫ coprod.desc 0 (𝟙 _) = eg.inv ≫ coprod.desc 0 (𝟙 _) at hr
  let h := ef ≪≫ eg.symm
  have hs' : coprod.inr ≫ h.hom = (coprod.inr : p.of.obj.left ⟶ g.denom.of ⨿ p.of.obj.left) := by
    have hh := congrArg (fun k => k ≫ eg.inv) hs
    simpa only [h, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id, Category.comp_id] using hh
  have hr' : h.hom ≫ coprod.desc 0 (𝟙 _) =
      (coprod.desc 0 (𝟙 _) : f.denom.of ⨿ p.of.obj.left ⟶ p.of.obj.left) := by
    have hh := congrArg (fun k => ef.hom ≫ k) hr
    simpa only [h, Iso.trans_hom, Iso.symm_hom, ← Category.assoc,
      Iso.hom_inv_id, Category.id_comp] using hh.symm
  have hs'' : coprod.inr ≫ h.inv = (coprod.inr : p.of.obj.left ⟶ f.denom.of ⨿ p.of.obj.left) := by
    have hh := congrArg (fun k => k ≫ h.inv) hs'
    simpa [Category.assoc] using hh.symm
  have hr'' : h.inv ≫ coprod.desc 0 (𝟙 _) =
      (coprod.desc 0 (𝟙 _) : g.denom.of ⨿ p.of.obj.left ⟶ p.of.obj.left) := by
    have hh := congrArg (fun k => h.inv ≫ k) hr'
    simpa [← Category.assoc] using hh.symm
  let a : f.denom.of ⟶ g.denom.of := coprod.inl ≫ h.hom ≫ coprod.desc (𝟙 _) 0
  let b : g.denom.of ⟶ f.denom.of := coprod.inl ≫ h.inv ≫ coprod.desc (𝟙 _) 0
  have ha : a ≫ coprod.inl = coprod.inl ≫ h.hom := by
    exact factor_coprod_inl R (coprod.inl ≫ h.hom) (by simp [Category.assoc, hr'])
  have hb : b ≫ coprod.inl = coprod.inl ≫ h.inv := by
    exact factor_coprod_inl R (coprod.inl ≫ h.inv) (by simp [Category.assoc, hr''])
  have hab : a ≫ b = 𝟙 _ := by
    dsimp only [b]
    rw [← Category.assoc, ha, Category.assoc]
    simp
  have hba : b ≫ a = 𝟙 _ := by
    dsimp only [a]
    rw [← Category.assoc, hb, Category.assoc]
    simp
  refine ⟨Core.isoMk ⟨a, b, hab, hba⟩, ?_⟩
  apply extensionFiber_hom_ext R
  change coprod.map a (𝟙 _) ≫ g.map.iso.hom.hom.left = f.map.iso.hom.hom.left
  have hmap : coprod.map a (𝟙 _) = h.hom := by
    apply coprod.hom_ext
    · simpa using ha
    · simpa using hs'.symm
  rw [hmap]
  change (ef.hom ≫ eg.inv) ≫ eg.hom = ef.hom
  simp

/-- Equality of action-category arrows is detected jointly by section and retraction. -/
theorem extensionAction_hom_ext {C : Category.{u, u} R}
    {p q : ExtensionActionCategory R C} {f g : p ⟶ q}
    (hs : extensionActionSection R f = extensionActionSection R g)
    (hr : extensionActionRetraction R f = extensionActionRetraction R g) : f = g := by
  induction f using Quotient.inductionOn with
  | _ f =>
    induction g using Quotient.inductionOn with
    | _ g => exact Quotient.sound (extensionRep_rel_of_coordinates R f g hs hr)

end ModuleCat.FiniteProjective
