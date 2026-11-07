/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
The ordinary categorical geometry uses native Mathlib maps and independent universes. -/

public import Colib.CategoryTheory.Abelian.SerreClass.OverKernel
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Abelian.SerreClass.MorphismProperty

/-!
# Ordinary image subobjects and Serre support

Epi precomposition retains the image subobject. Serre-isomorphism images retain
the original Serre support property and top subobject. Base change to an actual
subobject of an image gives the original epimorphic pullback projection.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Abelian.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Epi precomposition leaves the image subobject unchanged in an abelian category. -/
lemma imageSubobject_epi_comp {X Y Z : C} (p : X ⟶ Y) [Epi p] (f : Y ⟶ Z) :
    imageSubobject (p ≫ f) = imageSubobject f := by
  let a := Subobject.ofLE _ _ (imageSubobject_comp_le p f)
  have : IsIso a := isIso_of_mono_of_epi a
  exact Subobject.eq_of_comm (asIso a) (Subobject.ofLE_arrow _)

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- The actual image inclusion of a Serre-isomorphism is again a Serre-isomorphism. -/
theorem imageSubobject_arrow_isoModSerre {X N : C} (f : X ⟶ N) (hf : P.isoModSerre f) :
    P.isoModSerre (imageSubobject f).arrow := by
  apply P.isoModSerre_of_mono
  exact P.prop_of_epi (cokernel.map f (imageSubobject f).arrow
    (factorThruImageSubobject f) (𝟙 _) (by simp)) hf.2

/-- Subobjects of the fixed base whose cokernel belongs to the Serre class. -/
abbrev SerreImagePoset (N : C) := { I : Subobject N // P.isoModSerre I.arrow }

instance instOrderTopSerreImagePoset (N : C) : OrderTop (SerreImagePoset P N) where
  top := ⟨⊤, P.isoModSerre_of_isIso _⟩
  le_top I := show I.val ≤ (⊤ : Subobject N) from le_top

/-- Base change to a subobject contained in the image is epimorphic. -/
theorem pullback_to_image_epi {N : C} (X : Over N) (I : Subobject N)
    (hI : I ≤ imageSubobject X.hom) : Epi (pullback.snd X.hom I.arrow) := by
  let t := Subobject.ofLE I (imageSubobject X.hom) hI
  have ht : t ≫ (imageSubobject X.hom).arrow = I.arrow := Subobject.ofLE_arrow _
  have hw : pullback.fst X.hom I.arrow ≫ factorThruImageSubobject X.hom =
      pullback.snd X.hom I.arrow ≫ t := by
    apply (cancel_mono (imageSubobject X.hom).arrow).1
    rw [Category.assoc, imageSubobject_arrow_comp, Category.assoc, ht, pullback.condition]
  have hs : IsPullback (pullback.fst X.hom I.arrow) (pullback.snd X.hom I.arrow)
      (factorThruImageSubobject X.hom) t := by
    apply IsPullback.mk' hw
    · intro Z a b ha hb
      exact pullback.hom_ext ha hb
    · intro Z a b h
      have h' : a ≫ X.hom = b ≫ I.arrow := by
        rw [← imageSubobject_arrow_comp X.hom, ← ht, ← Category.assoc, h, Category.assoc]
      exact ⟨pullback.lift a b h', pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  exact MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C) hs inferInstance

end CategoryTheory.Abelian.SerreLocalization
