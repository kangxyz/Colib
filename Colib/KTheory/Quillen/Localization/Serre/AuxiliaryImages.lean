/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Uses native Q-construction and intrinsic abelian full-subcategory exact structure. -/

public import Colib.CategoryTheory.Abelian.SerreClass.ImageSubobjects
public import Colib.KTheory.Quillen.Localization.Serre.KernelReflection
public import Colib.CategoryTheory.TheoremA.ContractibleStructured
public import Colib.CategoryTheory.Abelian.Devissage.QInclusion

/-! # Images of the auxiliary objects as a genuine ordered base -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.SerreLocalization

open CategoryTheory.Abelian.SerreLocalization CategoryTheory.Abelian
attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{u} C] [Abelian C]

/-- A Q-arrow over the base can only increase the image of its structure map. -/
theorem overQ_image_mono {N : C} {X Y : OverQ N} (f : X ⟶ Y) :
    imageSubobject X.obj.of.hom ≤ imageSubobject Y.obj.of.hom := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  have : Epi s.l.left := s.wl
  rw [← imageSubobject_epi_comp s.l.left X.obj.of.hom, Over.w s.l,
    ← Over.w s.r]
  exact imageSubobject_comp_le s.r.left Y.obj.of.hom

variable (P : ObjectProperty C) [P.IsSerreClass]

/-- The image index category has a genuine terminal object, the whole base. -/
theorem auxiliaryImagePoset_contractible (N : C) :
    ContractibleSpace (ClassifyingSpace (SerreImagePoset P N)) :=
  classifyingSpace_contractible_of_isTerminal (isTerminalTop (α := SerreImagePoset P N))

/-- The image projection is functorial on actual Q-span classes. -/
def auxiliaryImageFunctor (N : C) : AuxiliaryKernel P N ⥤ SerreImagePoset P N where
  obj X := ⟨imageSubobject X.obj.obj.of.hom,
    imageSubobject_arrow_isoModSerre P _ X.property⟩
  map f := homOfLE (overQ_image_mono f.hom)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The full kernel comma for the entire auxiliary category. -/
abbrev AuxiliaryKernelComma (N : C) (T : (abelianExactStructure P.FullSubcategory).QCategory) :=
  CostructuredArrow (auxiliaryKernelFunctor P N) T

/-- The kernel comma has the same concrete image projection. -/
def auxiliaryKernelCommaImageFunctor (N : C)
    (T : (abelianExactStructure P.FullSubcategory).QCategory) :
    AuxiliaryKernelComma P N T ⥤ SerreImagePoset P N :=
  CostructuredArrow.proj _ _ ⋙ auxiliaryImageFunctor P N

end CategoryTheory.ExactCategory.SerreLocalization
