/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveMonoidal
public import Colib.CategoryTheory.GroupCompletion.DiagonalAction
public import Colib.KTheory.GrothendieckGroup.Basic
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
Implementation provenance:
`Quillen/KTheory/Plus/ProjectiveGroupCompletion.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Projective group completion and its original Grothendieck grading

This is the actual Grayson category on the direct-sum isomorphism groupoid of
finite projective modules. Its grading takes `(A, B)` to `[B] - [A]` in the
existing exact-category Grothendieck group. Every translated representative
preserves that value. No assertion about path components or plus acyclicity
is made here, and the original Quillen K-groups are not redefined.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

namespace ModuleCat.FiniteProjective
variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric

/-- The original isomorphism groupoid localized under simultaneous direct sums. -/
def GroupCompletionCategory := GroupCompletion.Localization (IsoCategory R) (IsoCategory R)

/-- The ring construction uses its specified direct-sum action, without requiring
callers to install a monoidal structure on the projective module category. -/
instance groupCompletionCategory : CategoryTheory.Category (GroupCompletionCategory R) :=
  inferInstanceAs (CategoryTheory.Category
    (GroupCompletion.Localization (IsoCategory R) (IsoCategory R)))

/-- The object represented by a denominator and numerator projective module. -/
abbrev completionPair (A B : IsoCategory R) : GroupCompletionCategory R := ⟨(A, B)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The original groupoid enters group completion with the monoidal unit denominator. -/
def completionUnit : IsoCategory R ⥤ GroupCompletionCategory R where
  obj P := completionPair R (𝟙_ (IsoCategory R)) P
  map f := GroupCompletion.ActionLocalization.ofHom (𝟙 _, f)
  map_id _ := GroupCompletion.ActionLocalization.ofHom_id _
  map_comp f g := by
    simpa only [prod_comp, Category.id_comp] using
      (GroupCompletion.ActionLocalization.ofHom_comp
        (C := IsoCategory R) (D := IsoCategory R × IsoCategory R)
        (Prod.mkHom (𝟙 (𝟙_ (IsoCategory R))) f) (Prod.mkHom (𝟙 _) g))

/-- A projective class in the preexisting Grothendieck group. -/
def coreClass (P : IsoCategory R) : (exactStructure R).GrothendieckGroup :=
  (exactStructure R).grothendieckClass P.of

/-- The direct-sum monoidal product has its original additive object class. -/
theorem coreClass_tensor (P Q : IsoCategory R) :
    coreClass R (P ⊗ Q) = coreClass R P + coreClass R Q := by
  change (exactStructure R).grothendieckClass (P.of ⨿ Q.of) = _
  rw [← (exactStructure R).grothendieckClass_iso (biprod.isoCoprod P.of Q.of)]
  exact (exactStructure R).grothendieckClass_additive
    ((exactStructure R).conflation_biprod_inl_snd P.of Q.of)

/-- The actual monoidal unit has zero object class. -/
@[simp] theorem coreClass_unit : coreClass R (𝟙_ (IsoCategory R)) = 0 := by
  change (exactStructure R).grothendieckClass _ = 0
  rw [(exactStructure R).grothendieckClass_iso (freeIsoZero R).hom.iso]
  exact (exactStructure R).grothendieckClass_of_isZero free_zero_isZero

/-- The virtual class, with numerator minus denominator in the existing group. -/
def completionGrade (X : GroupCompletionCategory R) : (exactStructure R).GrothendieckGroup :=
  coreClass R X.obj.2 - coreClass R X.obj.1

/-- Every actual quotient arrow preserves the virtual class. -/
theorem completionGrade_map {X Y : GroupCompletionCategory R} (f : X ⟶ Y) :
    completionGrade R X = completionGrade R Y := by
  obtain ⟨h, rfl⟩ := GroupCompletion.ActionLocalization.mkHom_surjective X.obj Y.obj f
  have h₁ := (exactStructure R).grothendieckClass_iso h.map.1.iso
  have h₂ := (exactStructure R).grothendieckClass_iso h.map.2.iso
  change coreClass R (h.denom ⊗ X.obj.1) = coreClass R Y.obj.1 at h₁
  change coreClass R (h.denom ⊗ X.obj.2) = coreClass R Y.obj.2 at h₂
  rw [coreClass_tensor] at h₁ h₂
  dsimp [completionGrade]
  rw [← h₁, ← h₂]
  abel

/-- Grading is a genuine functor to the discrete original Grothendieck group. -/
def completionGrading :
    GroupCompletionCategory R ⥤ Discrete (exactStructure R).GrothendieckGroup where
  obj X := Discrete.mk (completionGrade R X)
  map f := Discrete.eqToHom (completionGrade_map R f)

/-- The canonical entrance has precisely the original projective object class. -/
@[simp] theorem completionGrade_unit_obj (P : IsoCategory R) :
    completionGrade R ((completionUnit R).obj P) = coreClass R P := by
  simp [completionGrade, completionUnit]

/-- Diagonal pairs represent the zero virtual class. -/
@[simp] theorem completionGrade_diagonal (P : IsoCategory R) :
    completionGrade R (completionPair R P P) = 0 := by
  simp [completionGrade]

/-- Simultaneously adding an actual projective summand does not change the grade. -/
theorem completionGrade_translate (P A B : IsoCategory R) :
    completionGrade R (completionPair R (P ⊗ A) (P ⊗ B)) =
      completionGrade R (completionPair R A B) := by
  simp only [completionGrade, coreClass_tensor]
  abel

/-- The original diagonal pair has an actual arrow from the chosen zero pair. -/
def completionDiagonalArrow (P : IsoCategory R) :
    completionPair R (𝟙_ _) (𝟙_ _) ⟶ completionPair R P P :=
  GroupCompletion.Localization.mkHom P (ρ_ P).hom (ρ_ P).hom

end ModuleCat.FiniteProjective
