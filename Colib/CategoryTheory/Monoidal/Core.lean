/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Monoidal.Transport
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Monoidal/Core.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Monoidal structures on the core of a category

The core retains the original tensor objects and coherent isomorphisms. The
faithful inclusion transports the monoidal laws, rather than requiring a strict
monoidal category. Braiding and symmetry are inherited from the same inclusion.
-/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory MonoidalCategory

namespace CategoryTheory.Core
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Tensor isomorphisms define tensoring on the actual categorical core. -/
@[instance_reducible]
def monoidalStruct : MonoidalCategoryStruct (Core C) where
  tensorObj X Y := ⟨X.of ⊗ Y.of⟩
  tensorHom f g := ⟨f.iso ⊗ᵢ g.iso⟩
  whiskerLeft X _ _ g := ⟨whiskerLeftIso X.of g.iso⟩
  whiskerRight f X := ⟨whiskerRightIso f.iso X.of⟩
  tensorUnit := ⟨𝟙_ C⟩
  associator X Y Z := isoMk (α_ X.of Y.of Z.of)
  leftUnitor X := isoMk (λ_ X.of)
  rightUnitor X := isoMk (ρ_ X.of)

attribute [local instance] monoidalStruct

/-- The inclusion preserves all tensor data without changing objects or arrows. -/
def monoidalInducingData : Monoidal.InducingFunctorData (inclusion C) where
  μIso _ _ := Iso.refl _
  εIso := Iso.refl _
  whiskerLeft_eq := by intros; simp +instances [monoidalStruct, inclusion]
  whiskerRight_eq _ _ := by simp +instances [monoidalStruct, inclusion]
  tensorHom_eq _ _ := by simp +instances [monoidalStruct, inclusion]
  associator_eq _ _ _ := by simp +instances [monoidalStruct, inclusion]
  leftUnitor_eq _ := by simp +instances [monoidalStruct, inclusion]
  rightUnitor_eq _ := by simp +instances [monoidalStruct, inclusion]

/-- The core inherits the original, potentially non-strict monoidal structure. -/
instance monoidalCategory : MonoidalCategory (Core C) :=
  Monoidal.induced (inclusion C) monoidalInducingData

/-- The original faithful inclusion is a strong monoidal functor. -/
instance inclusionMonoidal : (inclusion C).Monoidal :=
  Monoidal.fromInducedMonoidal (inclusion C) monoidalInducingData

/-- The braiding is the original braiding, regarded as a core isomorphism. -/
instance braidedCategory [BraidedCategory C] : BraidedCategory (Core C) :=
  .ofFaithful (inclusion C) (fun X Y => isoMk (β_ X.of Y.of)) (by
    intro X Y
    change 𝟙 _ ≫ (β_ X.of Y.of).hom = (β_ X.of Y.of).hom ≫ 𝟙 _
    simp)

/-- The core inclusion preserves the original braiding. -/
instance inclusionBraided [BraidedCategory C] : (inclusion C).Braided where
  braided X Y := by
    change 𝟙 _ ≫ (β_ X.of Y.of).hom = (β_ X.of Y.of).hom ≫ 𝟙 _
    simp

/-- Symmetry is reflected by the faithful inclusion. -/
instance symmetricCategory [SymmetricCategory C] : SymmetricCategory (Core C) :=
  .ofFaithful (inclusion C)

end CategoryTheory.Core
