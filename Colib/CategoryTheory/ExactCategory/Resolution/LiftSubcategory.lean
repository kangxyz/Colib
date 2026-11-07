/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Resolution.Finite
public import Colib.CategoryTheory.ExactCategory.Subcategory
public import Colib.CategoryTheory.ExactCategory.KernelClosed

/-!
# Lifting actual finite resolutions to an exact full subcategory

If the resolving objects belong to a kernel-closed exact subcategory, a finite
resolution of an object of that subcategory lifts term by term. Every syzygy
and every arrow is retained. The length is unchanged.

This elementary construction supplies the categorical step from a finite
resolution of module sheaves to a finite resolution of coherent sheaves.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.ExactStructure.FiniteResolution

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {E : ExactStructure C} {P Q : ObjectProperty C}
  [Q.ContainsZero] [Q.IsClosedUnderIsomorphisms] [Q.IsClosedUnderFiniteProducts]
  [E.IsExtensionClosed Q] [E.IsKernelClosed Q]
  (hPQ : ∀ X, P X → Q X)

/-- Lift a finite resolution without changing any ambient object or morphism. -/
def liftToSubcategory : ∀ {X : C}, E.FiniteResolution P X → (hX : Q X) →
    (ExactSubcategory.exactStructure E Q).FiniteResolution
      (fun Y => P Y.obj) ⟨X, hX⟩
  | _, .of_mem hP, _ => .of_mem hP
  | _, .step S hS hP R, hX => by
    have h₂ : Q S.X₂ := hPQ _ hP
    have h₁ : Q S.X₁ := ExactStructure.IsKernelClosed.prop_kernel hS h₂ hX
    let T : ShortComplex Q.FullSubcategory :=
      ShortComplex.mk
        (Q.homMk (X := ⟨S.X₁, h₁⟩) (Y := ⟨S.X₂, h₂⟩) S.f)
        (Q.homMk (X := ⟨S.X₂, h₂⟩) (Y := ⟨S.X₃, hX⟩) S.g)
        (ObjectProperty.hom_ext _ S.zero)
    exact .step T hS hP (liftToSubcategory R h₁)

@[simp]
theorem length_liftToSubcategory {X : C} (R : E.FiniteResolution P X) (hX : Q X) :
    (R.liftToSubcategory hPQ hX).length = R.length := by
  induction R with
  | of_mem hP => rfl
  | step S hS hP R ih => simp only [liftToSubcategory, length_step, ih]

end CategoryTheory.ExactCategory.ExactStructure.FiniteResolution

attribute [colib_tag "COL-0271",
  colib_ref "WeibelKBook" "V, Resolution Theorem 3.1, page 20" "background"
    "Actual finite admissible resolutions; bounded-complex extraction and \
    full-subcategory lifting are proved here"]
  CategoryTheory.ExactCategory.ExactStructure.FiniteResolution.liftToSubcategory
  CategoryTheory.ExactCategory.ExactStructure.FiniteResolution.length_liftToSubcategory
