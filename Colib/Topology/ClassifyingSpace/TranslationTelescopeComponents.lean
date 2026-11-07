/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.TranslationTelescopeShift
public import Colib.CategoryTheory.Monoidal.TranslationTelescopeCoherence
public import Colib.Topology.ClassifyingSpace.Connectivity
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
Adapted from the same-named Quillen source at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original
component relation and objectwise braiding.

# Component comparison for the original precompletion translations

The braiding below is used objectwise. It does not assert a natural
transformation of telescope maps or a homotopy equivalence of left translations.
-/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace CategoryTheory.MonoidalCategory.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- At each telescope object the braiding joins the original left and right maps. -/
def generatorComparison (e : C) (X : Model e) :
    (leftTranslation e e).obj X ⟶ (rightStabilization e).obj X :=
  (modelEquivalence e).inverse.map
    ((Grothendieck.ι (Grothendieck.EndofunctorTelescope.diagram (tensorRight e)) X.base).map
      (β_ e ((modelEquivalence e).functor.obj X).fiber).hom)

/-- Objectwise comparison suffices for equality on path components. -/
theorem generator_joined_rightStabilization (e : C) (x : ClassifyingSpace (Model e)) :
    Joined (classifyingSpaceMap (leftTranslation e e) x)
      (classifyingSpaceMap (rightStabilization e) x) := by
  obtain ⟨X, hX⟩ := classifyingSpace_joined_vertex x
  have h := hX.map (classifyingSpaceMap (leftTranslation e e)).hom.continuous
  have k := hX.map (classifyingSpaceMap (rightStabilization e)).hom.continuous
  apply h.symm.trans
  apply Joined.trans (y := classifyingSpaceMap (rightStabilization e) (classifyingSpacePoint X))
  · simpa only [classifyingSpaceMap_point] using
      (show Joined _ _ from ⟨classifyingSpacePath (generatorComparison e X)⟩)
  · exact k

/-- Generator left translation reflects components via right stabilization. -/
theorem generator_joined_iff (e : C) (x y : ClassifyingSpace (Model e)) :
    Joined (classifyingSpaceMap (leftTranslation e e) x)
      (classifyingSpaceMap (leftTranslation e e) y) ↔ Joined x y := by
  constructor
  · intro h
    apply (rightStabilization_joined_iff e x y).mp
    exact (generator_joined_rightStabilization e x).symm.trans
      (h.trans (generator_joined_rightStabilization e y))
  · exact fun h ↦ h.map (classifyingSpaceMap (leftTranslation e e)).hom.continuous

/-- Generator left translation reaches every component. -/
theorem exists_joined_generator (e : C) (y : ClassifyingSpace (Model e)) :
    ∃ x, Joined (classifyingSpaceMap (leftTranslation e e) x) y := by
  obtain ⟨x, hx⟩ := exists_joined_rightStabilization e y
  exact ⟨x, (generator_joined_rightStabilization e x).trans hx⟩

omit [BraidedCategory C] in
/-- The actual parameter isomorphism supplies component comparison. -/
theorem leftTranslation_iso_joined (e : C) {P Q : C} (f : P ≅ Q)
    (x : ClassifyingSpace (Model e)) :
    Joined (classifyingSpaceMap (leftTranslation e P) x)
      (classifyingSpaceMap (leftTranslation e Q) x) :=
  ⟨(classifyingSpaceNaturalTransformationHomotopy (leftTranslationIso e f).hom).evalAt x⟩

omit [BraidedCategory C] in
/-- The original associator gives the component-level composition law. -/
theorem leftTranslation_tensor_joined (e P Q : C) (x : ClassifyingSpace (Model e)) :
    Joined (classifyingSpaceMap (leftTranslation e (P ⊗ Q)) x)
      (classifyingSpaceMap (leftTranslation e P)
        (classifyingSpaceMap (leftTranslation e Q) x)) := by
  have h := (classifyingSpaceNaturalTransformationHomotopy
    (leftTranslationTensor e P Q).hom).evalAt x
  simpa only [classifyingSpaceMap_comp, TopCat.comp_app] using (show Joined _ _ from ⟨h⟩)

omit [BraidedCategory C] in
/-- The original unit transformation joins unit translation to the identity. -/
theorem leftTranslation_unit_joined (e : C) (x : ClassifyingSpace (Model e)) :
    Joined (classifyingSpaceMap (leftTranslation e (𝟙_ C)) x) x := by
  have h := (classifyingSpaceNaturalTransformationHomotopy (leftTranslationUnit e).hom).evalAt x
  simpa only [classifyingSpaceMap_id, TopCat.id_app] using (show Joined _ _ from ⟨h⟩)

omit [BraidedCategory C] in
/-- Component reflection is closed under the original tensor composition. -/
theorem leftTranslation_tensor_reflects_joined (e P Q : C)
    (hP : ∀ x y : ClassifyingSpace (Model e),
      Joined (classifyingSpaceMap (leftTranslation e P) x)
        (classifyingSpaceMap (leftTranslation e P) y) → Joined x y)
    (hQ : ∀ x y : ClassifyingSpace (Model e),
      Joined (classifyingSpaceMap (leftTranslation e Q) x)
        (classifyingSpaceMap (leftTranslation e Q) y) → Joined x y)
    (x y : ClassifyingSpace (Model e))
    (h : Joined (classifyingSpaceMap (leftTranslation e (P ⊗ Q)) x)
      (classifyingSpaceMap (leftTranslation e (P ⊗ Q)) y)) : Joined x y := by
  apply hQ
  apply hP
  exact (leftTranslation_tensor_joined e P Q x).symm.trans
    (h.trans (leftTranslation_tensor_joined e P Q y))

omit [BraidedCategory C] in
/-- Component surjectivity is closed under the original tensor composition. -/
theorem leftTranslation_tensor_surjective_components (e P Q : C)
    (hP : ∀ y : ClassifyingSpace (Model e),
      ∃ x, Joined (classifyingSpaceMap (leftTranslation e P) x) y)
    (hQ : ∀ y : ClassifyingSpace (Model e),
      ∃ x, Joined (classifyingSpaceMap (leftTranslation e Q) x) y)
    (y : ClassifyingSpace (Model e)) :
    ∃ x, Joined (classifyingSpaceMap (leftTranslation e (P ⊗ Q)) x) y := by
  obtain ⟨z, hz⟩ := hP y
  obtain ⟨x, hx⟩ := hQ z
  exact ⟨x, (leftTranslation_tensor_joined e P Q x).trans
    ((hx.map (classifyingSpaceMap (leftTranslation e P)).hom.continuous).trans hz)⟩

/-- Reflection descends from a complementary tensor summand by objectwise braiding. -/
theorem leftTranslation_reflects_joined_of_complement (e P Q K : C) (f : P ⊗ Q ≅ K)
    (hK : ∀ x y : ClassifyingSpace (Model e),
      Joined (classifyingSpaceMap (leftTranslation e K) x)
        (classifyingSpaceMap (leftTranslation e K) y) → Joined x y)
    (x y : ClassifyingSpace (Model e))
    (h : Joined (classifyingSpaceMap (leftTranslation e P) x)
      (classifyingSpaceMap (leftTranslation e P) y)) : Joined x y := by
  apply hK
  have hx := leftTranslation_iso_joined e ((β_ Q P) ≪≫ f) x
  have hy := leftTranslation_iso_joined e ((β_ Q P) ≪≫ f) y
  exact hx.symm.trans ((leftTranslation_tensor_joined e Q P x).trans
    ((h.map (classifyingSpaceMap (leftTranslation e Q)).hom.continuous).trans
      ((leftTranslation_tensor_joined e Q P y).symm.trans hy)))

omit [BraidedCategory C] in
/-- Surjectivity on components descends from the actual complementary tensor sum. -/
theorem leftTranslation_surjective_components_of_complement
    (e P Q K : C) (f : P ⊗ Q ≅ K)
    (hK : ∀ y : ClassifyingSpace (Model e),
      ∃ x, Joined (classifyingSpaceMap (leftTranslation e K) x) y)
    (y : ClassifyingSpace (Model e)) :
    ∃ x, Joined (classifyingSpaceMap (leftTranslation e P) x) y := by
  obtain ⟨x, hx⟩ := hK y
  refine ⟨classifyingSpaceMap (leftTranslation e Q) x, ?_⟩
  exact (leftTranslation_tensor_joined e P Q x).symm.trans
    ((leftTranslation_iso_joined e f x).trans hx)

end CategoryTheory.MonoidalCategory.TranslationTelescope
