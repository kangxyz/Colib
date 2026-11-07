/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.SplitSequence
public import Colib.CategoryTheory.Waldhausen.Cofinality.Grading

/-! # Actual common-complement relations for a dense cofiber-closed subcategory

Density supplies actual coproduct complements. Original weak invariance and
extension/cofiber closure, including the chosen zero, construct the common
complement relation without a K-zero or cofinality conclusion as a premise.

Implementation provenance: `Quillen/Waldhausen/Cofinality/DenseSubcategory.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
maps, hypotheses and independent object/hom universes are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.Cofinality
variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C]
  (P : ObjectProperty C)

/-- Concrete closure and density properties of the original full subcategory. -/
structure DenseCofiberData : Prop where
  zero : P W.zero
  weak {A B : C} (f : A ⟶ B) : W.weq f → (P A ↔ P B)
  extension {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q} : W.cof i →
    IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q) → P A → P Q → P B
  quotient {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q} : W.cof i →
    IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q) → P A → P B → P Q
  complement (A : C) : ∃ B : C, P (A ⨿ B)

namespace DenseCofiberData
variable {W P} (h : DenseCofiberData W P)
include h

/-- Closure retains the actual source and target of any original isomorphism. -/
theorem iso_iff {A B : C} (e : A ≅ B) : P A ↔ P B := h.weak e.hom (W.weq_iso _ inferInstance)

/-- Actual split cofiber sequences give coproduct closure. -/
theorem coprod_mem {A B : C} (hA : P A) (hB : P B) : P (A ⨿ B) :=
  h.extension (Additivity.coprod_inr_cof W A B) (Additivity.coprod_inr_cofiber W A B) hB hA

/-- An actual subcategory summand can be cancelled by its displayed split cofiber. -/
theorem coprod_mem_iff_left {A B : C} (hB : P B) : P (A ⨿ B) ↔ P A :=
  ⟨fun hAB ↦ h.quotient (Additivity.coprod_inr_cof W A B)
    (Additivity.coprod_inr_cofiber W A B) hB hAB, fun hA ↦ h.coprod_mem hA hB⟩

/-- The chosen original zero is the actual unit of the chosen coproduct, up to its real
isomorphism. -/
def zeroCoprodIso (A : C) : W.zero ⨿ A ≅ A := by
  let : IsIso (W.isZero.to_ W.zero) := W.isZero.isIso W.isZero _
  let : IsIso (coprod.inr : A ⟶ W.zero ⨿ A) :=
    (Additivity.coprod_isPushout W W.zero A).isIso_inr_of_isIso
  exact (asIso (coprod.inr : A ⟶ W.zero ⨿ A)).symm

/-- The genuine four-summand permutation used by common complements. -/
def coprodFourSwap (A B D E : C) : (A ⨿ B) ⨿ (D ⨿ E) ≅ (A ⨿ D) ⨿ (B ⨿ E) :=
  coprod.associator A B (D ⨿ E) ≪≫
    coprod.mapIso (Iso.refl A) (coprod.associator B D E).symm ≪≫
    coprod.mapIso (Iso.refl A) (coprod.mapIso (coprod.braiding B D) (Iso.refl E)) ≪≫
    coprod.mapIso (Iso.refl A) (coprod.associator D B E) ≪≫
    (coprod.associator A D (B ⨿ E)).symm

/-- Two objects have a common actual complement taking both into the subcategory. -/
def Related (_h : DenseCofiberData W P) (A B : C) : Prop := ∃ Z : C, P (A ⨿ Z) ∧ P (B ⨿ Z)

/-- Genuine density gives a common complement of an object with itself. -/
theorem related_refl (A : C) : h.Related A A := by
  obtain ⟨Z, hZ⟩ := h.complement A
  exact ⟨Z, hZ, hZ⟩

/-- Common complements are symmetric without making any new choice. -/
theorem related_symm {A B : C} (hab : h.Related A B) : h.Related B A := by
  obtain ⟨Z, hA, hB⟩ := hab
  exact ⟨Z, hB, hA⟩

/-- Transitivity uses a genuine three-object complement and actual coproduct permutations. -/
theorem related_trans {A B D : C} (hab : h.Related A B) (hbd : h.Related B D) : h.Related A D := by
  obtain ⟨Z, hA, hB⟩ := hab
  obtain ⟨T, hB', hD⟩ := hbd
  refine ⟨Z ⨿ (B ⨿ T), (h.iso_iff (coprod.associator A Z (B ⨿ T))).mp (h.coprod_mem hA hB'), ?_⟩
  let e : (D ⨿ T) ⨿ (B ⨿ Z) ≅ D ⨿ (Z ⨿ (B ⨿ T)) :=
    coprodFourSwap D T B Z ≪≫
      coprod.mapIso (Iso.refl (D ⨿ B)) (coprod.braiding T Z) ≪≫
      coprodFourSwap D B Z T ≪≫ coprod.associator D Z (B ⨿ T)
  exact (h.iso_iff e).mp (h.coprod_mem hD hB)

/-- Actual isomorphic objects have common complements by transporting the displayed summand. -/
theorem related_of_iso {A B : C} (e : A ≅ B) : h.Related A B := by
  obtain ⟨Z, hZ⟩ := h.complement B
  exact ⟨Z, (h.iso_iff (coprod.mapIso e (Iso.refl Z))).mpr hZ, hZ⟩

/-- Original weak comparisons preserve the common-complement class via genuine weak coproducts. -/
theorem related_of_weak {A B : C} (f : A ⟶ B) (hf : W.weq f) : h.Related A B := by
  obtain ⟨Z, hZ⟩ := h.complement B
  exact ⟨Z, (h.weak (coprod.map f (𝟙 Z))
    (Additivity.coprod_map_weak W f (𝟙 Z) hf (W.weq.id_mem Z))).mpr hZ, hZ⟩

/-- Addition is well defined because the chosen common complements can themselves be summed. -/
theorem related_coprod {A B D E : C} (hab : h.Related A B) (hde : h.Related D E) :
    h.Related (A ⨿ D) (B ⨿ E) := by
  obtain ⟨Z, hA, hB⟩ := hab
  obtain ⟨T, hD, hE⟩ := hde
  exact ⟨Z ⨿ T, (h.iso_iff (coprodFourSwap A Z D T)).mp (h.coprod_mem hA hD),
    (h.iso_iff (coprodFourSwap B Z E T)).mp (h.coprod_mem hB hE)⟩

/-- The zero-class test is exactly actual membership, using the genuine split cofiber. -/
theorem related_zero_iff (A : C) : h.Related A W.zero ↔ P A := by
  constructor
  · rintro ⟨Z, hA, hZ⟩
    exact (h.coprod_mem_iff_left ((h.iso_iff (zeroCoprodIso (W := W) Z)).mp hZ)).mp hA
  · intro hA
    exact ⟨W.zero, h.coprod_mem hA h.zero, h.coprod_mem h.zero h.zero⟩

/-- The actual common-complement equivalence relation. -/
def setoid : Setoid C where
  r := h.Related
  iseqv := ⟨h.related_refl, h.related_symm, h.related_trans⟩

end DenseCofiberData
end CategoryTheory.Waldhausen.Cofinality
