/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Extend

/-!
# Extending actual projective-resolution comparisons

A chain map into the image of a projective resolution under an additive functor
extends to the native integer-indexed cochain resolutions. The comparison retains
its literal components and its augmentation square.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits HomologicalComplex

universe u₁ v₁ u₂ v₂

namespace CategoryTheory.ProjectiveResolution

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (F : C ⥤ D) [F.Additive]
  {A : C} {B : D} (R : ProjectiveResolution A) (S : ProjectiveResolution B)
  (h : S.complex ⟶ (F.mapHomologicalComplex (.down ℕ)).obj R.complex)

/-- The degreewise comparison, zero in positive degrees. -/
def cochainComparisonComponent (i : ℤ) :
    S.cochainComplex.X i ⟶ F.obj (R.cochainComplex.X i) :=
  if hi : i ≤ 0 then
    (S.cochainComplexXIso i (-i).toNat (by omega)).hom ≫ h.f (-i).toNat ≫
      F.map (R.cochainComplexXIso i (-i).toNat (by omega)).inv
  else 0

@[simp]
lemma cochainComparisonComponent_neg (n : ℕ) :
    cochainComparisonComponent F R S h (-n) =
      (S.cochainComplexXIso (-n) n rfl).hom ≫ h.f n ≫
        F.map (R.cochainComplexXIso (-n) n rfl).inv := by
  dsimp only [cochainComparisonComponent]
  rw [dite_eq_left (by omega)]
  have aux (k : ℕ) (hk : -(k : ℤ) = -(n : ℤ)) :
      (S.cochainComplexXIso (-n) k hk).hom ≫ h.f k ≫
        F.map (R.cochainComplexXIso (-n) k hk).inv =
      (S.cochainComplexXIso (-n) n rfl).hom ≫ h.f n ≫
        F.map (R.cochainComplexXIso (-n) n rfl).inv := by
    have : k = n := by omega
    subst k
    rfl
  exact aux _ _

/-- Extension of a chain comparison to the native cochain resolutions. -/
def cochainComparison :
    S.cochainComplex ⟶ (F.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex where
  f := cochainComparisonComponent F R S h
  comm' i j _ := by
    by_cases hi : i ≤ 0
    · by_cases hj : j ≤ 0
      · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat hi
        obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hj
        simp only [cochainComparisonComponent_neg]
        change _ ≫ F.map (R.cochainComplex.d _ _) = S.cochainComplex.d _ _ ≫ _
        rw [R.cochainComplex_d _ _ m n rfl rfl,
          S.cochainComplex_d _ _ m n rfl rfl]
        have hc : F.map (R.cochainComplexXIso (-m) m rfl).inv ≫
            F.map (R.cochainComplexXIso (-m) m rfl).hom = 𝟙 _ := by
          rw [← F.map_comp, Iso.inv_hom_id, F.map_id]
        simp only [Functor.map_comp, Category.assoc, reassoc_of% hc,
          Iso.inv_hom_id_assoc]
        simpa only [Functor.mapHomologicalComplex_obj_d, Category.assoc] using
          congrArg (fun f => (S.cochainComplexXIso (-m) m rfl).hom ≫ f ≫
            F.map (R.cochainComplexXIso (-n) n rfl).inv) (h.comm m n)
      · exact (F.map_isZero (R.cochainComplex.isZero_of_isStrictlyLE 0 j (by omega))).eq_of_tgt _ _
    · exact (S.cochainComplex.isZero_of_isStrictlyLE 0 i (by omega)).eq_of_src _ _

@[simp, reassoc]
lemma cochainComparison_f_neg (n : ℕ) :
    (cochainComparison F R S h).f (-n) =
      (S.cochainComplexXIso (-n) n rfl).hom ≫ h.f n ≫
        F.map (R.cochainComplexXIso (-n) n rfl).inv :=
  cochainComparisonComponent_neg F R S h n

/-- Chain-level augmentation compatibility gives the native cochain square. -/
@[reassoc]
lemma cochainComparison_comp_π' (a : B ⟶ F.obj A)
    (ha : h.f 0 ≫ F.map (R.π.f 0) = S.π.f 0 ≫ a) :
    cochainComparison F R S h ≫ (F.mapHomologicalComplex (.up ℤ)).map R.π' ≫
      (F.mapCochainComplexSingleFunctor 0).hom.app A =
        S.π' ≫ (CochainComplex.singleFunctor D 0).map a := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f]
  rw [show (cochainComparison F R S h).f 0 = _ from
    cochainComparison_f_neg F R S h 0]
  simp [π'_f_zero, Functor.mapCochainComplexSingleFunctor,
    Functor.map_comp, Category.assoc, ← F.map_comp_assoc, ha,
    CochainComplex.singleFunctor,
    HomologicalComplex.single, HomologicalComplex.singleObjXSelf,
    HomologicalComplex.singleObjXIsoOfEq]

/-- A literal chain-level component equation transfers to the extended comparison. -/
lemma cochainComparison_component {T : C} {n : ℕ}
    (f : R.complex.X n ⟶ T) (g : S.complex.X n ⟶ F.obj T)
    (hg : g = h.f n ≫ F.map f) :
    (S.cochainComplexXIso (-n) n rfl).hom ≫ g =
      (cochainComparison F R S h).f (-n) ≫
        F.map ((R.cochainComplexXIso (-n) n rfl).hom ≫ f) := by
  rw [cochainComparison_f_neg, hg]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]

end CategoryTheory.ProjectiveResolution
