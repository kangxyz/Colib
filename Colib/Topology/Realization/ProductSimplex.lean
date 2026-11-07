/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.CylinderIso
public import Mathlib.CategoryTheory.MorphismProperty.Retract

/-!
# Realization and products with a standard simplex

A simplex is a simplicial retract of an iterated interval. Consequently the
proved cylinder comparison implies the full product comparison for every
standard simplex. This supplies its inverse and naturality without choosing
triangulations independently on different simplices.
-/
@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial Topology

universe u

namespace SSet

/-- Product comparison is compatible with the associators. -/
theorem productComparison_associativity {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) (X Y Z : C) :
    F.map (α_ X Y Z).hom ≫ prodComparison F X (Y ⊗ Z) ≫
        (F.obj X ◁ prodComparison F Y Z) =
      prodComparison F (X ⊗ Y) Z ≫ (prodComparison F X Y ▷ F.obj Z) ≫
        (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, whiskerLeft_fst, prodComparison_fst_assoc,
      associator_hom_fst, whiskerRight_fst_assoc, prodComparison_fst,
      ← F.map_comp, associator_hom_fst]
  · apply CartesianMonoidalCategory.hom_ext <;>
      simp only [Category.assoc, whiskerLeft_snd_assoc, prodComparison_snd_assoc,
        prodComparison_fst, prodComparison_snd, associator_hom_snd_fst,
        associator_hom_snd_snd, whiskerRight_fst_assoc, whiskerRight_snd,
        prodComparison_fst_assoc, ← F.map_comp]

/-- Product comparison being an isomorphism is stable under a retract of
its second argument. -/
theorem productComparison_isIso_of_retract {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) (X : C) {Y Z : C} (r : Retract Y Z)
    [IsIso (prodComparison F X Z)] : IsIso (prodComparison F X Y) := by
  apply MorphismProperty.of_retract (P := MorphismProperty.isomorphisms D) (g := prodComparison
    F X Z)
  · refine { i := Arrow.homMk (F.map (X ◁ r.i)) (F.obj X ◁ F.map r.i)
               (prodComparison_natural_whiskerLeft F r.i)
             r := Arrow.homMk (F.map (X ◁ r.r)) (F.obj X ◁ F.map r.r)
               (prodComparison_natural_whiskerLeft F r.r)
             retract := ?_ }
    apply Arrow.hom_ext <;> simp [← F.map_comp, ← MonoidalCategory.whiskerLeft_comp]
  · infer_instance

/-- The interval result stated with the ordinary product comparison. -/
instance realizationProductComparison_interval_isIso (X : SSet.{u}) :
    IsIso (prodComparison SSet.toTop X Δ[1]) := by
  have h : prodComparison SSet.toTop X Δ[1] ≫
      (|X| ◁ SSet.stdSimplex.toTopObjIsoI.hom) = realizationCylinderComparison X := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [realizationCylinderComparison]
  exact IsIso.of_isIso_fac_right h

/-- Combining two product comparisons using associativity. -/
theorem productComparison_isIso_tensor {C D : Type*} [Category C] [Category D]
    [CartesianMonoidalCategory C] [CartesianMonoidalCategory D]
    (F : C ⥤ D) (X Y Z : C)
    [IsIso (prodComparison F X Y)] [IsIso (prodComparison F Y Z)]
    [IsIso (prodComparison F (X ⊗ Y) Z)] :
    IsIso (prodComparison F X (Y ⊗ Z)) := by
  have h := productComparison_associativity F X Y Z
  have : IsIso (F.map (α_ X Y Z).hom ≫ prodComparison F X (Y ⊗ Z)) :=
    IsIso.of_isIso_fac_right (by simpa only [Category.assoc] using h)
  exact IsIso.of_isIso_fac_left (rfl :
    F.map (α_ X Y Z).hom ≫ prodComparison F X (Y ⊗ Z) =
      F.map (α_ X Y Z).hom ≫ prodComparison F X (Y ⊗ Z))

/-- The simplicial map adding the two grid coordinates. -/
def simplexPrismSum (n : ℕ) : (Δ[n] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[n + 1] where
  app m := ↾fun x ↦ SSet.stdSimplex.objMk
    (SSet.prodStdSimplex.orderHomOfSimplex x rfl)
  naturality m k f := by
    ext x : 4
    rfl

/-- A maximal chain in the prism splits the sum of its grid coordinates. -/
def simplexPrismRetract (n : ℕ) : Retract (Δ[n + 1] : SSet.{u}) (Δ[n] ⊗ Δ[1]) where
  i := SSet.yonedaEquiv.symm (SSet.prodStdSimplex.nonDegenerateEquiv₁ (Fin.last n)).val
  r := simplexPrismSum n
  retract := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    apply SSet.stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    exact (SSet.prodStdSimplex.nonDegenerate_max_dim_iff _ rfl).mp
      (SSet.prodStdSimplex.nonDegenerateEquiv₁ (Fin.last n)).property

/-- The point is a simplicial retract of the interval. -/
def simplexZeroIntervalRetract : Retract (Δ[0] : SSet.{u}) Δ[1] where
  i := SSet.stdSimplex.δ 0
  r := SSet.stdSimplex.σ 0
  retract := SSet.stdSimplex.ext₀

/-- Geometric realization preserves product with every standard simplex. -/
instance realizationProductComparison_simplex_isIso (X : SSet.{u}) (n : ℕ) :
    IsIso (prodComparison SSet.toTop X Δ[n]) := by
  induction n with
  | zero => exact productComparison_isIso_of_retract SSet.toTop X simplexZeroIntervalRetract
  | succ n hn =>
    have : IsIso (prodComparison SSet.toTop X (Δ[n] ⊗ Δ[1])) :=
      productComparison_isIso_tensor SSet.toTop X Δ[n] Δ[1]
    exact productComparison_isIso_of_retract SSet.toTop X (simplexPrismRetract n)

/-- The canonical product homeomorphism, with an arbitrary simplicial set
in its first argument and a representable in its second argument. -/
def realizationProductSimplexIso (X : SSet.{u}) (n : ℕ) :
    |X ⊗ Δ[n]| ≅ |X| ⊗ |(Δ[n] : SSet.{u})| :=
  asIso (prodComparison SSet.toTop X Δ[n])

/-- Naturality of the canonical homeomorphism in both arguments. -/
theorem realizationProductSimplexIso_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    {m n : ℕ} (g : ⦋m⦌ ⟶ ⦋n⦌) :
    SSet.toTop.map (f ⊗ₘ SSet.stdSimplex.map g) ≫
        (realizationProductSimplexIso Y n).hom =
      (realizationProductSimplexIso X m).hom ≫
        (SSet.toTop.map f ⊗ₘ SSet.toTop.map (SSet.stdSimplex.map g)) :=
  prodComparison_natural SSet.toTop f (SSet.stdSimplex.map g)

@[simp]
theorem realizationProductSimplexIso_hom (X : SSet.{u}) (n : ℕ) :
    (realizationProductSimplexIso X n).hom = prodComparison SSet.toTop X Δ[n] := rfl

/-- The corresponding comparison for an arbitrary object of the simplex category. -/
instance realizationProductComparison_representable_isIso
    (X : SSet.{u}) (n : SimplexCategory) :
    IsIso (prodComparison SSet.toTop X (SSet.stdSimplex.obj n)) := by
  cases n using SimplexCategory.rec with
  | _ n => exact realizationProductComparison_simplex_isIso X n

/-- Realization of the product of two simplices is the actual product of their
barycentric topological simplices. -/
def realizationProductSimplexHomeomorph (p q : ℕ) :
    |(Δ[p] ⊗ Δ[q] : SSet.{u})| ≃ₜ
      _root_.stdSimplex ℝ (Fin (p + 1)) × _root_.stdSimplex ℝ (Fin (q + 1)) :=
  (TopCat.homeoOfIso (realizationProductSimplexIso Δ[p] q)).trans
    ((SimplexCategory.toTopHomeo ⦋p⦌).prodCongr
      (SimplexCategory.toTopHomeo ⦋q⦌))

@[simp]
theorem realizationProductSimplexHomeomorph_apply (p q : ℕ)
    (x : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    realizationProductSimplexHomeomorph p q x =
      (SimplexCategory.toTopHomeo ⦋p⦌ (SSet.toTop.map (fst Δ[p] Δ[q]) x),
       SimplexCategory.toTopHomeo ⦋q⦌ (SSet.toTop.map (snd Δ[p] Δ[q]) x)) := rfl

/-- The barycentric comparison is natural under both simplex operators. -/
theorem realizationProductSimplexHomeomorph_naturality
    {p q p' q' : ℕ} (f : ⦋p⦌ ⟶ ⦋p'⦌) (g : ⦋q⦌ ⟶ ⦋q'⦌)
    (x : |(Δ[p] ⊗ Δ[q] : SSet.{u})|) :
    realizationProductSimplexHomeomorph p' q'
        (SSet.toTop.map (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map g) x) =
      (_root_.stdSimplex.map f (realizationProductSimplexHomeomorph p q x).1,
       _root_.stdSimplex.map g (realizationProductSimplexHomeomorph p q x).2) := by
  apply Prod.ext
  · change SimplexCategory.toTopHomeo ⦋p'⦌
      ((SSet.toTop.map (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map g) ≫
        SSet.toTop.map (fst Δ[p'] Δ[q'])) x) = _
    rw [← Functor.map_comp, tensorHom_fst, Functor.map_comp]
    exact SimplexCategory.toTopHomeo_naturality_apply f _
  · change SimplexCategory.toTopHomeo ⦋q'⦌
      ((SSet.toTop.map (SSet.stdSimplex.map f ⊗ₘ SSet.stdSimplex.map g) ≫
        SSet.toTop.map (snd Δ[p'] Δ[q'])) x) = _
    rw [← Functor.map_comp, tensorHom_snd, Functor.map_comp]
    exact SimplexCategory.toTopHomeo_naturality_apply g _

end SSet
