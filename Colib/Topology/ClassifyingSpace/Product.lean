/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.ProductComparison
public import Colib.Topology.ClassifyingSpace.Map
public import Mathlib.CategoryTheory.Products.Basic

/-!
# The original product comparison for classifying spaces

The nerve preserves categorical products. Combined with the existing exact
compact-source lifting theorem for realization products, this yields the actual
product map on positive homotopy groups, without claiming that arbitrary
ordinary topological products commute with realization by a homeomorphism.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology

namespace CategoryTheory

variable (C D : Type u) [Category.{v} C] [Category.{v} D]

/-- The product nerve isomorphism retains the two actual projection functors. -/
def nerveProductIso : nerve (C × D) ≅ nerve C ⊗ nerve D where
  hom :=
    { app := fun _ ↦ ↾fun F ↦
        (F ⋙ CategoryTheory.Prod.fst C D, F ⋙ CategoryTheory.Prod.snd C D)
      naturality := by intros; rfl }
  inv :=
    { app := fun _ ↦ ↾fun F ↦ F.1.prod' F.2
      naturality := by intros; rfl }
  hom_inv_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro F
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro F
    apply Prod.ext
    · refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
      intro i j f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
    · refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
      intro i j f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl

/-- The classifying-space comparison is the pair of the actual projection maps. -/
def classifyingSpaceProductComparison :
    C(ClassifyingSpace (C × D), ClassifyingSpace C × ClassifyingSpace D) :=
  (classifyingSpaceMap (CategoryTheory.Prod.fst C D)).hom.prodMk
    (classifyingSpaceMap (CategoryTheory.Prod.snd C D)).hom

lemma classifyingSpaceProductComparison_eq :
    classifyingSpaceProductComparison C D =
      (ProductRealization.comparison (nerve C) (nerve D)).comp
        (SSet.toTop.map (nerveProductIso C D).hom).hom := by
  apply ContinuousMap.ext
  intro x
  apply Prod.ext
  · change classifyingSpaceMap (CategoryTheory.Prod.fst C D) x =
      (SSet.toTop.map (nerveProductIso C D).hom ≫
        prodComparison SSet.toTop (nerve C) (nerve D) ≫ fst _ _) x
    rw [prodComparison_fst, ← Functor.map_comp]
    rfl
  · change classifyingSpaceMap (CategoryTheory.Prod.snd C D) x =
      (SSet.toTop.map (nerveProductIso C D).hom ≫
        prodComparison SSet.toTop (nerve C) (nerve D) ≫ snd _ _) x
    rw [prodComparison_snd, ← Functor.map_comp]
    rfl

lemma classifyingSpaceProductComparison_injective :
    Function.Injective (classifyingSpaceProductComparison C D) := by
  rw [classifyingSpaceProductComparison_eq]
  exact (ProductRealization.comparison_injective (nerve C) (nerve D)).comp
    (TopCat.homeoOfIso (SSet.toTop.mapIso (nerveProductIso C D))).injective

lemma classifyingSpaceProductComparison_compact_lifts :
    HasCompactSourceLifts (classifyingSpaceProductComparison C D) := by
  intro T _ _ f
  obtain ⟨g, hg⟩ := ProductRealization.comparison_compact_lifts (nerve C) (nerve D) T f
  refine ⟨(SSet.toTop.map (nerveProductIso C D).inv).hom.comp g, ?_⟩
  rw [classifyingSpaceProductComparison_eq]
  apply ContinuousMap.ext
  intro t
  change ProductRealization.comparison (nerve C) (nerve D)
    (SSet.toTop.map (nerveProductIso C D).hom
      (SSet.toTop.map (nerveProductIso C D).inv (g t))) = f t
  have h := ConcreteCategory.congr_hom (SSet.toTop.mapIso (nerveProductIso C D)).inv_hom_id (g t)
  change SSet.toTop.map (nerveProductIso C D).hom
    (SSet.toTop.map (nerveProductIso C D).inv (g t)) = g t at h
  rw [h]
  exact DFunLike.congr_fun hg t

@[simp]
lemma classifyingSpaceProductComparison_point (c : C) (d : D) :
    classifyingSpaceProductComparison C D (classifyingSpacePoint (c, d)) =
      (classifyingSpacePoint c, classifyingSpacePoint d) := by
  exact Prod.ext (classifyingSpaceMap_point (CategoryTheory.Prod.fst C D) (c, d))
    (classifyingSpaceMap_point (CategoryTheory.Prod.snd C D) (c, d))

/-- Product decomposition of actual shifted homotopy groups at object vertices. -/
def classifyingSpaceProductPiEquiv (c : C) (d : D) (n : ℕ) :
    ShiftedHomotopyGroup (C × D) (c, d) n ≃*
      ShiftedHomotopyGroup C c n × ShiftedHomotopyGroup D d n :=
  (piEquivOfCompactLifts (classifyingSpaceProductComparison C D)
    (classifyingSpaceProductComparison_injective C D)
    (classifyingSpaceProductComparison_compact_lifts C D)
    (classifyingSpaceProductComparison_point C D c d) n).trans
      (piProdEquiv n (classifyingSpacePoint c) (classifyingSpacePoint d))

/-- The forward map is exactly the pair of the original projection-induced maps. -/
lemma classifyingSpaceProductPiEquiv_apply (c : C) (d : D) (n : ℕ)
    (a : ShiftedHomotopyGroup (C × D) (c, d) n) :
    classifyingSpaceProductPiEquiv C D c d n a =
      (shiftedHomotopyGroupMap (CategoryTheory.Prod.fst C D) (c, d) n a,
        shiftedHomotopyGroupMap (CategoryTheory.Prod.snd C D) (c, d) n a) := by
  induction a using Quotient.inductionOn with
  | _ a =>
    apply Prod.ext
    · apply congrArg Quotient.mk'
      ext t
      rfl
    · apply congrArg Quotient.mk'
      ext t
      rfl

/-- A paired functor induces the pair of its original maps under the product comparison. -/
lemma classifyingSpaceProductPiEquiv_pairing {E : Type u} [Category.{v} E]
    (F : E ⥤ C) (G : E ⥤ D) (e : E) (n : ℕ)
    (a : ShiftedHomotopyGroup E e n) :
    classifyingSpaceProductPiEquiv C D (F.obj e) (G.obj e) n
      (shiftedHomotopyGroupMap (F.prod' G) e n a) =
        (shiftedHomotopyGroupMap F e n a, shiftedHomotopyGroupMap G e n a) := by
  rw [classifyingSpaceProductPiEquiv_apply]
  apply Prod.ext
  · exact congrArg (fun h ↦ h a)
      (shiftedHomotopyGroupMap_comp (F.prod' G) (CategoryTheory.Prod.fst C D) e n).symm
  · exact congrArg (fun h ↦ h a)
      (shiftedHomotopyGroupMap_comp (F.prod' G) (CategoryTheory.Prod.snd C D) e n).symm

end CategoryTheory
