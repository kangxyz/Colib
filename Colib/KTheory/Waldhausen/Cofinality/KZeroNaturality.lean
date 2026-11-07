/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Cofinality.ComplementMap
public import Colib.KTheory.Waldhausen.Cofinality.DenseKZero
public import Colib.Topology.ClassifyingSpace.GroupoidFundamentalGroupNaturality

/-! # Naturality of the original grading obstruction
Implementation provenance: `Quillen/Waldhausen/Cofinality/KZeroNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe u

namespace CategoryTheory.Waldhausen.Cofinality.Grading
variable {C D G H : Type u} [SmallCategory C] [SmallCategory D]
  [AddCommGroup G] [AddCommGroup H] {W : Structure C} {V : Structure D}
  (d : Grading W G) (e : Grading V H) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (φ : G →+ H) (hφ : ∀ A, e.value (F.obj A) = φ (d.value A))

include hF hφ in
/-- Exactness of the original functor for the genuine endpoint-grade weak classes. -/
theorem coarseMap_exact :
    IsExact d.coarseStructure.cof d.coarseStructure.weq
      e.coarseStructure.cof e.coarseStructure.weq F where
  zero := hF.zero
  cofibration := hF.cofibration
  pushout := hF.pushout
  weak {A B} f hf := by
    change e.value (F.obj A) = e.value (F.obj B)
    rw [hφ A,hφ B]
    exact congrArg φ hf

variable (Td : FunctorialFactorization W) (Te : FunctorialFactorization V)

/-- Original represented values remain represented after the exact functor. -/
def valueRangeMap : d.valueRange Td →+ e.valueRange Te where
  toFun x := ⟨φ x.val, by
    obtain ⟨A,hA⟩ := x.property
    exact ⟨F.obj A, (hφ A).trans (congrArg φ hA)⟩⟩
  map_zero' := Subtype.ext (map_zero φ)
  map_add' _ _ := Subtype.ext (map_add φ _ _)

/-- The original group-grade square commutes on every actual grid arrow. -/
theorem groupGradeMap_natural :
    sSetMap (coarseMap_exact d e hF φ hφ) ≫ e.groupGradeMap Te =
      d.groupGradeMap Td ≫ nerveMap (valueRangeMap d e φ hφ Td Te).toMultiplicative.toFunctor := by
  ext n : 3
  funext X
  refine CategoryTheory.Functor.ext (fun _ ↦ Subsingleton.elim _ _) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Subtype.ext
  exact hφ (X.val.obj (0,(⟨(i,j),leOfHom f⟩ : Interval n.unop)))

include hφ in
/-- The chosen-zero rebasing changes no actual endpoint grade. -/
lemma rebase_value (A : C) :
    e.value ((rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero)).obj A) =
      φ (d.value A) :=
  (e.weak ((CategoryTheory.rebaseFunctorIso F W.zero V.zero
    ((hF.zero W.isZero).iso V.isZero)).inv.app A) (V.weq_iso _ inferInstance)).trans (hφ A)

/-- The whole original coarse K-zero square commutes, including its canonical
zero rebasing, before identifying either homotopy group with the grade group. -/
theorem coarseKZeroToGroupPi_natural :
    (e.coarseKZeroToGroupPi Te).comp (KMap (coarseMap_exact d e hF φ hφ) 0) =
      (HomotopyGroup.mapHom
        (classifyingSpaceMap (valueRangeMap d e φ hφ Td Te).toMultiplicative.toFunctor).hom
        (classifyingSpaceMap_point _ (SingleObj.star _))).comp (d.coarseKZeroToGroupPi Td) := by
  rw [KMap_eq_piMap]
  unfold coarseKZeroToGroupPi
  rw [← HomotopyGroup.mapHom_comp, ← HomotopyGroup.mapHom_comp]
  congr 1
  change (SSet.toTop.map (sSetMap _) ≫ SSet.toTop.map (e.groupGradeMap Te)).hom =
    (SSet.toTop.map (d.groupGradeMap Td) ≫ SSet.toTop.map (nerveMap _)).hom
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp]
  congr 2
  exact groupGradeMap_natural d e hF.rebase φ (rebase_value d e hF φ hφ) Td Te

/-- Naturality retains the original KMap and the actual represented grade values. -/
theorem coarseKZeroEquiv_natural (x : d.coarseStructure.K 0) :
    (valueRangeMap d e φ hφ Td Te).toMultiplicative (d.coarseKZeroEquiv Td x) =
      e.coarseKZeroEquiv Te (KMap (coarseMap_exact d e hF φ hφ) 0 x) := by
  apply (GroupoidClassifying.singleObjPiOneEquiv _).injective
  rw [← GroupoidClassifying.singleObjPiOneEquiv_natural]
  simp only [coarseKZeroEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    MulEquiv.ofBijective_apply]
  change HomotopyGroup.mapHom _ _ (d.coarseKZeroToGroupPi Td x) =
    e.coarseKZeroToGroupPi Te (KMap (coarseMap_exact d e hF φ hφ) 0 x)
  exact (DFunLike.congr_fun (coarseKZeroToGroupPi_natural d e hF φ hφ Td Te) x).symm

include Td Te in
/-- An injective value-group map gives injectivity on the original coarse K-zero. -/
theorem coarseKMap_injective (hφi : Function.Injective φ) :
    Function.Injective (KMap (coarseMap_exact d e hF φ hφ) 0) := by
  intro x y hxy
  apply (d.coarseKZeroEquiv Td).injective
  have hr : Function.Injective (valueRangeMap d e φ hφ Td Te).toMultiplicative := by
    intro a b hab
    apply Subtype.ext
    exact hφi (congrArg Subtype.val hab)
  apply hr
  rw [coarseKZeroEquiv_natural d e hF φ hφ Td Te, coarseKZeroEquiv_natural d e hF φ hφ Td Te, hxy]

variable (Dd : Fibration.RowFactorization.JointData (.refl W))
  (De : Fibration.RowFactorization.JointData (.refl V))

/-- The original fine K-zero obstruction square commutes as actual homomorphisms. -/
theorem gradeKZeroMap_natural :
    (valueRangeMap d e φ hφ Dd.sourceFactorization De.sourceFactorization).toMultiplicative.comp
      (d.gradeKZeroMap Dd) = (e.gradeKZeroMap De).comp (KMap hF 0) := by
  apply MonoidHom.ext
  intro x
  change (valueRangeMap d e φ hφ Dd.sourceFactorization De.sourceFactorization).toMultiplicative
    (d.coarseKZeroEquiv Dd.sourceFactorization (KMap (Fibration.changeWeak_exact d.nested) 0 x)) = _
  rw [coarseKZeroEquiv_natural d e hF φ hφ Dd.sourceFactorization De.sourceFactorization]
  have hc : (KMap (coarseMap_exact d e hF φ hφ) 0).comp
      (KMap (Fibration.changeWeak_exact d.nested) 0) =
      (KMap (Fibration.changeWeak_exact e.nested) 0).comp (KMap hF 0) := by
    rw [CategoryTheory.Waldhausen.KMap_comp_KMap, CategoryTheory.Waldhausen.KMap_comp_KMap]
  exact congrArg (e.coarseKZeroEquiv De.sourceFactorization) (DFunLike.congr_fun hc x)

end CategoryTheory.Waldhausen.Cofinality.Grading

namespace CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {W : Structure C} {V : Structure D} [HasBinaryCoproducts C] [HasBinaryCoproducts D]
  {P : ObjectProperty C} {Q : ObjectProperty D}
  (h : DenseCofiberData W P) (k : DenseCofiberData V Q) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F) (hp : ∀ A, P A → Q (F.obj A))
  (Dd : Fibration.RowFactorization.JointData (.refl W))
  (De : Fibration.RowFactorization.JointData (.refl V))

/-- Naturality of the already-defined original fine K-zero complement obstruction,
proved through its actual simplicial group-grade map and canonical zero rebasing. -/
theorem classKZeroMap_natural :
    (h.classMap k hF hp).toMultiplicative.comp (h.classKZeroMap Dd) =
      (k.classKZeroMap De).comp (KMap hF 0) := by
  apply MonoidHom.ext
  intro x
  have ht := Grading.gradeKZeroMap_natural h.grading k.grading hF
    (h.classMap k hF hp) (fun _ ↦ rfl) Dd De
  exact congrArg
    (fun z : Multiplicative (k.grading.valueRange De.sourceFactorization) ↦
      Multiplicative.ofAdd z.toAdd.val) (DFunLike.congr_fun ht x)

end CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
