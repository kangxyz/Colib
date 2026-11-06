/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Adjunction.Limits

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Transpose
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.TriplePushout

/-! # Genuine exactness of the Reedy-square transposition

For a morphism cube, the two total relative pushouts are related by their
actual universal properties. This proves preservation of the Reedy class;
the categorical involution alone would not supply this assertion.


Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/TransposeExact.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The actual three-direction relative pushout proves the transposed cube is Reedy-cofibrant. -/
theorem transpose_cof {X Y : Obj (waldhausenStructure W)} {f : X ⟶ Y}
    (hf : cof (waldhausenStructure W) f) : cof (waldhausenStructure W) ((transpose W).map f) := by
  let V := waldhausenStructure W
  let R := (relativeFunctor V).obj (Arrow.mk f)
  let i : X.obj.right ⟶ R := Additivity.sourceι V (inclusion V) (inclusion_cof V) (Arrow.mk f)
  let j : Y.obj.left ⟶ R := Additivity.targetι V (inclusion V) (inclusion_cof V) (Arrow.mk f)
  let k : R ⟶ Y.obj.right := relativeMap V f
  have hR : IsPushout X.obj.hom f.hom.left i j :=
    Additivity.pushoutFunctor_isPushout V (inclusion V) (inclusion_cof V) (Arrow.mk f)
  have hi : i ≫ k = f.hom.right :=
    Additivity.sourceι_comparison V (inclusion V) (inclusion_cof V) (Arrow.mk f)
  have hj : j ≫ k = Y.obj.hom :=
    Additivity.targetι_comparison V (inclusion V) (inclusion_cof V) (Arrow.mk f)
  obtain ⟨hP, hQ⟩ := pointwise_of_isPushout W X.property hR
  let f' := (transpose W).map f
  let R' := (relativeFunctor V).obj (Arrow.mk f')
  let i' : ((transpose W).obj X).obj.right ⟶ R' :=
    Additivity.sourceι V (inclusion V) (inclusion_cof V) (Arrow.mk f')
  let j' : ((transpose W).obj Y).obj.left ⟶ R' :=
    Additivity.targetι V (inclusion V) (inclusion_cof V) (Arrow.mk f')
  let k' : R' ⟶ ((transpose W).obj Y).obj.right := relativeMap V f'
  have hR' : IsPushout ((transpose W).obj X).obj.hom f'.hom.left i' j' :=
    Additivity.pushoutFunctor_isPushout V (inclusion V) (inclusion_cof V) (Arrow.mk f')
  have hi' : i' ≫ k' = f'.hom.right :=
    Additivity.sourceι_comparison V (inclusion V) (inclusion_cof V) (Arrow.mk f')
  have hj' : j' ≫ k' = ((transpose W).obj Y).obj.hom :=
    Additivity.targetι_comparison V (inclusion V) (inclusion_cof V) (Arrow.mk f')
  obtain ⟨hP', hQ'⟩ := pointwise_of_isPushout W ((transpose W).obj X).property hR'
  change cof W f'.hom.left ∧ cof W k'
  refine ⟨?_, ?_⟩
  · exact cof_of_relative W f'.hom.left hf.1.1 hP k.hom.left
      (congrArg (fun z ↦ z.hom.left) hi) (congrArg (fun z ↦ z.hom.left) hj) hf.2.1
  · have hl' : W.cof k'.hom.left := cof_relative W hf.1 hP' k'.hom.left
      (congrArg (fun z ↦ z.hom.left) hi') (congrArg (fun z ↦ z.hom.left) hj')
    let T := (relativeFunctor W).obj (Arrow.mk k)
    let tQ : R.obj.right ⟶ T := Additivity.sourceι W (inclusion W) (inclusion_cof W) (Arrow.mk k)
    let tC : Y.obj.right.obj.left ⟶ T :=
      Additivity.targetι W (inclusion W) (inclusion_cof W) (Arrow.mk k)
    let K : T ⟶ Y.obj.right.obj.right := relativeMap W k
    have hT : IsPushout R.obj.hom k.hom.left tQ tC :=
      Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk k)
    have hQK : tQ ≫ K = k.hom.right :=
      Additivity.sourceι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk k)
    have hCK : tC ≫ K = Y.obj.right.obj.hom :=
      Additivity.targetι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk k)
    obtain ⟨r, hU, hrD, hrC⟩ := relativePushoutInterchange hP hQ hP' hQ' hT
      i.hom.w j.hom.w (congrArg (fun z ↦ z.hom.left) hi) (congrArg (fun z ↦ z.hom.left) hj)
      i'.hom.w j'.hom.w (congrArg (fun z ↦ z.hom.left) hi') (congrArg (fun z ↦ z.hom.left) hj')
    apply cof_of_relative W k' hl' hU K ?_ ?_ hf.2.2
    · apply hQ'.hom_ext
      · rw [← Category.assoc, hrD, Category.assoc, hQK]
        exact (congrArg (fun z ↦ z.hom.right) hi).trans
          (congrArg (fun z ↦ z.hom.right) hi').symm
      · rw [← Category.assoc, hrC, hCK]
        exact (congrArg (fun z ↦ z.hom.right) hj').symm
    · rw [Category.assoc, hQK]
      exact congrArg (fun z ↦ z.hom.right) hj

/-- The original categorical transposition is a genuine exact functor. -/
theorem transpose_exact :
    IsExact (waldhausenStructure (waldhausenStructure W)).cof
      (waldhausenStructure (waldhausenStructure W)).weq
      (waldhausenStructure (waldhausenStructure W)).cof
      (waldhausenStructure (waldhausenStructure W)).weq (transpose W) where
  zero h := (isZero (waldhausenStructure W)).of_iso
    ((transpose W).mapIso (h.iso (isZero (waldhausenStructure W))))
  cofibration _ h := transpose_cof W h
  weak _ h := transpose_weq W h
  pushout _ h := by
    let : (transpose W).IsEquivalence := (transposeEquivalence W).isEquivalence_functor
    exact h.map (transpose W)

end CategoryTheory.Waldhausen.ExtensionCategory
