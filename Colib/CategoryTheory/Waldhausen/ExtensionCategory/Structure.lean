/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.ArrowPushouts

/-! # The genuine Waldhausen structure on cofibration arrows

Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/Structure.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- Every pushout along a Reedy cofibration is computed on its two components. -/
theorem pointwise_of_isPushout {A B D P : Obj W}
    {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ P} {j : D ⟶ P}
    (hf : cof W f) (h : IsPushout f g i j) :
    IsPushout f.hom.left g.hom.left i.hom.left j.hom.left ∧
      IsPushout f.hom.right g.hom.right i.hom.right j.hom.right := by
  obtain ⟨Q, i₀, j₀, h₀, hl, hr, _⟩ := exists_pointwise_pushout W f g hf
  let e : Q ≅ P := h₀.isoIsPushout _ _ h
  constructor
  · apply hl.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ((source W).mapIso e)
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg (fun a ↦ a.hom.left) (h₀.inl_isoIsPushout_hom _ _ h)
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg (fun a ↦ a.hom.left) (h₀.inr_isoIsPushout_hom _ _ h)
  · apply hr.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) ((middle W).mapIso e)
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg (fun a ↦ a.hom.right) (h₀.inl_isoIsPushout_hom _ _ h)
    · simpa only [Iso.refl_hom, Category.id_comp] using!
        congrArg (fun a ↦ a.hom.right) (h₀.inr_isoIsPushout_hom _ _ h)

/-- Reedy cofibrations are stable under genuine pushouts. -/
theorem cof_pushout {A B D P : Obj W}
    {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ P} {j : D ⟶ P}
    (hf : cof W f) (h : IsPushout f g i j) : cof W j := by
  obtain ⟨hl, hr⟩ := pointwise_of_isPushout W hf h
  refine ⟨W.cof_pushout hf.1 hl, ?_⟩
  exact relative_cof_of_pointwise_pushout W f.hom g.hom i.hom j.hom hl hr
    (Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk f))
    (Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W) (Arrow.mk j))
    (Additivity.sourceι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f))
    (Additivity.targetι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk f))
    (Additivity.sourceι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk j))
    (Additivity.targetι_comparison W (inclusion W) (inclusion_cof W) (Arrow.mk j)) hf.2

/-- The actual Reedy Waldhausen structure on the category of cofibration arrows. -/
def waldhausenStructure : Waldhausen.Structure (Obj W) where
  zero := zero W
  isZero := isZero W
  cof := cof W
  weq := weq W
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := cof_iso W
  weq_iso := weq_iso W
  cof_zero X := by
    have h : (isZero W).to_ X = fromZero W X := (isZero W).eq_of_src _ _
    rw [h]
    exact cof_fromZero W X
  pushout_exists f g hf := by
    obtain ⟨P, i, j, h, _, _, _⟩ := exists_pointwise_pushout W f g hf
    exact ⟨P, i, j, h⟩
  cof_pushout := cof_pushout W
  gluing := by
    intro A B D P A' B' D' P' f g i j f' g' i' j' a b d p hf hf' h h' ef eg ei ej ha hb hd
    obtain ⟨hl, hr⟩ := pointwise_of_isPushout W hf h
    obtain ⟨hl', hr'⟩ := pointwise_of_isPushout W hf' h'
    exact ⟨W.gluing a.hom.left b.hom.left d.hom.left p.hom.left hf.1 hf'.1 hl hl'
      (congrArg (fun k ↦ k.hom.left) ef) (congrArg (fun k ↦ k.hom.left) eg)
      (congrArg (fun k ↦ k.hom.left) ei) (congrArg (fun k ↦ k.hom.left) ej) ha.1 hb.1 hd.1,
      W.gluing a.hom.right b.hom.right d.hom.right p.hom.right
        (cof_middle W hf) (cof_middle W hf') hr hr'
        (congrArg (fun k ↦ k.hom.right) ef) (congrArg (fun k ↦ k.hom.right) eg)
        (congrArg (fun k ↦ k.hom.right) ei) (congrArg (fun k ↦ k.hom.right) ej) ha.2 hb.2 hd.2⟩

/-- Source projection preserves every genuine zero object. -/
theorem source_isZero {X : Obj W} (hX : IsZero X) : IsZero ((source W).obj X) :=
  W.isZero.of_iso ((source W).mapIso (hX.iso (isZero W)))

/-- Middle projection preserves every genuine zero object. -/
theorem middle_isZero {X : Obj W} (hX : IsZero X) : IsZero ((middle W).obj X) :=
  W.isZero.of_iso ((middle W).mapIso (hX.iso (isZero W)))

/-- The original subobject functor is genuinely Waldhausen-exact. -/
theorem source_exact : IsExact (waldhausenStructure W).cof (waldhausenStructure W).weq W.cof
    W.weq (source W) where
  zero := source_isZero W
  cofibration _ h := h.1
  weak _ h := h.1
  pushout hf h := (pointwise_of_isPushout W hf h).1

/-- The original middle-object functor is genuinely Waldhausen-exact. -/
theorem middle_exact : IsExact (waldhausenStructure W).cof (waldhausenStructure W).weq W.cof
    W.weq (middle W) where
  zero := middle_isZero W
  cofibration _ h := cof_middle W h
  weak _ h := h.2
  pushout hf h := (pointwise_of_isPushout W hf h).2

end CategoryTheory.Waldhausen.ExtensionCategory
