/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Cofinality.KZeroNaturality
public import Colib.KTheory.Waldhausen.Cofinality.GeneralDense

/-! # Injective original coarse grading maps in independent universes
Implementation provenance: `Quillen/Waldhausen/Cofinality/ImageReflection.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.Cofinality.Grading
private lemma KMap_injective_transport {C D : Type u} [Category.{v} C] [Category.{v} D]
    {W W' : Structure C} {V V' : Structure D} {F : C ⥤ D}
    (hW : W = W') (hV : V = V')
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hF' : IsExact W'.cof W'.weq V'.cof V'.weq F) :
    Function.Injective (KMap hF 0) ↔ Function.Injective (KMap hF' 0) := by
  subst W'
  subst V'
  rfl

variable {C D G H : Type u} [Category.{v} C] [Category.{v} D]
  [AddCommGroup G] [AddCommGroup H] {W : Structure C} {V : Structure D}
  (d : Grading W G) (e : Grading V H) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (φ : G →+ H) (hφ : ∀ A, e.value (F.obj A) = φ (d.value A))

include hF hφ in
/-- The same exact functor preserves the original grade-equality classes. -/
theorem coarseMap_exact_general :
    IsExact d.coarseStructure.cof d.coarseStructure.weq
      e.coarseStructure.cof e.coarseStructure.weq F where
  zero := hF.zero
  cofibration := hF.cofibration
  pushout := hF.pushout
  weak {A B} f hf := by
    change e.value (F.obj A) = e.value (F.obj B)
    rw [hφ A,hφ B]
    exact congrArg φ hf

variable (Dd : Fibration.RowFactorization.JointData (.refl W))
  (De : Fibration.RowFactorization.JointData (.refl V))

include Dd De in
/-- The actual common-universe homeomorphisms transport injectivity back to
the unchanged original K-map. -/
theorem coarseKMap_injective_general (hφi : Function.Injective φ) :
    Function.Injective (KMap (coarseMap_exact_general d e hF φ hφ) 0) := by
  let φ' : ULift.{v} G →+ ULift.{v} H :=
    AddEquiv.ulift.symm.toAddMonoidHom.comp (φ.comp AddEquiv.ulift.toAddMonoidHom)
  have hφ' (A : AsSmall.{0} C) : e.asSmallGrading.value ((asSmallFunctor F).obj A) =
      φ' (d.asSmallGrading.value A) := ULift.ext (hφ (AsSmall.down.obj A))
  have hi := coarseKMap_injective d.asSmallGrading e.asSmallGrading hF.asSmall
    φ' hφ' Dd.reflexiveAsSmall.sourceFactorization De.reflexiveAsSmall.sourceFactorization
    (by intro a b h; exact ULift.ext (hφi (congrArg ULift.down h)))
  have hi' := (KMap_injective_transport d.asSmallGrading_coarseStructure
    e.asSmallGrading_coarseStructure _
    (coarseMap_exact_general d e hF φ hφ).asSmall).mp hi
  intro x y hxy
  apply (d.coarseStructure.asSmallKEquiv 0).injective
  apply hi'
  have hn := asSmallKEquiv_naturality (coarseMap_exact_general d e hF φ hφ) 0
  exact (DFunLike.congr_fun hn x).symm.trans
    ((congrArg (e.coarseStructure.asSmallKEquiv 0) hxy).trans (DFunLike.congr_fun hn y))

end CategoryTheory.Waldhausen.Cofinality.Grading

/-! # Original dense-image K-zero reflection from actual membership reflection -/
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} [HasBinaryCoproducts C] [HasBinaryCoproducts D]
  {P : ObjectProperty C} {Q : ObjectProperty D}
  (h : DenseCofiberData W P) (k : DenseCofiberData V Q) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hp : ∀ A, P A ↔ Q (F.obj A))
  (Dd : Fibration.RowFactorization.JointData (.refl W))
  (De : Fibration.RowFactorization.JointData (.refl V))
  (hsd : Fibration.RowFactorization.SecondEndpointSection (.refl W) Dd)
  (hse : Fibration.RowFactorization.SecondEndpointSection (.refl V) De)

include hp Dd De hsd hse in
/-- The exact original K-zero image is reflected by an exact functor that
reflects the actual dense object property. No object presentation of K-zero
and no surjectivity of either original restriction map is used. -/
theorem KMap_mem_inclusion_range_iff (x : W.K 0) :
    KMap hF 0 x ∈ (KMap k.inclusion_exact 0).range ↔
      x ∈ (KMap h.inclusion_exact 0).range := by
  let φ := h.classMap k hF (fun A ↦ (hp A).mp)
  have hφ (A : C) : k.grading.value (F.obj A) = φ (h.grading.value A) := rfl
  let hc := Grading.coarseMap_exact_general h.grading k.grading hF φ hφ
  have hi : Function.Injective (KMap hc 0) :=
    Grading.coarseKMap_injective_general h.grading k.grading hF φ hφ Dd De
      (h.classMap_injective k hF (fun A ↦ (hp A).mp) (fun A ↦ (hp A).mpr))
  have hn : (KMap hc 0).comp (KMap (Fibration.changeWeak_exact h.grading.nested) 0) =
      (KMap (Fibration.changeWeak_exact k.grading.nested) 0).comp (KMap hF 0) := by
    rw [CategoryTheory.Waldhausen.KMap_comp_KMap, CategoryTheory.Waldhausen.KMap_comp_KMap]
  rw [k.range_inclusion_KMap_general De hse 0, h.range_inclusion_KMap_general Dd hsd 0]
  change KMap (Fibration.changeWeak_exact k.grading.nested) 0 (KMap hF 0 x) = 1 ↔ _
  have hn' := DFunLike.congr_fun hn x
  change KMap hc 0 (KMap (Fibration.changeWeak_exact h.grading.nested) 0 x) =
    KMap (Fibration.changeWeak_exact k.grading.nested) 0 (KMap hF 0 x) at hn'
  rw [← hn']
  change KMap hc 0 (KMap (Fibration.changeWeak_exact h.grading.nested) 0 x) = 1 ↔
    KMap (Fibration.changeWeak_exact h.grading.nested) 0 x = 1
  constructor
  · intro hh
    exact hi (hh.trans (map_one (KMap hc 0)).symm)
  · intro hh
    rw [hh,map_one]

end CategoryTheory.Waldhausen.Cofinality.DenseCofiberData
