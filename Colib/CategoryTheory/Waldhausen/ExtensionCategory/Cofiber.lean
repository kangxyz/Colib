/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Structure
public import Colib.CategoryTheory.Waldhausen.Additivity.CofibrationSequence
public import Colib.CategoryTheory.Waldhausen.Additivity.PushoutPreservation

/-! # The exact cofiber functor and its genuine structural sequence

Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/Cofiber.lean` at Quillen commit
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

/-- The source-to-middle transformation satisfies the actual relative condition. -/
theorem inclusion_isCofibrationTransformation :
    Additivity.IsCofibrationTransformation W (inclusion W) (waldhausenStructure W) where
  app_cof := inclusion_cof W
  relative_cof _ hf := hf.2

/-- The functor of canonical arrows from each extension to the chosen zero extension. -/
def terminalArrow : Obj W ⥤ Arrow (Obj W) where
  obj X := Arrow.mk (toZero W X)
  map {X Y} f := Arrow.homMk f (𝟙 _) ((isZero W).eq_of_tgt _ _)
  map_id X := by apply Arrow.hom_ext <;> rfl
  map_comp f g := by apply Arrow.hom_ext <;> simp

/-- The actual quotient is the categorical pushout of the original cofibration
along the canonical map to the chosen zero object. -/
def cofiber : Obj W ⥤ C := terminalArrow W ⋙ relativeFunctor W

/-- The actual middle-to-cofiber quotient projection. -/
def quotient : middle W ⟶ cofiber W :=
  Functor.whiskerLeft (terminalArrow W)
    (Additivity.sourceιNatTrans W (inclusion W) (inclusion_cof W))

/-- The displayed quotient really is the cofiber pushout of the original arrow. -/
theorem cofiber_isPushout (X : Obj W) :
    IsPushout ((inclusion W).app X) (W.isZero.from_ ((source W).obj X))
      ((quotient W).app X) (W.isZero.to_ ((cofiber W).obj X)) := by
  have h := Additivity.pushoutFunctor_isPushout W (inclusion W) (inclusion_cof W)
    ((terminalArrow W).obj X)
  change IsPushout ((inclusion W).app X) (W.isZero.from_ ((source W).obj X))
    ((quotient W).app X)
    (Additivity.targetι W (inclusion W) (inclusion_cof W) ((terminalArrow W).obj X)) at h
  have he : Additivity.targetι W (inclusion W) (inclusion_cof W) ((terminalArrow W).obj X) =
      W.isZero.to_ ((cofiber W).obj X) := W.isZero.eq_of_src _ _
  rwa [he] at h

/-- The actual cofiber functor is exact for the proved Reedy Waldhausen structure. -/
theorem cofiber_exact :
    IsExact (waldhausenStructure W).cof (waldhausenStructure W).weq W.cof W.weq (cofiber W) where
  zero hX := Additivity.pushoutFunctor_obj_isZero W (inclusion W) (inclusion_cof W)
    (waldhausenStructure W) (source_exact W) (middle_exact W)
    ((terminalArrow W).obj _) hX (isZero W)
  cofibration f hf := Additivity.pushoutFunctor_map_cof W (inclusion W) (waldhausenStructure W)
    (source_exact W) (inclusion_isCofibrationTransformation W) ((terminalArrow W).map f)
    hf ((cof W).id_mem _)
  weak f hf := Additivity.pushoutFunctor_map_weak_of_exact W (inclusion W) (waldhausenStructure W)
    (source_exact W) (middle_exact W) (inclusion_isCofibrationTransformation W) ((terminalArrow
      W).map f)
    hf ((weq W).id_mem _)
  pushout {A B D P} {f g i j} hf h := by
    apply Additivity.pushoutFunctor_map_isPushout_of_exact W (inclusion W) (inclusion_cof W)
      (waldhausenStructure W) (source_exact W) (middle_exact W)
      ((terminalArrow W).map f) ((terminalArrow W).map g)
      ((terminalArrow W).map i) ((terminalArrow W).map j)
    · simpa only [← Functor.map_comp] using congrArg (terminalArrow W).map h.w
    · exact hf
    · exact (cof W).id_mem _
    · exact h
    · exact IsPushout.of_id_fst

/-- The universal source/middle/cofiber sequence is genuinely structural:
all exactness and relative-cofibration conditions have been proved. -/
theorem isCofibrationSequence :
    Additivity.IsCofibrationSequence (waldhausenStructure W) W (inclusion W) (quotient W) where
  exactF := source_exact W
  exactG := middle_exact W
  exactH := cofiber_exact W
  cofibration := inclusion_isCofibrationTransformation W
  cofiber := cofiber_isPushout W

end CategoryTheory.Waldhausen.ExtensionCategory
