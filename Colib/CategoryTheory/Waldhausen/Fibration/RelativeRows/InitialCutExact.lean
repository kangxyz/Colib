/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.InitialCutArrows

/-! # Genuine exactness of the cutoff arrow-valued functor

Actual Reedy cube cofibrancy is transported back through the proved row/arrow
interchange and reflected by the original relative-row inclusion. Zero,
weak equivalences and pushouts retain the original component diagrams.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/InitialCutExact.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C} (N : NestedWeakEquivalences V)

/-- The actual ambient cutoff square satisfies the original Reedy row-arrow condition. -/
theorem ambientCutArrow_map_cof {n : SimplexCategory} {X Y : Obj N n} (f : X ⟶ Y)
    (hf : (waldhausenStructure N n).cof f) :
    ExtensionCategory.cof (QuotientRows.waldhausenStructure V (addInitial.obj n))
      ((ambientCutArrow N n).map f) := by
  have h := QuotientRows.rowsToReedy_cof V (cutArrowRows_map_cof N f hf)
  change ExtensionCategory.cof (QuotientRows.waldhausenStructure V (addInitial.obj n))
    ((QuotientRows.reedyToRows V (addInitial.obj n) ⋙ QuotientRows.rowsToReedy V (addInitial.obj
      n)).map
      ((ambientCutArrow N n).map f)) at h
  rw [QuotientRows.reedyToRows_rowsToReedy] at h
  exact h

/-- The original acyclicity-tag inclusion reflects the genuine relative cutoff condition. -/
theorem cutArrow_map_cof {n : SimplexCategory} {X Y : Obj N n} (f : X ⟶ Y)
    (hf : (waldhausenStructure N n).cof f) :
    ExtensionCategory.cof (waldhausenStructure N n) ((cutArrow N n).map f) :=
  ExtensionCategory.cof_of_postcompose (waldhausenStructure N n)
    (QuotientRows.waldhausenStructure V (addInitial.obj n)) (forget_exact N n)
    (fun {_ _} _ h ↦ h) (ambientCutArrow_map_cof N f hf)

/-- The actual cutoff arrow-valued functor is genuinely exact. -/
theorem cutArrow_exact (n : SimplexCategory) :
    IsExact (waldhausenStructure N n).cof (waldhausenStructure N n).weq
      (ExtensionCategory.waldhausenStructure (waldhausenStructure N n)).cof
      (ExtensionCategory.waldhausenStructure (waldhausenStructure N n)).weq (cutArrow N n) where
  zero h := ExtensionCategory.isZero_of_components (waldhausenStructure N n) _
    ((cutFunctor_exact N n).zero h) h
  cofibration f hf := cutArrow_map_cof N f hf
  weak f hf := ⟨(cutFunctor_exact N n).weak f hf, hf⟩
  pushout hf h := IsPushout.of_map_of_faithful (ExtensionCategory.forget (waldhausenStructure N n))
    (ExtensionCategory.arrow_isPushout _ _ _ _ ((cutFunctor_exact N n).pushout hf h) h)

/-- The original cutoff-to-identity transformation has the genuine relative cofibration property. -/
theorem cutToId_isCofibrationTransformation (n : SimplexCategory) :
    Additivity.IsCofibrationTransformation (waldhausenStructure N n)
      (cutToId N n) (waldhausenStructure N n) where
  app_cof := cutToId_cof N n
  relative_cof f hf := (cutArrow_map_cof N f hf).2

end CategoryTheory.Waldhausen.Fibration.RelativeRows
