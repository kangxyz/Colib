/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Limits/Shapes/CoproductCokernel.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
 # Adding an identity summand leaves the cokernel unchanged -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory
namespace CategoryTheory.Limits
variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/-- The cokernel of `id ⨿ i` is the original cokernel, with quotient map `[0,p]`. -/
def isCokernelCoprodId {A B Q : C} (S : C) (i : A ⟶ B) (p : B ⟶ Q)
    (z : i ≫ p = 0) (hp : IsColimit (CokernelCofork.ofπ p z))
    [HasBinaryCoproduct S A] [HasBinaryCoproduct S B] :
    IsColimit (CokernelCofork.ofπ (coprod.desc (0 : S ⟶ Q) p)
      (show coprod.map (𝟙 S) i ≫ coprod.desc (0 : S ⟶ Q) p = 0 by
        ext <;> simp [z])) := by
  let : Epi p := Cofork.IsColimit.epi hp
  let : Epi (coprod.desc (0 : S ⟶ Q) p) := ⟨by
    intro T a b hab
    apply (cancel_epi p).1
    simpa using congrArg (fun t => (coprod.inr : B ⟶ S ⨿ B) ≫ t) hab⟩
  refine CokernelCofork.IsColimit.ofπ' _ _ ?_
  intro T a ha
  have h : i ≫ coprod.inr ≫ a = 0 := by
    have h' := congrArg (fun m => (coprod.inr : A ⟶ S ⨿ A) ≫ m) ha
    simpa only [coprod.inr_map_assoc, comp_zero] using h'
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc' hp (coprod.inr ≫ a) h
  refine ⟨l, ?_⟩
  apply coprod.hom_ext
  · have h' := congrArg (fun m => (coprod.inl : S ⟶ S ⨿ A) ≫ m) ha
    simpa using h'.symm
  · simpa using hl

end CategoryTheory.Limits
