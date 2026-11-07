/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremA.Augmentations

/-!
Adapted from `Quillen/CategoryTheory/TheoremA/ReplacementEntry.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps retained.

# Original object entries in the strict simplicial replacement -/

@[expose] public section
noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u
namespace CategoryTheory.TheoremA
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u}) (d : D)

/-- The original diagram object enters using the constant chain at that object. -/
def replacementEntry : H.obj d ⟶ replacementDiagonal H where
  app p := ↾fun x ↦ ⟨(Functor.const _).obj d, x⟩
  naturality p q α := by
    ext x : 3
    change (⟨(Functor.const _).obj d, (H.obj d).map α x⟩ :
      (replacementDiagonal H).obj q) =
      ⟨(Functor.const _).obj d, (H.obj d).map α ((H.map (𝟙 d)).app p x)⟩
    rw [H.map_id]
    rfl

/-- Under the source augmentation the entry is precisely the original comma projection. -/
theorem replacementEntry_diagonalSourceMap {C : Type u} [SmallCategory C]
    (F : C ⥤ D) (d : D) :
    replacementEntry (commaNerveDiagram F) d ≫ diagonalSourceMap F =
      nerveMap (CostructuredArrow.proj F d) := by
  apply NatTrans.ext
  funext p
  rfl

end CategoryTheory.TheoremA
