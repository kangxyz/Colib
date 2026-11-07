/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremA.ReplacementEntry
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
Adapted from `Quillen/CategoryTheory/TheoremA/InitialReplacement.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# The canonical replacement comparison from an initial object

The original initial-object transition maps form the specified constant-to-diagram
transformation. Its composite with the constant-diagram entry is strictly the
original replacement entry, before taking realization or homology.
-/

@[expose] public section
noncomputable section
open SSet TopCat _root_.stdSimplex
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremA
variable {D : Type u} [SmallCategory D]

/-- The canonical original transition maps from an initial object form a diagram transformation. -/
def initialReplacementComparison (H : D ⥤ SSet.{u}) (i : D) (hi : IsInitial i) :
    (Functor.const D).obj (H.obj i) ⟶ H where
  app d := H.map (hi.to d)
  naturality d e f := by
    change 𝟙 (H.obj i) ≫ H.map (hi.to e) = H.map (hi.to d) ≫ H.map f
    rw [Category.id_comp, ← H.map_comp, hi.hom_ext (hi.to d ≫ f) (hi.to e)]

/-- The constant replacement comparison retains the exact original entry. -/
theorem initialReplacementComparison_entry (H : D ⥤ SSet.{u}) (i : D)
    (hi : IsInitial i) :
    replacementEntry ((Functor.const D).obj (H.obj i)) i ≫
        diagonalMap (simplicialReplacementMap (initialReplacementComparison H i hi)) =
      replacementEntry H i := by
  apply NatTrans.ext
  funext p
  apply ConcreteCategory.hom_ext
  intro x
  change (⟨(Functor.const _).obj i, (H.map (hi.to i)).app p x⟩ :
    (replacementDiagonal H).obj p) = ⟨(Functor.const _).obj i, x⟩
  rw [hi.hom_ext (hi.to i) (𝟙 i), H.map_id]
  rfl

end CategoryTheory.TheoremA
