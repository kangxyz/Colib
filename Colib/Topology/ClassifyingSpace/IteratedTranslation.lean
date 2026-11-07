/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.GroupCompletion.IteratedComma
public import Colib.Topology.ClassifyingSpace.UniverseHomotopy
public import Colib.Topology.ClassifyingSpace.GroupCompletionTranslation
public import Colib.Topology.Homotopy.Equiv.HomotopySquare

/-! # The actual realized transport square for the iterated projection -/
@[expose] public section
noncomputable section
universe u v u' v'
open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory
open scoped MonoidalLeftAction
namespace CategoryTheory.GroupCompletion.Localization
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalLeftAction C D]
attribute [local instance] firstCoordinateLeftAction

/-- The exact comma-transition square commutes through the homotopy obtained
by realizing its actual natural transformation, in arbitrary universes. -/
def iteratedCommaTranslationHomotopy {X Y : D} (s : C) (g : s ⊙ₗ X ⟶ Y) :
    ((classifyingSpaceMapUniversal (CostructuredArrow.map
      (S := iteratedSecondProjection (C := C) (D := D))
      (ActionLocalization.mkHom ⟨s, g⟩))).comp
        (classifyingSpaceMapUniversal (iteratedCommaEntry X))).Homotopy
      ((classifyingSpaceMapUniversal (iteratedCommaEntry Y)).comp
        (translationClassifyingHomotopyEquiv s).symm.toFun) := by
  have H := classifyingSpaceUniversalHomotopy (iteratedCommaTranslation s g)
  refine H.cast (classifyingSpaceMapUniversal_comp _ _) ?_
  rw [classifyingSpaceMapUniversal_comp, classifyingSpaceMapUniversal_eq]
  rfl

end CategoryTheory.GroupCompletion.Localization
