/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Cokernel
public import Colib.CategoryTheory.ExactCategory.Functor.QConstruction
public import Colib.CategoryTheory.ExactCategory.ExtensionTotal
public import Colib.CategoryTheory.Subdivision.Functor

/-!
# Exact functors on total extensions and their original cokernels

## Implementation provenance

Adapted from `Quillen/CategoryTheory/ExactCategory/ExtensionFunctor.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactFunctor
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')

/-- The map acts on the original subdivision model of total extensions. -/
def extensionTotalFunctor : E.ExtensionTotal ⥤ E'.ExtensionTotal :=
  Subdivision.map F.inflationFunctor

/-- The original middle-object projection commutes with the exact functor. -/
theorem extensionTotalFunctor_middle :
    F.extensionTotalFunctor ⋙ E'.extensionTotalMiddle = E.extensionTotalMiddle ⋙ F.toFunctor := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro x y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- The genuine original quotient presentation after applying the exact functor. -/
def mapExtensionQuotientData (x : E.ExtensionTotal) :
    E'.ExtensionQuotientData (F.extensionTotalFunctor.obj x) where
  obj := F.toFunctor.obj (E.extensionQuotientData x).obj
  π := F.toFunctor.map (E.extensionQuotientData x).π
  zero := by
    change F.toFunctor.map x.fiber.unop.hom.hom ≫
      F.toFunctor.map (E.extensionQuotientData x).π = 0
    rw [← F.toFunctor.map_comp, (E.extensionQuotientData x).zero, F.toFunctor.map_zero]
  conflation := F.map_conflation _ (E.extensionQuotientData x).conflation

/-- The canonical comparison of the mapped quotient and the chosen target quotient. -/
def extensionQuotientIso (x : E.ExtensionTotal) :
    F.toFunctor.obj (E.extensionQuotientData x).obj ≅
      (E'.extensionQuotientData (F.extensionTotalFunctor.obj x)).obj :=
  (F.mapExtensionQuotientData x).iso E' (E'.extensionQuotientData _)

/-- The canonical comparison retains the original quotient projection. -/
@[reassoc] theorem extensionQuotientIso_π (x : E.ExtensionTotal) :
    F.toFunctor.map (E.extensionQuotientData x).π ≫ (F.extensionQuotientIso x).hom =
      (E'.extensionQuotientData (F.extensionTotalFunctor.obj x)).π :=
  (F.mapExtensionQuotientData x).π_iso_hom E' (E'.extensionQuotientData _)

end CategoryTheory.ExactCategory.ExactFunctor
