/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Extension
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionFunctor
public import Colib.CategoryTheory.ExactCategory.ExtensionProjectionGeometry
public import Colib.CategoryTheory.ExactCategory.QSpanNaturality

/-!
# Exact-functor naturality of the original extension projection

## Implementation provenance

Adapted from `Quillen/CategoryTheory/ExactCategory/ExtensionFunctorProjection.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.ExactFunctor
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D} (F : ExactFunctor E E')
variable {x y : E.ExtensionTotal} (f : x ⟶ y)

/-- The mapped original span apex remains the actual smaller-kernel cokernel. -/
def mapExtensionProjectionCokernel :
    IsColimit (CokernelCofork.ofπ (F.toFunctor.map (E.extensionProjectionCokernel f).π)
      (show ((CategoryTheory.Subdivision.domainMap (F.extensionTotalFunctor.map f)).hom ≫
        (F.extensionTotalFunctor.obj x).fiber.unop.hom.hom) ≫
          F.toFunctor.map (E.extensionProjectionCokernel f).π = 0 by
        change (F.toFunctor.map (CategoryTheory.Subdivision.domainMap f).hom ≫
          F.toFunctor.map x.fiber.unop.hom.hom) ≫ _ = 0
        rw [← F.toFunctor.map_comp, ← F.toFunctor.map_comp,
          (E.extensionProjectionCokernel f).zero, F.toFunctor.map_zero])) := by
  let h := F.mapInflationCokernel (E.extensionProjectionCokernel f).zero
    (E.extensionProjectionCokernel f).isColimit
    (E.inflation_comp _ _ (CategoryTheory.Subdivision.domainMap f).property
      x.fiber.unop.hom.property)
  apply CokernelCofork.isColimitOfIsColimitOfIff' h
  intro W a
  change _ ↔ (F.toFunctor.map (CategoryTheory.Subdivision.domainMap f).hom ≫
    F.toFunctor.map x.fiber.unop.hom.hom) ≫ a = 0
  rw [F.toFunctor.map_comp]

/-- Canonical comparison of the two actual projection-span apexes. -/
def extensionProjectionApexIso :
    F.toFunctor.obj (E.extensionProjectionSpan f).apex ≅
      (E'.extensionProjectionSpan (F.extensionTotalFunctor.map f)).apex :=
  (F.mapExtensionProjectionCokernel f).coconePointUniqueUpToIso
    (E'.extensionProjectionCokernel (F.extensionTotalFunctor.map f)).isColimit

/-- The original quotient projection commutes with the canonical apex comparison. -/
@[reassoc] theorem extensionProjectionApexIso_π :
    F.toFunctor.map (E.extensionProjectionCokernel f).π ≫
        (F.extensionProjectionApexIso f).hom =
      (E'.extensionProjectionCokernel (F.extensionTotalFunctor.map f)).π :=
  (F.mapExtensionProjectionCokernel f).comp_coconePointUniqueUpToIso_hom
    (E'.extensionProjectionCokernel (F.extensionTotalFunctor.map f)).isColimit
    WalkingParallelPair.one

/-- The original Q arrows commute with the canonical quotient comparisons. -/
theorem extensionProjection_naturality :
    F.mapQ.map (E.extensionProjection.map f) ≫ (E'.qIsoOfIso (F.extensionQuotientIso y)).hom =
      (E'.qIsoOfIso (F.extensionQuotientIso x)).hom ≫
        E'.extensionProjection.map (F.extensionTotalFunctor.map f) := by
  let : Epi (F.toFunctor.map (E.extensionProjectionCokernel f).π) :=
    Cofork.IsColimit.epi (F.mapExtensionProjectionCokernel f)
  apply E'.qSpan_iso_naturality
    (F.toQCompatibleFunctor.mapSpan (E.extensionProjectionSpan f))
    (E'.extensionProjectionSpan (F.extensionTotalFunctor.map f))
    (F.extensionQuotientIso x) (F.extensionQuotientIso y) (F.extensionProjectionApexIso f)
  · apply (cancel_epi (F.toFunctor.map (E.extensionProjectionCokernel f).π)).1
    change F.toFunctor.map (E.extensionProjectionCokernel f).π ≫
      F.toFunctor.map (E.extensionProjectionSpan f).l ≫ _ = _
    rw [← Category.assoc, ← F.toFunctor.map_comp,
      (E.extensionProjectionCokernel f).left, F.extensionQuotientIso_π,
      ← Category.assoc, F.extensionProjectionApexIso_π,
      (E'.extensionProjectionCokernel (F.extensionTotalFunctor.map f)).left]
  · apply (cancel_epi (F.toFunctor.map (E.extensionProjectionCokernel f).π)).1
    change F.toFunctor.map (E.extensionProjectionCokernel f).π ≫
      F.toFunctor.map (E.extensionProjectionSpan f).r ≫ _ = _
    rw [← Category.assoc, ← F.toFunctor.map_comp,
      (E.extensionProjectionCokernel f).right, F.toFunctor.map_comp, Category.assoc,
      F.extensionQuotientIso_π, ← Category.assoc, F.extensionProjectionApexIso_π,
      (E'.extensionProjectionCokernel (F.extensionTotalFunctor.map f)).right]
    rfl

/-- The canonical natural isomorphism of the two unchanged original Q projections. -/
def extensionProjectionIso :
    E.extensionProjection ⋙ F.mapQ ≅ F.extensionTotalFunctor ⋙ E'.extensionProjection :=
  NatIso.ofComponents (fun x ↦ E'.qIsoOfIso (F.extensionQuotientIso x))
    (fun f ↦ F.extensionProjection_naturality f)

/-- The natural comparison uses precisely the canonical original cokernel isomorphism. -/
theorem extensionProjectionIso_hom_app (x : E.ExtensionTotal) :
    F.extensionProjectionIso.hom.app x = (E'.qIsoOfIso (F.extensionQuotientIso x)).hom := rfl

end CategoryTheory.ExactCategory.ExactFunctor
