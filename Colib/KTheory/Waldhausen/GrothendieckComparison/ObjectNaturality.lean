/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.WeakRelations
public import Colib.CategoryTheory.Waldhausen.Rows.OneRowNaturality
public import Colib.KTheory.Waldhausen.Functoriality
public import Colib.Topology.Homotopy.HomotopyGroup.FundamentalGroup

/-! # Original exact functors preserve actual Waldhausen object-loop classes

Strict chosen-zero preservation is checked on the unchanged original one-step
row. The general statement then uses exactly the canonical zero rebasing
already built into the public KMap and its original categorical isomorphism.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/ObjectNaturality.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v
namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The unchanged S-map sends the original object simplex to its exact image
when the original chosen zero is preserved literally. -/
theorem sSetMap_kZeroObjectSimplex (h0 : F.obj V.zero = W.zero) (A : C) :
    (sSetMap hF).app (op ⦋1⦌) (V.kZeroObjectSimplex A) =
      W.kZeroObjectSimplex (F.obj A) := by
  apply Subtype.ext
  change (Structure.intervalProjection ⦋1⦌ ⋙ QuotientRows.oneDiagram V A) ⋙ F =
    Structure.intervalProjection ⦋1⦌ ⋙ QuotientRows.oneDiagram W (F.obj A)
  rw [Functor.assoc, QuotientRows.oneDiagram_postcompose V W hF h0]

/-- The actual object-loop path is natural under a strictly zero-preserving exact functor. -/
theorem deloopingMap_kZeroObjectLoop (h0 : F.obj V.zero = W.zero) (A : C) :
    ((V.kZeroObjectLoop A).map (deloopingMap hF).hom.continuous).cast
      (deloopingMap_basepoint_of_zeroEq hF h0).symm
      (deloopingMap_basepoint_of_zeroEq hF h0).symm = W.kZeroObjectLoop (F.obj A) := by
  ext t
  change SSet.toTop.map (sSetMap hF) (realizationEdgePath (V.kZeroObjectEdge A) t) = _
  exact (realizationEdgePath_naturality_apply (sSetMap hF) (V.kZeroObjectEdge A) t).trans
    (congrArg (fun e : (sSet W.cof W.weq) _⦋1⦌ ↦
      SSet.toTop.map (SSet.yonedaEquiv.symm e) (realizationInterval t))
        (sSetMap_kZeroObjectSimplex hF h0 A))

/-- The actual based realization map retains the original canonical object class. -/
theorem piMap_kZeroObjectClass (h0 : F.obj V.zero = W.zero) (A : C) :
    HomotopyGroup.piMap 0 (deloopingMap hF).hom (deloopingMap_basepoint_of_zeroEq hF h0)
      (V.kZeroObjectClass A) = W.kZeroObjectClass (F.obj A) := by
  apply W.kZeroFundamentalGroupEquiv.injective
  change HomotopyGroup.pi1MulEquivFundamentalGroup
    (HomotopyGroup.map (deloopingMap hF).hom (deloopingMap_basepoint_of_zeroEq hF h0)
      (V.kZeroObjectClass A)) = _
  rw [HomotopyGroup.pi1MulEquivFundamentalGroup_naturality]
  change FundamentalGroup.mapOfEq _ _
    (V.kZeroFundamentalGroupEquiv (V.kZeroObjectClass A)) = _
  rw [V.kZeroFundamentalGroupEquiv_objectClass, W.kZeroFundamentalGroupEquiv_objectClass,
    FundamentalGroup.mapOfEq_apply]
  apply End.ext
  exact congrArg Path.Homotopic.Quotient.mk (deloopingMap_kZeroObjectLoop hF h0 A)

/-- The original public KMap takes each original canonical object-loop class to
its original image object, with exactly the existing zero rebasing. -/
@[simp] theorem KMap_kZeroObjectClass (A : C) :
    KMap hF 0 (V.kZeroObjectClass A) = W.kZeroObjectClass (F.obj A) := by
  rw [KMap_eq_piMap]
  exact (piMap_kZeroObjectClass hF.rebase (rebaseFunctor_obj_base _ _ _ _) A).trans
    (W.kZeroObjectClass_iso ((rebaseFunctorIso F V.zero W.zero
      ((hF.zero V.isZero).iso W.isZero)).symm.app A))

end CategoryTheory.Waldhausen
