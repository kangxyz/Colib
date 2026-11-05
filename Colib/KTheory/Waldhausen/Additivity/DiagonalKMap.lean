/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedZeroMaps
public import Colib.KTheory.Waldhausen.Additivity.DiagonalNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.Homeomorph
public import Colib.Topology.Realization.EdgePath


/-! # Exact identification of normalized diagonal maps with public K-maps

Adapted from Quillen/Waldhausen/Additivity/DiagonalKMap.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual diagonal comparison is already
a homeomorphism, so its forward group equivalence is constructed directly.
No unbased homotopy-equivalence or subdivision equivalence theorem is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v

namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (V : Structure C) (W : Structure D) {F : C ⥤ D}
variable (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The original realization of the canonical rebased functor is based. -/
theorem rebasedDeloopingMap_basepoint :
    deloopingMap hF.rebase V.kBasepoint = W.kBasepoint := by
  have h := deloopingMap_basepoint hF.rebase V.zero V.isZero
  simpa only [CategoryTheory.rebaseFunctor_obj_base] using h

private theorem groupsMapOfZeroEq_eq_piMap {J : C ⥤ D}
    (hJ : IsExact V.cof V.weq W.cof W.weq J)
    (Z : C) (hZ : IsZero Z) (Z' : D) (hZ' : IsZero Z') (h : J.obj Z = Z') (n : ℕ)
    (hb : deloopingMap hJ (basepoint V.cof V.weq Z hZ) = basepoint W.cof W.weq Z' hZ') :
    groupsMapOfZeroEq hJ Z hZ Z' hZ' h n = HomotopyGroup.piMap n (deloopingMap hJ).hom hb := by
  subst Z'
  rfl

/-- The displayed based map is exactly the original public `KMap`. -/
theorem KMap_eq_rebased_piMap (n : ℕ) :
    KMap hF n = HomotopyGroup.piMap n (deloopingMap hF.rebase).hom
      (rebasedDeloopingMap_basepoint V W hF) :=
  groupsMapOfZeroEq_eq_piMap V W hF.rebase V.zero V.isZero W.zero W.isZero
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) n (rebasedDeloopingMap_basepoint V W hF)

/-- The actual diagonal grid map preserves the original chosen zero point. -/
theorem rebasedDiagonalMap_basepoint :
    realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hF.rebase)
      (SSet.realizationPoint (diagonalZeroVertex V)) = SSet.realizationPoint
        (diagonalZeroVertex W) := by
  exact (SSet.realizationPoint_naturality _ _).trans
    (congrArg SSet.realizationPoint (rebasedGridMap_zero V W hF (op ⦋0⦌) (op ⦋0⦌)))

/-- The canonical based map on the independent-grid diagonal. -/
def diagonalKMap (n : ℕ) :
    HomotopyGroup.Pi (n + 1) |SSet.diagonalSSet (bisimplicialSSet V)|
      (SSet.realizationPoint (diagonalZeroVertex V)) →*
    HomotopyGroup.Pi (n + 1) |SSet.diagonalSSet (bisimplicialSSet W)|
      (SSet.realizationPoint (diagonalZeroVertex W)) :=
  HomotopyGroup.piMap n (realizedDiagonalMap (bisimplicialSSetMap V.cof V.weq hF.rebase))
    (rebasedDiagonalMap_basepoint V W hF)

omit W hF in
/-- The exact diagonal identification retains the actual original basepoint. -/
theorem diagonalRealization_basepoint :
    SSet.toTop.map (bisimplicialDiagonalIso V).hom (SSet.realizationPoint (diagonalZeroVertex V)) =
      V.kBasepoint :=
  SSet.realizationPoint_naturality _ _

omit W hF in
/-- The original diagonal identification induces its actual forward group isomorphism. -/
def diagonalPiEquiv (n : ℕ) :
    HomotopyGroup.Pi (n + 1) |SSet.diagonalSSet (bisimplicialSSet V)|
      (SSet.realizationPoint (diagonalZeroVertex V)) ≃* V.K n :=
  HomotopyGroup.homeomorphPiEquiv
    (TopCat.homeoOfIso (SSet.toTop.mapIso (bisimplicialDiagonalIso V)))
    (diagonalRealization_basepoint V) n

/-- The actual grid comparison square agrees with the original public K-map. -/
theorem diagonalKMap_naturality (n : ℕ) :
    (diagonalPiEquiv W n).toMonoidHom.comp (diagonalKMap V W hF n) =
      (KMap hF n).comp (diagonalPiEquiv V n).toMonoidHom := by
  rw [KMap_eq_rebased_piMap V W hF n]
  ext q
  refine Quotient.inductionOn q (fun p ↦ ?_)
  apply congrArg Quotient.mk'
  ext t
  exact DFunLike.congr_fun (realizedDiagonalMap_exact_naturality V W hF.rebase) (p t)

end CategoryTheory.Waldhausen.Additivity
