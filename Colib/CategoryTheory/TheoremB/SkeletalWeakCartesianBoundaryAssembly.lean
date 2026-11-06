/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremB.SkeletalBoundary
public import Colib.CategoryTheory.TheoremB.SkeletalCartesianAssembly
public import Colib.Topology.HomotopyPullback.WeakCalculus

/-!
# Original incoming boundary squares for arbitrary coefficient maps

An independent geometric map and coefficient map give a genuine Cartesian
product square. Exact realized outer-product coordinates and actual coproduct
cocones then give the original incoming boundary face for any natural
transformation of coefficient diagrams. No weakness of that transformation is
assumed; the boundary-to-cell square is already genuinely Cartesian.


Implementation provenance:
`Quillen/CategoryTheory/TheoremB/SkeletalWeakCartesianBoundaryAssembly.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.TheoremA


noncomputable section
open Topology TopCat SSet Topology.HomotopyPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.TheoremB.Skeletal
open TheoremA

/-- Independent coefficient and geometric maps give an actual Cartesian
product square, with the prescribed constant-path comparison. -/
theorem coefficientProduct_cartesian {X Y K L : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace K] [TopologicalSpace L]
    (r : C(X, Y)) (k : C(K, L)) :
    Cartesian (r.prodMap (ContinuousMap.id K)) (r.prodMap (ContinuousMap.id L))
      ((ContinuousMap.id X).prodMap k) ((ContinuousMap.id Y).prodMap k) rfl := by
  let h := cartesianIdentity r
  refine ⟨(h.equiv.prodCongr (HomotopyPullback.identityHomotopyEquiv k)).trans
    (HomotopyPullback.prodHomeomorph r (ContinuousMap.id L) (ContinuousMap.id Y) k).toHomotopyEquiv,
      ?_⟩
  apply ContinuousMap.ext
  intro z
  change HomotopyPullback.prodHomeomorph r (ContinuousMap.id L) (ContinuousMap.id Y) k
    (h.equiv.toFun z.1,(HomotopyPullback.identityHomotopyEquiv k).toFun z.2) = _
  rw [h.equiv_toFun,HomotopyPullback.identityHomotopyEquiv_toFun]
  rfl

/-- Realization preserves the strictly commuting outer-product square for
an arbitrary original coefficient map. -/
theorem coefficientOuter_square {K L X Y : SSet.{u}} (k : K ⟶ L) (r : X ⟶ Y) :
    realizationFunctor.map (outerProductMap (X := X) k) ≫
      realizationFunctor.map (outerProductCoefficientMap r) =
    realizationFunctor.map (outerProductCoefficientMap r) ≫
      realizationFunctor.map (outerProductMap (X := Y) k) := by
  rw [← Functor.map_comp,← Functor.map_comp]
  rfl

/-- The original realized outer-product square is genuinely Cartesian for
any coefficient map and any locally compact realized geometric domains. -/
theorem coefficientOuter_cartesian {K L X Y : SSet.{u}}
    [LocallyCompactSpace |K|] [LocallyCompactSpace |L|]
    (k : K ⟶ L) (r : X ⟶ Y) :
    Cartesian (realizationFunctor.map (outerProductCoefficientMap (K := K) r)).hom
      (realizationFunctor.map (outerProductCoefficientMap (K := L) r)).hom
      (realizationFunctor.map (outerProductMap (X := X) k)).hom
      (realizationFunctor.map (outerProductMap (X := Y) k)).hom
      (congrArg TopCat.Hom.hom (coefficientOuter_square k r)) := by
  apply cartesianOfCoordinates _ _ _ _ _
    ((SSet.toTop.map r).hom.prodMap (ContinuousMap.id |K|))
    ((SSet.toTop.map r).hom.prodMap (ContinuousMap.id |L|))
    ((ContinuousMap.id |X|).prodMap (SSet.toTop.map k).hom)
    ((ContinuousMap.id |Y|).prodMap (SSet.toTop.map k).hom) rfl
    (TopCat.homeoOfIso (realizedOuterProductIso K X))
    (TopCat.homeoOfIso (realizedOuterProductIso L X))
    (TopCat.homeoOfIso (realizedOuterProductIso K Y))
    (TopCat.homeoOfIso (realizedOuterProductIso L Y))
  · exact congrArg TopCat.Hom.hom (realizedOuterProductIso_coefficient (B := K) r).symm
  · exact congrArg TopCat.Hom.hom (realizedOuterProductIso_coefficient (B := L) r).symm
  · exact congrArg TopCat.Hom.hom (realizedOuterProductIso_domain (X := X) k).symm
  · exact congrArg TopCat.Hom.hom (realizedOuterProductIso_domain (X := Y) k).symm
  · exact coefficientProduct_cartesian (SSet.toTop.map r).hom (SSet.toTop.map k).hom

variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

/-- The original incoming boundary face of the replacement successor square
is genuinely Cartesian for an arbitrary natural transformation. -/
theorem coefficientReplacementBoundary_cartesian (n : ℕ) :
    Cartesian (cellBoundaryProjection η n).hom (cellProjection η n).hom
      (boundaryLeg H n).hom (boundaryLeg J n).hom
      (congrArg TopCat.Hom.hom (cellBoundarySquare η n)) := by
  let : CompactSpace |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
  let : T2Space |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
  apply cartesianCofan
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCellBoundary H s))
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCell H s))
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCellBoundary J s))
    (fun s : (nerve D).nonDegenerate n ↦ realizationFunctor.obj (replacementCell J s))
    (realizedCofan (replacementCellBoundary H)) (realizedCofan (replacementCell H))
    (realizedCofan (replacementCellBoundary J)) (realizedCofan (replacementCell J))
    (realizedBisimplicialSigmaIsColimit _) (realizedBisimplicialSigmaIsColimit _)
    (realizedBisimplicialSigmaIsColimit _) (realizedBisimplicialSigmaIsColimit _)
    (cellBoundaryProjection η n) (cellProjection η n)
    (boundaryLeg H n) (boundaryLeg J n) (cellBoundarySquare η n)
    (fun s ↦ realizationFunctor.map (outerProductCoefficientMap
      (K := (∂Δ[n] : SSet.{u})) (η.app (s.1.obj 0))))
    (fun s ↦ realizationFunctor.map (outerProductCoefficientMap
      (K := (Δ[n] : SSet.{u})) (η.app (s.1.obj 0))))
    (fun s ↦ realizationFunctor.map (replacementCellBoundaryι H s))
    (fun s ↦ realizationFunctor.map (replacementCellBoundaryι J s))
    (fun s ↦ coefficientOuter_square ∂Δ[n].ι (η.app (s.1.obj 0)))
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ =
      realizationFunctor.map _ ≫ realizationFunctor.map _
    rw [← Functor.map_comp,← Functor.map_comp]
    rfl
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ =
      realizationFunctor.map _ ≫ realizationFunctor.map _
    rw [← Functor.map_comp,← Functor.map_comp]
    rfl
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ =
      realizationFunctor.map _ ≫ realizationFunctor.map _
    rw [← Functor.map_comp,← Functor.map_comp]
    rfl
  · intro s
    change realizationFunctor.map _ ≫ realizationFunctor.map _ =
      realizationFunctor.map _ ≫ realizationFunctor.map _
    rw [← Functor.map_comp,← Functor.map_comp]
    rfl
  · intro s
    exact coefficientOuter_cartesian ∂Δ[n].ι (η.app (s.1.obj 0))

/-- The complete weak incoming boundary comparison, with the original point
and entire constant path, follows from its genuine Cartesian geometry. -/
theorem replacementBoundary_weakCartesian (n : ℕ) :
    WeakCartesian (cellBoundaryProjection η n).hom (cellProjection η n).hom
      (boundaryLeg H n).hom (boundaryLeg J n).hom
      (congrArg TopCat.Hom.hom (cellBoundarySquare η n)) :=
  (coefficientReplacementBoundary_cartesian η n).weak

end CategoryTheory.TheoremB.Skeletal
