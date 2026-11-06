/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.SkeletalNaturality
public import Colib.CategoryTheory.TheoremA.SkeletalCofibrations
public import Colib.Topology.Pushout.HomotopyEquivalence
public import Colib.Topology.Homotopy.Equiv.IsoSquare
public import Colib.Topology.Realization.LocallyCompactProduct
public import Colib.Topology.Realization.FiniteHausdorff
public import Colib.Topology.MappingCylinder.HomotopyExtension

/-! Source: Quillen/CategoryTheory/TheoremA/SkeletalEquivalences.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-! # Objectwise equivalences on finite realized replacement skeleta -/
@[expose] public section

noncomputable section

open SSet TopCat CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

/-- The diagonal outer-product comparison is natural in its coefficient. -/
@[reassoc]
theorem diagonalOuterProductIso_coefficient {B X Y : SSet.{u}} (f : X ⟶ Y) :
    diagonalMap (outerProductCoefficientMap (K := B) f) ≫ (diagonalOuterProductIso B Y).hom =
      (diagonalOuterProductIso B X).hom ≫ (f ▷ B) := rfl

/-- The realization of an outer product whose outer factor is locally compact. -/
def realizedOuterProductIso (B X : SSet.{u}) [LocallyCompactSpace |B|] :
    |diagonalSSet (outerProduct B X)| ≅ (|X| ⊗ |B|) :=
  have := realizationProductComparison_isIso_of_locallyCompact X B
  SSet.toTop.mapIso (diagonalOuterProductIso B X) ≪≫
    asIso (CartesianMonoidalCategory.prodComparison SSet.toTop X B)

/-- The outer-product homeomorphism respects the prescribed coefficient map. -/
theorem realizedOuterProductIso_coefficient {B X Y : SSet.{u}} [LocallyCompactSpace |B|]
    (f : X ⟶ Y) :
    SSet.toTop.map (diagonalMap (outerProductCoefficientMap (K := B) f)) ≫
      (realizedOuterProductIso B Y).hom =
    (realizedOuterProductIso B X).hom ≫ (SSet.toTop.map f ▷ |B|) := by
  dsimp [realizedOuterProductIso]
  rw [← Functor.map_comp_assoc, diagonalOuterProductIso_coefficient, Functor.map_comp_assoc,
    prodComparison_natural_whiskerRight]
  simp only [Category.assoc]

/-- A realized coefficient equivalence induces an actual equivalence on its
enriched cell (and likewise on its boundary). -/
def realizedOuterProductHomotopyEquiv (B : SSet.{u}) [LocallyCompactSpace |B|]
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (e : ContinuousMap.HomotopyEquiv |X| |Y|) (he : e.toFun = (SSet.toTop.map f).hom) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (outerProduct B X)|
      |diagonalSSet (outerProduct B Y)| :=
  homotopyEquivOfIsoSquare _ _ (realizedOuterProductIso B X) (realizedOuterProductIso B Y)
    (realizedOuterProductIso_coefficient f)
    (e.prodCongr (ContinuousMap.HomotopyEquiv.refl |B|)) (by
      apply ContinuousMap.ext
      intro x
      change (e.toFun x.1, x.2) = _
      rw [he]
      rfl)

@[simp]
theorem realizedOuterProductHomotopyEquiv_toFun (B : SSet.{u}) [LocallyCompactSpace |B|]
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (e : ContinuousMap.HomotopyEquiv |X| |Y|) (he : e.toFun = (SSet.toTop.map f).hom) :
    (realizedOuterProductHomotopyEquiv B f e he).toFun =
      (SSet.toTop.map (diagonalMap (outerProductCoefficientMap (K := B) f))).hom := rfl

/-- Equivalences of the realized summands induce the specified equivalence
on the realization of their bisimplicial coproduct. -/
def realizedBisimplicialSigmaHomotopyEquiv {ι : Type u}
    {X Y : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (e : ∀ i, ContinuousMap.HomotopyEquiv |diagonalSSet (X i)| |diagonalSSet (Y i)|)
    (he : ∀ i, (e i).toFun = (SSet.toTop.map (diagonalMap (f i))).hom) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (bisimplicialSigma X)|
      |diagonalSSet (bisimplicialSigma Y)| :=
  homotopyEquivOfIsoSquare _ _ (realizedBisimplicialSigmaIso X)
    (realizedBisimplicialSigmaIso Y) (realizedBisimplicialSigmaIso_naturality f)
    (ContinuousMap.sigmaHomotopyEquiv e) (by
      apply ContinuousMap.ext
      intro x
      change (⟨x.1, (e x.1).toFun x.2⟩ : Σ i, |diagonalSSet (Y i)|) = _
      rw [he]
      rfl)

@[simp]
theorem realizedBisimplicialSigmaHomotopyEquiv_toFun {ι : Type u}
    {X Y : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : ∀ i, X i ⟶ Y i)
    (e : ∀ i, ContinuousMap.HomotopyEquiv |diagonalSSet (X i)| |diagonalSSet (Y i)|)
    (he : ∀ i, (e i).toFun = (SSet.toTop.map (diagonalMap (f i))).hom) :
    (realizedBisimplicialSigmaHomotopyEquiv f e he).toFun =
      (SSet.toTop.map (diagonalMap (bisimplicialSigmaMap f))).hom := rfl

variable {D : Type u} [SmallCategory D] {H K : D ⥤ SSet.{u}} (η : H ⟶ K)
    (e : ∀ d, ContinuousMap.HomotopyEquiv |H.obj d| |K.obj d|)
    (he : ∀ d, (e d).toFun = (SSet.toTop.map (η.app d)).hom)

/-- Objectwise coefficient equivalences induce equivalences of the realized cell families. -/
def realizedReplacementCellsHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (replacementCells H n)|
      |diagonalSSet (replacementCells K n)| := by
  letI : CompactSpace |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.compactSpace
  letI : T2Space |(Δ[n] : SSet.{u})| := (SimplexCategory.toTopHomeo ⦋n⦌).symm.t2Space
  exact realizedBisimplicialSigmaHomotopyEquiv
    (fun s : (nerve D).nonDegenerate n ↦ outerProductCoefficientMap (η.app (s.1.obj 0)))
    (fun s ↦ realizedOuterProductHomotopyEquiv (Δ[n] : SSet.{u})
      (η.app (s.1.obj 0)) (e (s.1.obj 0)) (he (s.1.obj 0))) (fun _ ↦ rfl)

@[simp]
theorem realizedReplacementCellsHomotopyEquiv_toFun (n : ℕ) :
    (realizedReplacementCellsHomotopyEquiv η e he n).toFun =
      (SSet.toTop.map (diagonalMap (replacementCellsMap η n))).hom := rfl

/-- The same statement holds for the actual realized boundary families. -/
def realizedReplacementCellBoundariesHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv |diagonalSSet (replacementCellBoundaries H n)|
      |diagonalSSet (replacementCellBoundaries K n)| :=
  realizedBisimplicialSigmaHomotopyEquiv
    (fun s : (nerve D).nonDegenerate n ↦ outerProductCoefficientMap (η.app (s.1.obj 0)))
    (fun s ↦ realizedOuterProductHomotopyEquiv (∂Δ[n] : SSet.{u})
      (η.app (s.1.obj 0)) (e (s.1.obj 0)) (he (s.1.obj 0))) (fun _ ↦ rfl)

@[simp]
theorem realizedReplacementCellBoundariesHomotopyEquiv_toFun (n : ℕ) :
    (realizedReplacementCellBoundariesHomotopyEquiv η e he n).toFun =
      (SSet.toTop.map (diagonalMap (replacementCellBoundariesMap η n))).hom := rfl

/-- The zero skeleton is empty, so its coefficient comparison is an isomorphism. -/
instance replacementSkeletonMap_zero_isIso : IsIso ((replacementSkeletonMap η).app 0) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro p
  rw [NatTrans.isIso_iff_isIso_app]
  intro q
  apply (isIso_iff_bijective _).2
  constructor
  · intro x y _
    have hx : False := by simpa using x.1.2
    exact hx.elim
  · intro y
    have hy : False := by simpa using y.1.2
    exact hy.elim

/-- The realized zero-stage comparison is also an isomorphism. -/
instance realizedReplacementSkeletonMap_zero_isIso :
    IsIso ((realizedReplacementSkeletonMap η).app 0) :=
  Functor.map_isIso (diagonalFunctor ⋙ SSet.toTop) ((replacementSkeletonMap η).app 0)

/-- The actual comparison on every finite realized skeleton is a homotopy
equivalence, proved by induction over the genuine enriched pushouts. -/
def realizedReplacementSkeletonHomotopyEquivData (n : ℕ) :
    { E : ContinuousMap.HomotopyEquiv ((realizedReplacementSkeleton H).obj n)
        ((realizedReplacementSkeleton K).obj n) //
      E.toFun = ((realizedReplacementSkeletonMap η).app n).hom } := by
  induction n with
  | zero =>
    exact ⟨(TopCat.homeoOfIso (asIso ((realizedReplacementSkeletonMap η).app 0))).toHomotopyEquiv,
      rfl⟩
  | succ n ih =>
    let R := diagonalFunctor.{u} ⋙ SSet.toTop
    let a := R.map (replacementCellBoundariesMap η n)
    let b := R.map (replacementCellsMap η n)
    let c := (realizedReplacementSkeletonMap η).app n
    let d := (realizedReplacementSkeletonMap η).app (n + 1)
    let E := TopCat.Pushout.pushoutHomotopyEquivOfMap
      (realizedReplacementSkeleton_isPushout H n).flip
      (realizedReplacementSkeleton_isPushout K n).flip
      (homotopyExtensionProperty_replacementCellsBoundary H n)
      (homotopyExtensionProperty_replacementCellsBoundary K n)
      a b c d
      (by
        change R.map (replacementCellsBoundaryι H n) ≫ R.map (replacementCellsMap η n) =
          R.map (replacementCellBoundariesMap η n) ≫ R.map (replacementCellsBoundaryι K n)
        simpa only [Functor.map_comp] using congrArg R.map (replacementCellsMap_boundary η n))
      (by
        change R.map (replacementCellsAttaching H n) ≫ R.map ((replacementSkeletonMap η).app n) =
          R.map (replacementCellBoundariesMap η n) ≫ R.map (replacementCellsAttaching K n)
        simpa only [Functor.map_comp] using congrArg R.map (replacementCellsMap_attaching η n))
      (by
        change R.map (replacementCellsCharacteristic H n) ≫ R.map ((replacementSkeletonMap η).app (n
          + 1)) =
          R.map (replacementCellsMap η n) ≫ R.map (replacementCellsCharacteristic K n)
        simpa only [Functor.map_comp] using congrArg R.map (replacementCellsMap_characteristic η n))
      ((realizedReplacementSkeletonMap η).naturality (homOfLE (Nat.le_succ n)))
      (realizedReplacementCellBoundariesHomotopyEquiv η e he n) rfl
      (realizedReplacementCellsHomotopyEquiv η e he n) rfl
      ih.1 ih.2
    exact ⟨E, rfl⟩

/-- The finite-stage comparison equivalence with its canonical forward map. -/
def realizedReplacementSkeletonHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv ((realizedReplacementSkeleton H).obj n)
      ((realizedReplacementSkeleton K).obj n) :=
  (realizedReplacementSkeletonHomotopyEquivData η e he n).1

@[simp]
theorem realizedReplacementSkeletonHomotopyEquiv_toFun (n : ℕ) :
    (realizedReplacementSkeletonHomotopyEquiv η e he n).toFun =
      ((realizedReplacementSkeletonMap η).app n).hom :=
  (realizedReplacementSkeletonHomotopyEquivData η e he n).2

end CategoryTheory.TheoremA
