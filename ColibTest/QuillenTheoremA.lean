module
public import Colib.KTheory.Quillen.Resolution.LengthOneSpace
public import Colib.CategoryTheory.ExactCategory.Resolution.Strata
@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite SSet CategoryTheory.TheoremA
open scoped Simplicial Topology
example (X : SSet.{u}) : TopCat.HomotopyExtensionProperty
    (SSet.toTop.map (diagonalMap (outerProductMap (X := X) ∂Δ[0].ι))) :=
  homotopyExtensionProperty_enrichedBoundary X 0
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
example (H : D ⥤ SSet.{u}) (n : ℕ) : TopCat.HomotopyExtensionProperty
    ((realizedReplacementSkeleton H).map (homOfLE (Nat.le_succ n))) :=
  homotopyExtensionProperty_realizedReplacementSkeleton_succ H n
example {H K : D ⥤ SSet.{u}} (η : H ⟶ K)
    (e : ∀ d, ContinuousMap.HomotopyEquiv |H.obj d| |K.obj d|)
    (he : ∀ d, (e d).toFun = (SSet.toTop.map (η.app d)).hom) :
    (replacementRealizationHomotopyEquiv η e he).toFun =
      (SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom := rfl
example (H : D ⥤ SSet.{u}) (h : ∀ d, ContractibleSpace |H.obj d|) :
    (contractibleReplacementRealizationHomotopyEquiv H h).toFun =
      (SSet.toTop.map (replacementBaseMap H)).hom :=
  contractibleReplacementRealizationHomotopyEquiv_toFun H h
example (F : C ⥤ D) : (diagonalSourceHomotopyEquiv F).toFun =
    (SSet.toTop.map (diagonalSourceMap F)).hom := diagonalSourceHomotopyEquiv_toFun F
example (F : C ⥤ D)
    (h : ∀ d, ContractibleSpace (ClassifyingSpace (CostructuredArrow F d))) :
    (contractibleCommaClassifyingHomotopyEquiv F h).toFun = (classifyingSpaceMap F).hom := rfl
example (F : C ⥤ D)
    (h : ∀ d, ContractibleSpace (ClassifyingSpace (StructuredArrow d F))) :
    (contractibleStructuredClassifyingHomotopyEquiv F h).toFun = (classifyingSpaceMap F).hom := rfl
open CategoryTheory.ExactCategory
variable [Preadditive C] [HasFiniteBiproducts C] (E : ExactStructure C) (P : ObjectProperty C)
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [E.IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts] [E.IsKernelClosed P]
example (h : ∀ X, E.ResolutionLength P 1 X) :
    ContinuousMap.HomotopyEquiv (ExactSubcategory.exactStructure E P).KSpace E.KSpace :=
  Resolution.classifyingHomotopyEquivOfLengthOne E P h
example (h : ∀ X, E.ResolutionLength P 1 X) :
    (Resolution.classifyingHomotopyEquivOfLengthOne E P h).toFun =
      (classifyingSpaceMap (ExactSubcategory.exactInclusion E P).mapQ).hom :=
  Resolution.classifyingHomotopyEquivOfLengthOne_toFun E P h
