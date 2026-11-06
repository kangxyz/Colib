/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.SkeletalCofibrations
public import Colib.CategoryTheory.TheoremA.SkeletalNaturality
public import Colib.Topology.Realization.MonomorphismHEP
public import Colib.Topology.Realization.Skeleton

/-!
# Genuine skeletal attachments for coefficient-product domains

These constructions use the actual simplicial product domains and their
canonical simplicial skeletal attachments. No cartesian comparison is an
input to the pushout or cofibration statements.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/Realization/Cartesian/DomainGeometry.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving actual domains and structural maps. -/
@[expose] public section

open CategoryTheory.TheoremA SSet Topology TopCat


noncomputable section

open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Topology.Realization.CartesianDomains
open TheoremA

attribute [simp] skeletonOfMono_bot

/-- External product with a fixed coefficient simplicial set. -/
def outerProductFunctor (X : SSet.{u}) : SSet.{u} ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{u}) where
  obj K := outerProduct K X
  map f := outerProductMap f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The exact diagonal product domains, functorially in the base simplicial set. -/
abbrev diagonalOuterProductFunctor (X : SSet.{u}) : SSet.{u} ⥤ SSet.{u} :=
  outerProductFunctor X ⋙ diagonalFunctor

/-- The explicit diagonal/product coordinates are natural in the whole base. -/
def diagonalOuterProductFunctorIso (X : SSet.{u}) :
    diagonalOuterProductFunctor X ≅ tensorLeft X :=
  NatIso.ofComponents (fun K ↦ diagonalOuterProductIso K X)
    (fun f ↦ diagonalOuterProductIso_naturality f)

instance diagonalOuterProductFunctor_preservesColimits (X : SSet.{u}) :
    PreservesColimits (diagonalOuterProductFunctor X) :=
  preservesColimits_of_natIso (diagonalOuterProductFunctorIso X).symm

/-- Realization of the actual diagonal coefficient-product domain. -/
abbrev realizedOuterProductFunctor (X : SSet.{u}) : SSet.{u} ⥤ TopCat.{u} :=
  diagonalOuterProductFunctor X ⋙ SSet.toTop

instance realizedOuterProductFunctor_preservesColimits (X : SSet.{u}) :
    PreservesColimits (realizedOuterProductFunctor X) := inferInstance

/-- The realized coefficient-product functor preserves actual pushout squares,
including their specified four structural maps. -/
theorem realizedOuterProduct_isPushout (X : SSet.{u})
    {A B C D : SSet.{u}} {t : A ⟶ B} {l : A ⟶ C} {r : B ⟶ D} {b : C ⟶ D}
    (h : IsPushout t l r b) :
    IsPushout (SSet.toTop.map (diagonalMap (outerProductMap (X := X) t)))
      (SSet.toTop.map (diagonalMap (outerProductMap (X := X) l)))
      (SSet.toTop.map (diagonalMap (outerProductMap (X := X) r)))
      (SSet.toTop.map (diagonalMap (outerProductMap (X := X) b))) :=
  h.map (realizedOuterProductFunctor X)

/-- The realized domain construction is natural in the coefficient as well. -/
def realizedOuterProductCoefficientNatTrans {X Y : SSet.{u}} (f : X ⟶ Y) :
    realizedOuterProductFunctor X ⟶ realizedOuterProductFunctor Y where
  app K := SSet.toTop.map (diagonalMap (outerProductCoefficientMap f))
  naturality K L g := by
    change (diagonalFunctor ⋙ SSet.toTop).map _ ≫
      (diagonalFunctor ⋙ SSet.toTop).map _ =
      (diagonalFunctor ⋙ SSet.toTop).map _ ≫ (diagonalFunctor ⋙ SSet.toTop).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl

/-- The prescribed realized maps of coproduct injections form a true coproduct. -/
def realizedOuterProductSigmaIsColimit (X : SSet.{u}) {ι : Type u}
    (K : ι → SSet.{u}) :
    IsColimit (Cofan.mk ((realizedOuterProductFunctor X).obj (∐ K))
      (fun i ↦ (realizedOuterProductFunctor X).map (Sigma.ι K i))) :=
  isColimitCofanMkObjOfIsColimit (realizedOuterProductFunctor X) K (Sigma.ι K)
    (coproductIsCoproduct K)

/-- The actual realized coproduct of enriched domains is a disjoint union. -/
def realizedOuterProductSigmaIso (X : SSet.{u}) {ι : Type u} (K : ι → SSet.{u}) :
    (realizedOuterProductFunctor X).obj (∐ K) ≅
      TopCat.of (Σ i, (realizedOuterProductFunctor X).obj (K i)) :=
  (realizedOuterProductSigmaIsColimit X K).coconePointUniqueUpToIso
    (TopCat.sigmaCofanIsColimit fun i ↦ (realizedOuterProductFunctor X).obj (K i))

/-- The realized coproduct coordinates preserve each prescribed summand injection. -/
@[reassoc (attr := simp)] theorem realizedOuterProductSigmaIso_map_ι (X : SSet.{u})
    {ι : Type u} (K : ι → SSet.{u}) (i : ι) :
    SSet.toTop.map (SSet.diagonalFunctor.map ((outerProductFunctor X).map (Sigma.ι K i))) ≫
      (realizedOuterProductSigmaIso X K).hom =
        TopCat.sigmaι (fun i ↦ (realizedOuterProductFunctor X).obj (K i)) i :=
          (realizedOuterProductSigmaIsColimit X K).comp_coconePointUniqueUpToIso_hom _ ⟨i⟩

/-- The coproduct coordinates preserve the exact maps of the summands. -/
theorem realizedOuterProductSigmaIso_naturality (X : SSet.{u}) {ι : Type u}
    {K L : ι → SSet.{u}} (f : ∀ i, K i ⟶ L i) :
    (realizedOuterProductFunctor X).map (Limits.Sigma.map f) ≫
      (realizedOuterProductSigmaIso X L).hom =
    (realizedOuterProductSigmaIso X K).hom ≫
      topologicalSigmaMap (fun i ↦ (realizedOuterProductFunctor X).map (f i)) := by
  apply (realizedOuterProductSigmaIsColimit X K).hom_ext
  intro ⟨i⟩
  change (realizedOuterProductFunctor X).map (Sigma.ι K i) ≫
      (realizedOuterProductFunctor X).map (Limits.Sigma.map f) ≫ _ =
    (realizedOuterProductFunctor X).map (Sigma.ι K i) ≫
      (realizedOuterProductSigmaIso X K).hom ≫ _
  rw [← Functor.map_comp_assoc]
  simp only [Sigma.ι_map, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.assoc, realizedOuterProductSigmaIso_map_ι,
    realizedOuterProductSigmaIso_map_ι_assoc, topologicalSigmaMap_ι]

/-- A coproduct of realized coefficient-product HEP maps has HEP on its
actual categorical coproduct domain. -/
theorem homotopyExtensionProperty_realizedOuterProductSigma (X : SSet.{u}) {ι : Type u}
    {K L : ι → SSet.{u}} (f : ∀ i, K i ⟶ L i)
    (hf : ∀ i, TopCat.HomotopyExtensionProperty ((realizedOuterProductFunctor X).map (f i))) :
    TopCat.HomotopyExtensionProperty ((realizedOuterProductFunctor X).map (Limits.Sigma.map f)) :=
  TopCat.homotopyExtensionProperty_of_iso_square _ _
    (realizedOuterProductSigmaIso X K) (realizedOuterProductSigmaIso X L)
    (realizedOuterProductSigmaIso_naturality X f) (homotopyExtensionProperty_sigma _ hf)

/-- Cells of the canonical skeletal filtration of an arbitrary simplicial set. -/
abbrev DomainCell (K : SSet.{u}) (n : ℕ) :=
  SSet.relativeCellComplexOfMono.Cell (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) n

/-- Canonical cells are exactly the nondegenerate simplices. -/
def domainCellEquiv (K : SSet.{u}) (n : ℕ) : DomainCell K n ≃ K.nonDegenerate n where
  toFun c := ⟨c.simplex, c.nonDegenerate⟩
  invFun s := { simplex := s.1, nonDegenerate := s.2, notMem := by simp }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact identification of the relative-cell-complex stage with the ordinary skeleton. -/
def domainSkeletonIso (K : SSet.{u}) (n : ℕ) :
    (SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) n : SSet.{u}) ≅
      (K.skeleton n : SSet.{u}) :=
  SSet.Subcomplex.eqToIso (skeletonOfMono_bot K n)

/-- The coproduct of all standard simplices attached at one domain stage. -/
abbrev domainCells (K : SSet.{u}) (n : ℕ) : SSet.{u} :=
  ∐ fun _ : DomainCell K n ↦ (Δ[n] : SSet.{u})

/-- The coproduct of their actual standard boundaries. -/
abbrev domainCellBoundaries (K : SSet.{u}) (n : ℕ) : SSet.{u} :=
  ∐ fun _ : DomainCell K n ↦ (∂Δ[n] : SSet.{u})

/-- The map from the boundary family to the cell family. -/
abbrev domainCellsBoundaryι (K : SSet.{u}) (n : ℕ) :
    domainCellBoundaries K n ⟶ domainCells K n :=
  Limits.Sigma.map fun _ ↦ ∂Δ[n].ι

/-- Attaching the actual boundary family to the preceding ordinary skeleton. -/
def domainCellsAttaching (K : SSet.{u}) (n : ℕ) :
    domainCellBoundaries K n ⟶ (K.skeleton n : SSet.{u}) :=
  SSet.relativeCellComplexOfMono.t (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) n ≫
    (domainSkeletonIso K n).hom

/-- The actual characteristic map into the successor ordinary skeleton. -/
def domainCellsCharacteristic (K : SSet.{u}) (n : ℕ) :
    domainCells K n ⟶ (K.skeleton (n + 1) : SSet.{u}) :=
  SSet.relativeCellComplexOfMono.b (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) n ≫
    (domainSkeletonIso K (n + 1)).hom

/-- The ordinary skeleton inclusion is the fourth structural map. -/
abbrev domainSkeletonSucc (K : SSet.{u}) (n : ℕ) :
    (K.skeleton n : SSet.{u}) ⟶ (K.skeleton (n + 1) : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (K.skeleton.monotone (Nat.le_succ n))

/-- The canonical ordinary skeletal attachment is a genuine pushout. -/
theorem domainSkeleton_isPushout (K : SSet.{u}) (n : ℕ) :
    IsPushout (domainCellsAttaching K n) (domainCellsBoundaryι K n)
      (domainSkeletonSucc K n) (domainCellsCharacteristic K n) := by
  apply (SSet.relativeCellComplexOfMono.isPushout
    (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) n).of_iso
      (Iso.refl _) (domainSkeletonIso K n) (Iso.refl _) (domainSkeletonIso K (n + 1))
  · simp [domainCellsAttaching]
  · simp [domainCellsBoundaryι]
  · rfl
  · simp [domainCellsCharacteristic]

/-- The coefficient-product skeletal attachment remains a true pushout on realization. -/
theorem realizedOuterProductSkeleton_isPushout (X K : SSet.{u}) (n : ℕ) :
    IsPushout ((realizedOuterProductFunctor X).map (domainCellsAttaching K n))
      ((realizedOuterProductFunctor X).map (domainCellsBoundaryι K n))
      ((realizedOuterProductFunctor X).map (domainSkeletonSucc K n))
      ((realizedOuterProductFunctor X).map (domainCellsCharacteristic K n)) :=
  (domainSkeleton_isPushout K n).map (realizedOuterProductFunctor X)

/-- The realized boundary leg is a genuine cofibration for every coefficient. -/
theorem homotopyExtensionProperty_realizedDomainCellsBoundary (X K : SSet.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty
      ((realizedOuterProductFunctor X).map (domainCellsBoundaryι K n)) :=
  homotopyExtensionProperty_realizedOuterProductSigma X (fun _ : DomainCell K n ↦ ∂Δ[n].ι)
    (fun _ ↦ homotopyExtensionProperty_enrichedBoundary X n)

/-- Every realized coefficient-product successor inclusion has HEP. -/
theorem homotopyExtensionProperty_realizedDomainSkeletonSucc (X K : SSet.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty
      ((realizedOuterProductFunctor X).map (domainSkeletonSucc K n)) :=
  TopCat.homotopyExtensionProperty_pushout (realizedOuterProductSkeleton_isPushout X K n).flip
    (homotopyExtensionProperty_realizedDomainCellsBoundary X K n)

/-- The ordinary skeleton is generated in dimensions strictly below its index. -/
instance domainSkeleton_hasDimensionLT (K : SSet.{u}) (n : ℕ) :
    SSet.HasDimensionLT (K.skeleton n : SSet.{u}) n where
  degenerate_eq_top d hd := by
    ext x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    rw [SSet.Subcomplex.mem_degenerate_iff, SSet.mem_degenerate_iff_notMem_nonDegenerate]
    intro hx
    have hlt := (K.mem_skeleton_obj_iff_of_nonDegenerate ⟨x.1, hx⟩ n).mp x.2
    omega

/-- A finite-dimensional simplicial set is reached by its ordinary skeleton. -/
theorem domainSkeleton_eq_top (K : SSet.{u}) (n : ℕ) [K.HasDimensionLT n] :
    K.skeleton n = ⊤ := by
  rw [SSet.Subcomplex.eq_top_iff_of_hasDimensionLT _ n]
  intro d hd x _
  exact K.mem_skeleton x hd

/-- The terminal finite stage is canonically the original simplicial set. -/
def domainSkeletonTopIso (K : SSet.{u}) (n : ℕ) [K.HasDimensionLT n] :
    (K.skeleton n : SSet.{u}) ≅ K :=
  SSet.Subcomplex.eqToIso (domainSkeleton_eq_top K n) ≪≫ SSet.Subcomplex.topIso K

@[simp] theorem domainSkeletonTopIso_hom (K : SSet.{u}) (n : ℕ) [K.HasDimensionLT n] :
    (domainSkeletonTopIso K n).hom = (K.skeleton n).ι := rfl

instance domainSkeletonι_isIso (K : SSet.{u}) (n : ℕ) [K.HasDimensionLT n] :
    IsIso (K.skeleton n).ι := by
  rw [← domainSkeletonTopIso_hom K n]
  infer_instance

/-- The realized zero skeleton is genuinely empty. -/
instance realizationDomainSkeletonZero_isEmpty (K : SSet.{u}) :
    IsEmpty |(K.skeleton 0 : SSet.{u})| := ⟨by
  intro x
  obtain ⟨m, f, t, ht⟩ := realization_exists_simplex x
  have hs := (SSet.yonedaEquiv f).2
  simp at hs⟩

/-- The coefficient-product zero stage is genuinely empty for every coefficient. -/
instance realizedOuterProductSkeletonZero_isEmpty (X K : SSet.{u}) :
    IsEmpty ((realizedOuterProductFunctor X).obj (K.skeleton 0 : SSet.{u})) := ⟨by
  intro x
  obtain ⟨m, f, t, ht⟩ := realization_exists_simplex x
  have hs := (SSet.yonedaEquiv f).1.2
  simp at hs⟩

/-- A boundary-family injection follows the actual simplicial boundary inclusion. -/
@[reassoc]
theorem domainCellBoundary_ι (K : SSet.{u}) (n : ℕ) (c : DomainCell K n) :
    Sigma.ι (fun _ : DomainCell K n ↦ (∂Δ[n] : SSet.{u})) c ≫
      domainCellsBoundaryι K n =
    ∂Δ[n].ι ≫ Sigma.ι (fun _ : DomainCell K n ↦ (Δ[n] : SSet.{u})) c := by
  simp [domainCellsBoundaryι]

/-- A characteristic chart followed by the stage inclusion is the specified simplex. -/
@[reassoc (attr := simp)]
theorem domainCellCharacteristic_ι (K : SSet.{u}) (n : ℕ) (c : DomainCell K n) :
    Sigma.ι (fun _ : DomainCell K n ↦ (Δ[n] : SSet.{u})) c ≫
      domainCellsCharacteristic K n ≫ (K.skeleton (n + 1)).ι = c.map := by
  change c.ιSigmaStdSimplex ≫ SSet.relativeCellComplexOfMono.b _ n ≫
    (domainSkeletonIso K (n + 1)).hom ≫ (K.skeleton (n + 1)).ι = c.map
  have hi : (domainSkeletonIso K (n + 1)).hom ≫ (K.skeleton (n + 1)).ι =
      (SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) (n + 1)).ι := rfl
  rw [hi]
  exact c.ι_b_ι

/-- Attaching a boundary chart follows exactly the boundary of its characteristic simplex. -/
@[reassoc (attr := simp)]
theorem domainCellAttaching_ι (K : SSet.{u}) (n : ℕ) (c : DomainCell K n) :
    Sigma.ι (fun _ : DomainCell K n ↦ (∂Δ[n] : SSet.{u})) c ≫
      domainCellsAttaching K n ≫ (K.skeleton n).ι = ∂Δ[n].ι ≫ c.map := by
  change c.ιSigmaBoundary ≫ SSet.relativeCellComplexOfMono.t _ n ≫
    (domainSkeletonIso K n).hom ≫ (K.skeleton n).ι = ∂Δ[n].ι ≫ c.map
  have hi : (domainSkeletonIso K n).hom ≫ (K.skeleton n).ι =
      (SSet.skeletonOfMono (SSet.Subcomplex.ι (⊥ : K.Subcomplex)) n).ι := rfl
  rw [hi]
  simp

/-- The characteristic map of the complete cell family into the full simplicial set. -/
abbrev domainCellsMap (K : SSet.{u}) (n : ℕ) : domainCells K n ⟶ K :=
  Sigma.desc fun c ↦ c.map

@[reassoc]
theorem domainCellsCharacteristic_ι (K : SSet.{u}) (n : ℕ) :
    domainCellsCharacteristic K n ≫ (K.skeleton (n + 1)).ι = domainCellsMap K n := by
  apply Sigma.hom_ext
  intro c
  simp

/-- At the final finite stage the actual simplicial set is the pushout vertex. -/
theorem finiteDomainSkeleton_isPushout (K : SSet.{u}) (n : ℕ)
    [K.HasDimensionLT (n + 1)] :
    IsPushout (domainCellsAttaching K n) (domainCellsBoundaryι K n)
      (K.skeleton n).ι (domainCellsMap K n) := by
  apply (domainSkeleton_isPushout K n).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (domainSkeletonTopIso K (n + 1))
  · simp
  · simp
  · rfl
  · exact domainCellsCharacteristic_ι K n

/-- The finite coefficient-product attachment has the full realized domain
as its actual pushout vertex. -/
theorem realizedFiniteDomainSkeleton_isPushout (X K : SSet.{u}) (n : ℕ)
    [K.HasDimensionLT (n + 1)] :
    IsPushout ((realizedOuterProductFunctor X).map (domainCellsAttaching K n))
      ((realizedOuterProductFunctor X).map (domainCellsBoundaryι K n))
      ((realizedOuterProductFunctor X).map (K.skeleton n).ι)
      ((realizedOuterProductFunctor X).map (domainCellsMap K n)) :=
  (finiteDomainSkeleton_isPushout K n).map (realizedOuterProductFunctor X)

/-- The matching base attachment also has the full realization as its vertex. -/
theorem realizationFiniteDomainSkeleton_isPushout (K : SSet.{u}) (n : ℕ)
    [K.HasDimensionLT (n + 1)] :
    IsPushout (SSet.toTop.map (domainCellsAttaching K n))
      (SSet.toTop.map (domainCellsBoundaryι K n))
      (SSet.toTop.map (K.skeleton n).ι) (SSet.toTop.map (domainCellsMap K n)) :=
  (finiteDomainSkeleton_isPushout K n).map SSet.toTop

/-- A simplicial set of dimension below zero has empty realization. -/
instance realizationDomainDimensionZero_isEmpty (K : SSet.{u}) [K.HasDimensionLT 0] :
    IsEmpty |K| :=
  ⟨fun x ↦ isEmptyElim (SSet.toTop.map (domainSkeletonTopIso K 0).inv x)⟩

/-- Its coefficient-product realization is empty as well. -/
instance realizedOuterProductDimensionZero_isEmpty (X K : SSet.{u}) [K.HasDimensionLT 0] :
    IsEmpty ((realizedOuterProductFunctor X).obj K) :=
  ⟨fun x ↦ isEmptyElim ((realizedOuterProductFunctor X).map (domainSkeletonTopIso K 0).inv x)⟩

/-- Realization of the actual categorical base coproduct is a coproduct. -/
def realizationDomainSigmaIsColimit {ι : Type u} (K : ι → SSet.{u}) :
    IsColimit (Cofan.mk |(∐ K)| (fun i ↦ SSet.toTop.map (Sigma.ι K i))) :=
  isColimitCofanMkObjOfIsColimit SSet.toTop K (Sigma.ι K) (coproductIsCoproduct K)

/-- The actual categorical base coproduct has its disjoint-union coordinates. -/
def realizationDomainSigmaIso {ι : Type u} (K : ι → SSet.{u}) :
    |(∐ K)| ≅ TopCat.of (Σ i, |K i|) :=
  (realizationDomainSigmaIsColimit K).coconePointUniqueUpToIso
    (TopCat.sigmaCofanIsColimit fun i ↦ |K i|)

@[reassoc (attr := simp)]
theorem realizationDomainSigmaIso_ι {ι : Type u} (K : ι → SSet.{u}) (i : ι) :
    SSet.toTop.map (Sigma.ι K i) ≫ (realizationDomainSigmaIso K).hom =
      TopCat.sigmaι (fun i ↦ |K i|) i :=
  (realizationDomainSigmaIsColimit K).comp_coconePointUniqueUpToIso_hom _ ⟨i⟩

/-- Every natural projection to the realized base preserves the prescribed
coproduct coordinates. This applies in particular to the outer projection. -/
theorem realizedOuterProductSigmaIso_natTrans (X : SSet.{u})
    (η : realizedOuterProductFunctor X ⟶ SSet.toTop)
    {ι : Type u} (K : ι → SSet.{u}) :
    η.app (∐ K) ≫ (realizationDomainSigmaIso K).hom =
      (realizedOuterProductSigmaIso X K).hom ≫ topologicalSigmaMap (fun i ↦ η.app (K i)) := by
  apply (realizedOuterProductSigmaIsColimit X K).hom_ext
  intro ⟨i⟩
  change (realizedOuterProductFunctor X).map (Sigma.ι K i) ≫
      η.app (∐ K) ≫ (realizationDomainSigmaIso K).hom =
    (realizedOuterProductFunctor X).map (Sigma.ι K i) ≫
      (realizedOuterProductSigmaIso X K).hom ≫ _
  rw [← Category.assoc, η.naturality, Category.assoc, realizationDomainSigmaIso_ι,
    ← Category.assoc]
  simp only [Functor.comp_obj, Functor.comp_map, realizedOuterProductSigmaIso_map_ι,
    topologicalSigmaMap_ι]

/-- The coefficient natural transformation retains the coproduct coordinates. -/
theorem realizedOuterProductSigmaIso_coefficient {X Y : SSet.{u}} (f : X ⟶ Y)
    {ι : Type u} (K : ι → SSet.{u}) :
    (realizedOuterProductCoefficientNatTrans f).app (∐ K) ≫
        (realizedOuterProductSigmaIso Y K).hom =
      (realizedOuterProductSigmaIso X K).hom ≫
        topologicalSigmaMap (fun i ↦ (realizedOuterProductCoefficientNatTrans f).app (K i)) := by
  apply (realizedOuterProductSigmaIsColimit X K).hom_ext
  intro ⟨i⟩
  change (realizedOuterProductFunctor X).map (Sigma.ι K i) ≫
      (realizedOuterProductCoefficientNatTrans f).app (∐ K) ≫
        (realizedOuterProductSigmaIso Y K).hom =
    (realizedOuterProductFunctor X).map (Sigma.ι K i) ≫
      (realizedOuterProductSigmaIso X K).hom ≫ _
  rw [← Category.assoc, (realizedOuterProductCoefficientNatTrans f).naturality,
    Category.assoc]
  simp only [Functor.comp_obj, Functor.comp_map, realizedOuterProductSigmaIso_map_ι,
    realizedOuterProductSigmaIso_map_ι_assoc, topologicalSigmaMap_ι]

/-- The corresponding actual base boundary leg is a genuine cofibration. -/
theorem homotopyExtensionProperty_realizationDomainCellsBoundary (K : SSet.{u}) (n : ℕ) :
    TopCat.HomotopyExtensionProperty (SSet.toTop.map (domainCellsBoundaryι K n)) :=
  SSet.homotopyExtensionProperty_realization_mono _

end Topology.Realization.CartesianDomains
