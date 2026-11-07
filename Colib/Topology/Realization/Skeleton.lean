/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.SkeletalAttachment
public import Colib.Topology.Category.TopCat.SequentialColimit.FundamentalGroupoid

/-!
# Actual skeletal attachments and compact path reduction

Extracted from Quillen/Topology/Realization/EdgePathPresentation/Skeleton.lean,
commit c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual cocone maps,
relative skeleta, inclusions and hypotheses are retained. Namespace/import
ownership and the finite-simplex coordinate adapter are the only changes.
-/
@[expose] public noncomputable section
open CategoryTheory Limits Topology Convexity.StdSimplex TopCat
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet

/-- The relative skeleton of the empty inclusion is the ordinary skeleton. -/
theorem skeletonOfMono_bot (X : SSet.{u}) (n : ℕ) :
    SSet.skeletonOfMono ((⊥ : X.Subcomplex).ι) n = X.skeleton n := by
  simp [SSet.skeletonOfMono, SSet.Subcomplex.range]

/-- The actual relative simplicial skeleton tower after realization. -/
def realizedRelativeSkeletonTower {A X : SSet.{u}} (i : A ⟶ X) [Mono i] : ℕ ⥤ TopCat.{u} :=
  (SSet.relativeCellComplexOfMono i).F ⋙ SSet.toTop

/-- The canonical cocone of the actual relative realization tower. -/
def realizedRelativeSkeletonCocone {A X : SSet.{u}} (i : A ⟶ X) [Mono i] :
    Cocone (realizedRelativeSkeletonTower i) :=
  SSet.toTop.mapCocone { pt := X, ι := (SSet.relativeCellComplexOfMono i).incl }

/-- Realization preserves the exhaustive simplicial skeletal colimit. -/
def realizedRelativeSkeletonIsColimit {A X : SSet.{u}} (i : A ⟶ X) [Mono i] :
    IsColimit (realizedRelativeSkeletonCocone i) :=
  isColimitOfPreserves SSet.toTop (SSet.relativeCellComplexOfMono i).isColimit

/-- Successor maps of the actual relative tower are closed embeddings. -/
theorem realizedRelativeSkeleton_closedEmbeddings {A X : SSet.{u}} (i : A ⟶ X)
    [Mono i] (n : ℕ) :
    IsClosedEmbedding ((realizedRelativeSkeletonTower i).map (homOfLE (Nat.le_succ n))) :=
  realizedSkeletal_transition_isClosedEmbedding i n

/-- Every relative stage is T₁ whenever the original subspace is T₁. -/
instance realizedRelativeSkeleton_t1Space {A X : SSet.{u}} (i : A ⟶ X)
    [Mono i] [T1Space |A|] (n : ℕ) : T1Space ((realizedRelativeSkeletonTower i).obj n) := by
  induction n with
  | zero =>
    exact (TopCat.homeoOfIso (SSet.toTop.mapIso (SSet.relativeCellComplexOfMono
      i).isoBot)).symm.t1Space
  | succ n ih =>
    let : T1Space |(SSet.skeletonOfMono i n : SSet.{u})| := ih
    exact t1Space_pushout_of_closedEmbedding (realizedSkeletal_isPushout i n)
      (isClosedEmbedding_parameterizedSimplexBoundary (skeletalCellIndex i n) n)

/-- Realization of the empty subcomplex is empty. -/
instance realization_bot_isEmpty (X : SSet.{u}) :
    IsEmpty |((⊥ : X.Subcomplex) : SSet.{u})| := ⟨by
  intro x
  obtain ⟨m, f, t, ht⟩ := realization_exists_simplex x
  exact (SSet.yonedaEquiv f).2⟩

/-- The skeletal tower starting at the empty subcomplex. Stage `n` contains
exactly the simplices of dimension strictly less than `n`. -/
abbrev realizedSkeletonTower (X : SSet.{u}) : ℕ ⥤ TopCat.{u} :=
  realizedRelativeSkeletonTower ((⊥ : X.Subcomplex).ι)

/-- The ordinary skeletal cocone to the actual realization. -/
abbrev realizedSkeletonCocone (X : SSet.{u}) : Cocone (realizedSkeletonTower X) :=
  realizedRelativeSkeletonCocone ((⊥ : X.Subcomplex).ι)

/-- The actual realization is the colimit of its skeletal tower. -/
abbrev realizedSkeletonIsColimit (X : SSet.{u}) : IsColimit (realizedSkeletonCocone X) :=
  realizedRelativeSkeletonIsColimit ((⊥ : X.Subcomplex).ι)

/-- Identification of each chosen stage with the ordinary simplicial skeleton. -/
def realizedSkeletonStageIso (X : SSet.{u}) (n : ℕ) :
    (realizedSkeletonTower X).obj n ≅ |(X.skeleton n : SSet.{u})| :=
  SSet.toTop.mapIso (SSet.Subcomplex.eqToIso (skeletonOfMono_bot X n))

/-- Every compact subset of the actual realization lies in a finite skeleton. -/
theorem realization_isCompact_subset_stage (X : SSet.{u}) {K : Set |X|} (hK : IsCompact K) :
    ∃ n, K ⊆ Set.range ((realizedSkeletonCocone X).ι.app n) :=
  TopCat.SequentialColimit.isCompact_subset_stageRange_of_closedEmbeddings
    (realizedSkeletonIsColimit X) (realizedRelativeSkeleton_closedEmbeddings _) hK

/-- Every map from a compact space into the actual realization factors through
a finite stage of its actual skeletal tower. -/
theorem realization_continuousMap_factors {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (X : SSet.{u}) (f : C(Y, |X|)) :
    ∃ n, ∃ g : C(Y, (realizedSkeletonTower X).obj n),
      ∀ y, (realizedSkeletonCocone X).ι.app n (g y) = f y :=
  TopCat.SequentialColimit.continuousMap_factors
    (realizedSkeletonIsColimit X) (realizedRelativeSkeleton_closedEmbeddings _) f

@[reassoc (attr := simp)]
theorem realizedSkeletonStageIso_hom_ι (X : SSet.{u}) (n : ℕ) :
    (realizedSkeletonStageIso X n).hom ≫ SSet.toTop.map (X.skeleton n).ι =
      (realizedSkeletonCocone X).ι.app n := by
  change SSet.toTop.map (SSet.Subcomplex.eqToIso (skeletonOfMono_bot X n)).hom ≫
    SSet.toTop.map (X.skeleton n).ι = SSet.toTop.map _
  rw [← SSet.toTop.map_comp]
  congr 1

/-- The actual realization of every simplicial set is T₁. -/
instance realization_t1Space (X : SSet.{u}) : T1Space |X| :=
  TopCat.SequentialColimit.t1Space_colimit (realizedSkeletonIsColimit X)
    (realizedRelativeSkeleton_closedEmbeddings _)

/-- The inclusion of any stage containing all edges is full on fundamental
groupoids in the actual realization. -/
theorem realizedSkeleton_fundamentalGroupoid_full (X : SSet.{u}) (k : ℕ) (hk : 2 ≤ k) :
    (FundamentalGroupoid.map ((realizedSkeletonCocone X).ι.app k).hom).Full :=
  TopCat.SequentialColimit.stage_fundamentalGroupoid_full (realizedSkeletonIsColimit X)
    (realizedRelativeSkeleton_closedEmbeddings _) k
    (fun n hn ↦ realizedSkeletal_transition_fundamentalGroupoid_full _ n (hk.trans hn))

/-- In particular every path between points of the one-dimensional skeleton
is represented up to endpoint-fixed homotopy by a path in that skeleton. -/
theorem realizedSkeleton_path_homotopic_from_stage (X : SSet.{u}) (k : ℕ) (hk : 2 ≤ k)
    {x y : (realizedSkeletonTower X).obj k}
    (p : Path ((realizedSkeletonCocone X).ι.app k x) ((realizedSkeletonCocone X).ι.app k y)) :
    ∃ q : Path x y,
      (q.map ((realizedSkeletonCocone X).ι.app k).hom.continuous).Homotopic p :=
  TopCat.SequentialColimit.path_homotopic_from_stage (realizedSkeletonIsColimit X)
    (realizedRelativeSkeleton_closedEmbeddings _) k
    (fun n hn ↦ realizedSkeletal_transition_fundamentalGroupoid_full _ n (hk.trans hn)) p

/-- The standard one-dimensional skeleton, expressed directly as `X.skeleton 2`,
is full on fundamental groupoids after realization. -/
theorem realization_skeleton_fundamentalGroupoid_full (X : SSet.{u}) (k : ℕ) (hk : 2 ≤ k) :
    (FundamentalGroupoid.map (SSet.toTop.map (X.skeleton k).ι).hom).Full := by
  let e := realizedSkeletonStageIso X k
  have heq : SSet.toTop.map (X.skeleton k).ι =
      e.inv ≫ (realizedSkeletonCocone X).ι.app k := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact realizedSkeletonStageIso_hom_ι X k
  rw [heq]
  change (FundamentalGroupoid.map
    (((realizedSkeletonCocone X).ι.app k).hom.comp e.inv.hom)).Full
  rw [FundamentalGroupoid.map_comp]
  let := realizedSkeleton_fundamentalGroupoid_full X k hk
  have : (FundamentalGroupoid.map e.inv.hom).IsEquivalence :=
    (FundamentalGroupoidFunctor.equivOfHomotopyEquiv
      (TopCat.homeoOfIso e.symm).toHomotopyEquiv).isEquivalence_functor
  infer_instance

/-- Every ordinary skeletal inclusion is a closed embedding in the actual
realization, with its actual subspace topology. -/
theorem realization_skeleton_isClosedEmbedding (X : SSet.{u}) (n : ℕ) :
    IsClosedEmbedding (SSet.toTop.map (X.skeleton n).ι) := by
  let e := realizedSkeletonStageIso X n
  have heq : SSet.toTop.map (X.skeleton n).ι =
      e.inv ≫ (realizedSkeletonCocone X).ι.app n := by
    apply (cancel_epi e.hom).mp
    rw [Iso.hom_inv_id_assoc]
    exact realizedSkeletonStageIso_hom_ι X n
  rw [heq]
  exact (TopCat.SequentialColimit.stage_isClosedEmbedding (realizedSkeletonIsColimit X)
    (realizedRelativeSkeleton_closedEmbeddings _) n).comp
      (TopCat.homeoOfIso e.symm).isClosedEmbedding

/-- Compact containment expressed in terms of the ordinary simplicial skeleton. -/
theorem realization_isCompact_subset_skeleton (X : SSet.{u}) {K : Set |X|} (hK : IsCompact K) :
    ∃ n, K ⊆ Set.range (SSet.toTop.map (X.skeleton n).ι) := by
  obtain ⟨n, hn⟩ := realization_isCompact_subset_stage X hK
  refine ⟨n, ?_⟩
  intro x hx
  obtain ⟨y, rfl⟩ := hn hx
  exact ⟨(realizedSkeletonStageIso X n).hom y,
    ConcreteCategory.congr_hom (realizedSkeletonStageIso_hom_ι X n) y⟩

/-- Compact-source factorization through an ordinary finite skeleton. -/
theorem realization_continuousMap_factors_skeleton
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] (X : SSet.{u}) (f : C(Y, |X|)) :
    ∃ n, ∃ g : C(Y, |(X.skeleton n : SSet.{u})|),
      ∀ y, SSet.toTop.map (X.skeleton n).ι (g y) = f y := by
  obtain ⟨n, g, hg⟩ := realization_continuousMap_factors X f
  refine ⟨n, (realizedSkeletonStageIso X n).hom.hom.comp g, ?_⟩
  intro y
  exact (ConcreteCategory.congr_hom (realizedSkeletonStageIso_hom_ι X n) (g y)).trans (hg y)

/-- Every path with endpoints in the ordinary one-dimensional skeleton is
homotopic relative endpoints to a path in that skeleton. -/
theorem realization_skeleton_path_homotopic (X : SSet.{u}) (k : ℕ) (hk : 2 ≤ k)
    {x y : |(X.skeleton k : SSet.{u})|}
    (p : Path (SSet.toTop.map (X.skeleton k).ι x) (SSet.toTop.map (X.skeleton k).ι y)) :
    ∃ q : Path x y, (q.map (SSet.toTop.map (X.skeleton k).ι).hom.continuous).Homotopic p := by
  let := realization_skeleton_fundamentalGroupoid_full X k hk
  let F := FundamentalGroupoid.map (SSet.toTop.map (X.skeleton k).ι).hom
  obtain ⟨q, hq⟩ := F.map_surjective
    (X := FundamentalGroupoid.mk x) (Y := FundamentalGroupoid.mk y) ⟦p⟧
  obtain ⟨q, rfl⟩ := Path.Homotopic.Quotient.mk_surjective q
  exact ⟨q, Path.Homotopic.Quotient.eq.mp hq⟩

end SSet

attribute [colib_tag "COL-0159",
  colib_ref "HatcherAT" "Section 1.2, Proposition 1.26(a),(b), pages 50-51"
    "background"
    "Absence of new path generators from higher-dimensional attachments; not a faithfulness claim"]
  SSet.realizedSkeletal_isPushout
  SSet.realizedRelativeSkeletonIsColimit
  SSet.realization_continuousMap_factors_skeleton
  SSet.realization_skeleton_fundamentalGroupoid_full
  SSet.realization_skeleton_path_homotopic
