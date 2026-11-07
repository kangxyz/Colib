/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremA.GeometricNaturality
public import Colib.CategoryTheory.TheoremA.AttachmentHomology
public import Colib.Topology.LocalCoefficients.RelativeSquares
public import Colib.Topology.LocalCoefficients.SimplexRelativeProducts
public import Colib.Topology.LocalCoefficients.SigmaFunctoriality

/-!
Adapted from `Quillen/CategoryTheory/TheoremA/AttachmentNaturality.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Naturality and comparison for actual replacement attachment pairs

The original geometric characteristic maps form a strictly commuting square
with the actual diagram map and its original disjoint-union parameter map.
The relative comparison uses this square and genuine all-dimensional attachment
excision, with its coefficient pullback isomorphism retained explicitly.
-/

@[expose] public section
noncomputable section
open SSet TopCat _root_.stdSimplex
open CategoryTheory Limits FundamentalGroupoid.LocalCoefficients
open scoped Simplicial Topology
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.TheoremA
variable {D : Type u} [SmallCategory D] {H K : D ⥤ SSet.{u}}

/-- The original continuous map between the actual realized skeletal stages. -/
def replacementSkeletonStageMap (η : H ⟶ K) (n : ℕ) :
    C((realizedReplacementSkeleton H).obj n, (realizedReplacementSkeleton K).obj n) :=
  ((realizedReplacementSkeletonMap η).app n).hom

/-- The original successor inclusions commute strictly with the original stage maps. -/
theorem replacementSkeletonStep_square (η : H ⟶ K) (n : ℕ) :
    (replacementSkeletonStageMap η (n + 1)).comp (replacementSkeletonStep H n) =
      (replacementSkeletonStep K n).comp (replacementSkeletonStageMap η n) := by
  apply ContinuousMap.ext
  intro x
  exact ConcreteCategory.congr_hom
    ((realizedReplacementSkeletonMap η).naturality (homOfLE (Nat.le_succ n))) x

/-- The original stage map sends the actual old-skeleton image to the old-skeleton image. -/
theorem replacementSkeletonStageMap_mapsTo_range (η : H ⟶ K) (n : ℕ) :
    Set.MapsTo (replacementSkeletonStageMap η (n + 1))
      (Set.range (replacementSkeletonStep H n)) (Set.range (replacementSkeletonStep K n)) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨replacementSkeletonStageMap η n x,
    (ContinuousMap.congr_fun (replacementSkeletonStep_square η n) x).symm⟩

/-- The actual map of geometric cells preserves the simplex coordinate. -/
def replacementGeometricCellMap (η : H ⟶ K) (n : ℕ) :
    C(replacementCellParameters H n × _root_.stdSimplex ℝ (Fin (n + 1)),
      replacementCellParameters K n × _root_.stdSimplex ℝ (Fin (n + 1))) :=
  (replacementCellParametersMap η n).prodMap (ContinuousMap.id _)

/-- The original geometric cell map preserves the actual boundary subspace. -/
theorem replacementGeometricCellMap_mapsTo_boundary (η : H ⟶ K) (n : ℕ) :
    Set.MapsTo (replacementGeometricCellMap η n)
      (SimplexAttachment.sourceBoundary (replacementCellParameters H n) n)
      (SimplexAttachment.sourceBoundary (replacementCellParameters K n) n) :=
  fun _ hx ↦ hx

/-- The coordinate isomorphisms retain the original realized cell-map square. -/
@[reassoc]
theorem replacementGeometricCellMap_square (η : H ⟶ K) (n : ℕ) :
    SSet.toTop.map (diagonalMap (replacementCellsMap η n)) ≫
        (TopCat.isoOfHomeo (realizedReplacementCellsHomeomorph K n)).hom =
      (TopCat.isoOfHomeo (realizedReplacementCellsHomeomorph H n)).hom ≫
        TopCat.ofHom (replacementGeometricCellMap η n) := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact realizedReplacementCellsHomeomorph_naturality η n x

/-- Original characteristic maps commute with the actual geometric parameter map. -/
theorem replacementGeometricCharacteristic_naturality (η : H ⟶ K) (n : ℕ) :
    (replacementGeometricCharacteristic H n) ≫
        (realizedReplacementSkeletonMap η).app (n + 1) =
      TopCat.ofHom (replacementGeometricCellMap η n) ≫
        replacementGeometricCharacteristic K n := by
  apply (cancel_epi (TopCat.isoOfHomeo (realizedReplacementCellsHomeomorph H n)).hom).mp
  simp only [replacementGeometricCharacteristic, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← replacementGeometricCellMap_square, Category.assoc,
    Iso.hom_inv_id_assoc]
  have h := congrArg (diagonalFunctor ⋙ SSet.toTop).map
    (replacementCellsMap_characteristic η n)
  simp only [Functor.map_comp] at h
  simpa only [Functor.comp_map, diagonalFunctor, realizedReplacementSkeletonMap,
    Functor.whiskerRight_app] using h

/-- The exact original continuous-map square for attachment-pair functoriality. -/
theorem replacementGeometricCharacteristic_square (η : H ⟶ K) (n : ℕ) :
    (replacementSkeletonStageMap η (n + 1)).comp
        (replacementGeometricCharacteristic H n).hom =
      (replacementGeometricCharacteristic K n).hom.comp (replacementGeometricCellMap η n) := by
  exact congrArg TopCat.Hom.hom (replacementGeometricCharacteristic_naturality η n)

/-- Objectwise abelian comparison assembles on the original disjoint-union parameter map. -/
theorem replacementCellParametersMap_abelian_quasiIso (η : H ⟶ K)
    (hη : ∀ (d : D) (A : System.{u, u} |K.obj d|), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (SSet.toTop.map (η.app d)).hom A))
    (n : ℕ) (A : System.{u, u} (replacementCellParameters K n)) (hA : AbelianMonodromy A) :
    QuasiIso (pushforwardChainMap (replacementCellParametersMap η n) A) :=
  sigmaContinuousMap_abelian_quasiIso _ (fun s ↦ hη (s.val.obj 0)) A hA

/-- The actual map of geometric cell-boundary pairs preserves abelian twisted homology. -/
theorem replacementGeometricCellMap_relative_quasiIso (η : H ⟶ K)
    (hη : ∀ (d : D) (A : System.{u, u} |K.obj d|), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (SSet.toTop.map (η.app d)).hom A))
    (n : ℕ)
    (A : System.{u, u} (replacementCellParameters K n × _root_.stdSimplex ℝ (Fin (n + 1))))
    (hA : AbelianMonodromy A) :
    QuasiIso (relativePushforwardChainMap (replacementGeometricCellMap η n)
      (SimplexAttachment.sourceBoundary (replacementCellParameters H n) n)
      (SimplexAttachment.sourceBoundary (replacementCellParameters K n) n)
      (replacementGeometricCellMap_mapsTo_boundary η n) A) :=
  prodMap_id_simplexRelative_quasiIso (replacementCellParametersMap η n)
    (replacementCellParametersMap_abelian_quasiIso η hη n) n A hA

/-- The original stage map on the pairs given by the actual old-skeleton images. -/
def replacementSkeletonRangeRelativeMap (η : H ⟶ K) (n : ℕ)
    (A : System.{u, u} ((realizedReplacementSkeleton K).obj (n + 1))) :=
  relativePushforwardChainMap (replacementSkeletonStageMap η (n + 1))
    (Set.range (replacementSkeletonStep H n)) (Set.range (replacementSkeletonStep K n))
    (replacementSkeletonStageMap_mapsTo_range η n) A

/-- Objectwise abelian twisted comparison induces comparison of the actual successor
relative pairs, by the original characteristic square and genuine attachment excision. -/
theorem replacementSkeletonRangeRelativeMap_quasiIso (η : H ⟶ K)
    (hη : ∀ (d : D) (A : System.{u, u} |K.obj d|), AbelianMonodromy A →
      QuasiIso (pushforwardChainMap (SSet.toTop.map (η.app d)).hom A))
    (n : ℕ) (A : System.{u, u} ((realizedReplacementSkeleton K).obj (n + 1)))
    (hA : AbelianMonodromy A) :
    QuasiIso (replacementSkeletonRangeRelativeMap η n A) := by
  let f := (replacementGeometricCharacteristic H n).hom
  let g := (replacementGeometricCharacteristic K n).hom
  let a := replacementGeometricCellMap η n
  let b := replacementSkeletonStageMap η (n + 1)
  let U := SimplexAttachment.sourceBoundary (replacementCellParameters H n) n
  let V := Set.range (replacementSkeletonStep H n)
  let W := SimplexAttachment.sourceBoundary (replacementCellParameters K n) n
  let S := Set.range (replacementSkeletonStep K n)
  let hf : Set.MapsTo f U V := SimplexAttachment.cell_mapsTo_boundary
    (replacementCellParameters H n) n (replacementGeometric_isPushout H n)
  let hg : Set.MapsTo g W S := SimplexAttachment.cell_mapsTo_boundary
    (replacementCellParameters K n) n (replacementGeometric_isPushout K n)
  let ha : Set.MapsTo a U W := replacementGeometricCellMap_mapsTo_boundary η n
  let hb : Set.MapsTo b V S := replacementSkeletonStageMap_mapsTo_range η n
  let w : b.comp f = g.comp a := replacementGeometricCharacteristic_square η n
  have qf : QuasiIso (relativePushforwardChainMap f U V hf (pullback b A)) :=
    simplexAttachmentCell_relative_quasiIso (replacementCellParameters H n) n
      (replacementGeometric_isPushout H n) (pullback b A)
  have qg : QuasiIso (relativePushforwardChainMap g W S hg A) :=
    simplexAttachmentCell_relative_quasiIso (replacementCellParameters K n) n
      (replacementGeometric_isPushout K n) A
  have qa : QuasiIso (relativePushforwardChainMap a U W ha (pullback g A)) :=
    replacementGeometricCellMap_relative_quasiIso η hη n (pullback g A)
      (pullback_abelianMonodromy g hA)
  have qc : QuasiIso (relativeCoefficientChainMap U (pullbackSquareIso f g a b w A).hom) := by
    infer_instance
  have : QuasiIso (relativePushforwardChainMap f U V hf (pullback b A) ≫
      relativePushforwardChainMap b V S hb A) := by
    rw [← relativePushforwardChainMap_square f g a b w U V W S hf hg ha hb A]
    infer_instance
  exact quasiIso_of_comp_left (relativePushforwardChainMap f U V hf (pullback b A))
    (relativePushforwardChainMap b V S hb A)

end CategoryTheory.TheoremA
