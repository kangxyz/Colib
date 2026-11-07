/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.RelativeFunctoriality
public import Colib.Topology.LocalCoefficients.SmallChainExcision

/-!
Adapted from `Quillen/Topology/LocalCoefficients/OpenExcision.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and pullbacks.

 # Open excision for the original relative spatial chain map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X : Type u} [TopologicalSpace X]
  (U V : Set X) (A : System.{u, u} X)

/-- The intersection, regarded as an actual subspace of the first open set. -/
def intersectionInSubspace : Set U := {x | x.val ∈ V}

/-- Flattening nested intersection subspaces is an actual homeomorphism. -/
def intersectionSubspaceHomeomorph : intersectionInSubspace U V ≃ₜ (U ∩ V : Set X) where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The original nested-subspace chain map into intersection-small chains. -/
def intersectionSubspaceChainMap :
    singularChainComplex (pullback (subspaceInclusion (intersectionInSubspace U V))
      (pullback (subspaceInclusion U) A)) ⟶
        smallChainComplex (intersectionCover (singletonCover U) (singletonCover V)) A :=
  subspacePushforwardChainMap (subspaceInclusion U) (intersectionInSubspace U V)
    (U ∩ V) (fun x hx ↦ ⟨x.property, hx⟩) A ≫
    (subspaceSmallChainIso (U ∩ V) A).hom ≫
      (smallChainIsoOfPredicateIff (singletonCover (U ∩ V))
        (intersectionCover (singletonCover U) (singletonCover V)) A (fun _ ↦ by
          simp only [isCoverSmall_singletonCover, isCoverSmall_intersectionCover]
          exact Set.subset_inter_iff)).hom

/-- The nested-subspace comparison is a quasi-isomorphism with its original coefficient map. -/
theorem intersectionSubspaceChainMap_quasiIso :
    QuasiIso (intersectionSubspaceChainMap U V A) := by
  have hq := pushforwardChainMap_quasiIso_of_homotopyEquiv
    (intersectionSubspaceHomeomorph U V).toHomotopyEquiv
    (pullback (subspaceInclusion (U ∩ V)) A)
  have he : (intersectionSubspaceHomeomorph U V).toHomotopyEquiv.toFun =
      subspaceMap (subspaceInclusion U) (intersectionInSubspace U V)
        (U ∩ V) (fun x hx ↦ ⟨x.property, hx⟩) := rfl
  rw [he] at hq
  unfold intersectionSubspaceChainMap subspacePushforwardChainMap
  infer_instance

/-- Both routes into actual first-subspace chains agree. -/
@[reassoc]
theorem intersectionSubspaceChainMap_left :
    intersectionSubspaceChainMap U V A ≫
        intersectionChainLeft (singletonCover U) (singletonCover V) A =
      pushforwardChainMap (subspaceInclusion (intersectionInSubspace U V))
        (pullback (subspaceInclusion U) A) ≫ (subspaceSmallChainIso U A).hom := by
  apply (cancel_mono (smallChainComplexInclusion (singletonCover U) A)).mp
  simp only [Category.assoc, subspaceSmallChainIso_hom_inclusion]
  simp only [intersectionSubspaceChainMap, intersectionChainLeft,
    smallChainIsoOfPredicateIff, Category.assoc]
  rw [smallChainRefinement_inclusion
    (intersectionCover (singletonCover U) (singletonCover V)) (singletonCover U) A
      (fun h ↦ (isCoverSmall_intersectionCover _ _ _).mp h |>.1),
    smallChainRefinement_inclusion (singletonCover (U ∩ V))
      (intersectionCover (singletonCover U) (singletonCover V)) A
      (fun h ↦ ⟨((), ()), (isCoverSmall_singletonCover _ _).mp h⟩),
    subspaceSmallChainIso_hom_inclusion, subspacePushforwardChainMap_inclusion]

/-- The actual relative first-subspace complex maps to the small-chain excision source. -/
def openExcisionSourceMap :
    relativeSingularChainComplex (intersectionInSubspace U V)
      (pullback (subspaceInclusion U) A) ⟶
        cokernel (intersectionChainLeft (singletonCover U) (singletonCover V) A) :=
  cokernel.map _ _ (intersectionSubspaceChainMap U V A) (subspaceSmallChainIso U A).hom
    (intersectionSubspaceChainMap_left U V A).symm

/-- The change from genuine relative subspace chains to small chains is a quasi-isomorphism. -/
theorem openExcisionSourceMap_quasiIso : QuasiIso (openExcisionSourceMap U V A) := by
  let S := ShortComplex.mk
    (pushforwardChainMap (subspaceInclusion (intersectionInSubspace U V))
      (pullback (subspaceInclusion U) A)) (cokernel.π _) (cokernel.condition _)
  let T := ShortComplex.mk
    (intersectionChainLeft (singletonCover U) (singletonCover V) A)
      (cokernel.π _) (cokernel.condition _)
  have : Mono T.f := by
    dsimp [T, intersectionChainLeft]
    exact smallChainRefinement_mono _ _ A
      (fun h ↦ (isCoverSmall_intersectionCover _ _ _).mp h |>.1)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  let φ : S ⟶ T :=
    { τ₁ := intersectionSubspaceChainMap U V A
      τ₂ := (subspaceSmallChainIso U A).hom
      τ₃ := openExcisionSourceMap U V A
      comm₁₂ := intersectionSubspaceChainMap_left U V A
      comm₂₃ := by simp [openExcisionSourceMap, S, T] }
  apply HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hS hT
  · exact intersectionSubspaceChainMap_quasiIso U V A
  · change QuasiIso (subspaceSmallChainIso U A).hom
    infer_instance


/-- The inverse relative small-chain identification preserves the original quotient. -/
@[reassoc]
theorem relativeSingularSmallChainIso_quotient_inv (W : Set X) :
    cokernel.π (smallChainComplexInclusion (singletonCover W) A) ≫
        (relativeSingularSmallChainIso W A).inv =
      cokernel.π (pushforwardChainMap (subspaceInclusion W) A) := by
  apply (cancel_mono (relativeSingularSmallChainIso W A).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  symm
  dsimp [relativeSingularSmallChainIso]
  simp only [cokernel.map, cokernel.π_desc, Category.id_comp]

/-- Factoring the original relative spatial map through genuine small-chain excision. -/
theorem openExcisionSourceMap_factor :
    openExcisionSourceMap U V A ≫ openExcisionChainMap U V A =
      relativePushforwardChainMap (subspaceInclusion U) (intersectionInSubspace U V) V
        (fun _ hx ↦ hx) A := by
  apply (cancel_epi (cokernel.π
    (pushforwardChainMap (subspaceInclusion (intersectionInSubspace U V))
      (pullback (subspaceInclusion U) A)))).mp
  simp only [openExcisionSourceMap, openExcisionChainMap, smallChainExcisionMap,
    cokernel.map, cokernel.π_desc_assoc, Category.assoc,
    relativePushforwardChainMap_quotient]
  rw [relativeSingularSmallChainIso_quotient_inv, ← Category.assoc,
    subspaceSmallChainIso_hom_inclusion]

/-- The original inclusion of pairs (U,U∩V) → (X,V) is a twisted quasi-isomorphism
for an actual two-open-set cover, with no replacement forward map. -/
theorem relativePushforwardChainMap_openExcision
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (relativePushforwardChainMap (subspaceInclusion U)
      (intersectionInSubspace U V) V (fun _ hx ↦ hx) A) := by
  have := openExcisionSourceMap_quasiIso U V A
  have := openExcisionChainMap_quasiIso U V A hU hV hcover
  rw [← openExcisionSourceMap_factor U V A]
  infer_instance

end FundamentalGroupoid.LocalCoefficients
