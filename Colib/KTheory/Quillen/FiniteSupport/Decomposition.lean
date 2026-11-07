/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Quillen.FiniteSupport.FilteredStages
public import Colib.KTheory.Quillen.FiniteSupport.FiniteProduct
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Group.TypeTags.Hom

/-!
# The original Quillen K-groups of finite-support families

For the canonical category `CategoryTheory.Pi.FiniteCategoryFamily C`,
`decompositionKEquiv C n` identifies its original Quillen K-group in positive
degree `n + 1` with the direct sum of the original coordinate K-groups. Its
forward coordinates are exactly `finiteCategoryEvaluation.KMap`; its inverse
is the finite sum of the original `singletonExactInclusion.KMap` maps.

The proof uses the actual finite-stage Q-nerve colimit and the finite-product
theorem. No support or inverse equations are assumed. Arbitrary zero objects
outside a stage and the empty stage are covered by the categorical stage
equivalence. The index may lie in `u` while the object and morphism universes
are `max u v`.

The mathematical ingredients are Quillen's preservation of finite products and
filtered colimits, Section 2, equations (8)-(9), pp. 103-104. The finite-support
comparison is a consequence of those properties, specialized here to positive degrees.

Implementation provenance: `Quillen/KTheory/FiniteSupport/Decomposition.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual objects, maps, degrees
and universe parameters are retained.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Pi
open scoped DirectSum ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts Classical.propDecidable

namespace CategoryTheory.Pi.FiniteSupport

variable {I : Type u} (C : I → Type (max u v))
  [∀ i, Category.{max u v} (C i)] [∀ i, Abelian (C i)]

universe x y

private theorem abelianEquivalence_KMap_bijective
    {A B : Type x} [Category.{y} A] [Category.{y} B]
    [Abelian A] [Preadditive B] [HasFiniteBiproducts B] {E : ExactStructure B}
    (f : ExactCategory.ExactFunctor (abelianExactStructure A) E)
    [f.toFunctor.IsEquivalence] (n : ℕ) : Function.Bijective (f.KMap n) := by
  let : f.mapQ.IsEquivalence := f.mapQ_isEquivalence_of_equivalence
    (fun i hi => (abelianExactStructure_inflation_iff A i).2
      (f.toFunctor.mono_of_mono_map (E.mono_of_inflation hi)))
    (fun p hp => (abelianExactStructure_deflation_iff A p).2
      (f.toFunctor.epi_of_epi_map (E.epi_of_deflation hp)))
  exact f.KMap_bijective_of_mapQ_isEquivalence n

/-- Every original K-class is represented in a flat finite stage of the same
ambient family. The nested-stage presentation is removed by its actual exact
equivalence, preserving the original inclusion K-map. -/
theorem stageKMap_jointlySurjective (n : ℕ)
    (a : (finiteCategoryExactStructure C).K n) :
    ∃ s : Finset I, ∃ b : (stageExactStructure C s).K n,
      (stageExactToFiniteFamily C s).KMap n b = a := by
  obtain ⟨s, b, hb⟩ := KMap_jointlySurjective C n a
  let f := stageNestedExactFunctor C (stageSet s)
  have : f.toFunctor.IsEquivalence := by
    change (stageNestedEquivalence C (stageSet s)).functor.IsEquivalence
    infer_instance
  obtain ⟨c, hc⟩ := (abelianEquivalence_KMap_bijective f n).2 b
  refine ⟨stageSet s, c, ?_⟩
  have he : f.comp (stageLeg C s) = stageExactToFiniteFamily C (stageSet s) := rfl
  calc
    (stageExactToFiniteFamily C (stageSet s)).KMap n c =
        (f.comp (stageLeg C s)).KMap n c := congrArg (fun f => f.KMap n c) he.symm
    _ = (stageLeg C s).KMap n (f.KMap n c) :=
      DFunLike.congr_fun (ExactFunctor.KMap_comp f (stageLeg C s) n) c
    _ = (stageLeg C s).KMap n b := congrArg ((stageLeg C s).KMap n) hc
    _ = a := hb

/-- A stage inclusion followed by evaluation is the original stage evaluation
on K-groups, including the library's canonical zero normalization. -/
theorem evaluationKMap_stage (s : Finset I) (n : ℕ)
    (a : (stageExactStructure C s).K n) (i : I) :
    (finiteCategoryEvaluation C i).KMap n ((stageExactToFiniteFamily C s).KMap n a) =
      (stageEvaluation C s i).KMap n a := by
  have he : (stageExactToFiniteFamily C s).comp (finiteCategoryEvaluation C i) =
      stageEvaluation C s i := rfl
  exact (DFunLike.congr_fun
    (ExactFunctor.KMap_comp (stageExactToFiniteFamily C s)
      (finiteCategoryEvaluation C i) n) a).symm.trans (congrArg (fun f => f.KMap n a) he)

/-- Evaluation outside a stage is naturally the actual zero exact functor, so
its original K-map is trivial. Arbitrary off-support zero objects are allowed. -/
theorem stageEvaluationKMap_eq_one_of_notMem (s : Finset I) (i : I) (hi : i ∉ s)
    (n : ℕ) : (stageEvaluation C s i).KMap n = 1 := by
  let e : (stageEvaluation C s i).toFunctor ≅
      (ExactFunctor.zero (stageExactStructure C s) (abelianExactStructure (C i))).toFunctor :=
    NatIso.ofComponents (fun M => (M.property i hi).iso (isZero_zero (C i)))
      (fun {_ _} _ => (isZero_zero (C i)).eq_of_tgt _ _)
  exact (ExactFunctor.KMap_eq_of_natIso e n).trans (ExactFunctor.KMap_zero _ _ n)

/-- The original evaluations on the coordinates of a finite stage jointly
detect equality, by the genuine restriction equivalence and finite-product K-theory. -/
theorem stageK_ext (s : Finset I) (n : ℕ)
    {a b : (stageExactStructure C s).K n}
    (h : ∀ i : s, (stageEvaluation C s i.1).KMap n a =
      (stageEvaluation C s i.1).KMap n b) : a = b := by
  let f := stageExactRestriction C s
  have : f.toFunctor.IsEquivalence := by
    change (stageProductEquivalence C s).functor.IsEquivalence
    infer_instance
  apply (abelianEquivalence_KMap_bijective f n).1
  apply (productKEquiv (fun i : s => C i.1) n).injective
  apply funext
  intro i
  have hm (c : (stageExactStructure C s).K n) :
      (exactEvaluation (fun i : s => C i.1) i).KMap n (f.KMap n c) =
        (stageEvaluation C s i.1).KMap n c := by
    have he : f.comp (exactEvaluation (fun i : s => C i.1) i) =
        stageEvaluation C s i.1 := rfl
    exact (DFunLike.congr_fun
      (ExactFunctor.KMap_comp f (exactEvaluation (fun i : s => C i.1) i) n) c).symm.trans
        (congrArg (fun f => f.KMap n c) he)
  exact (hm a).trans ((h i).trans (hm b).symm)

/-- An original finite-support K-class has evaluation coordinates equal to one
outside a single finite set. -/
theorem evaluationKMap_support_bound (n : ℕ)
    (a : (finiteCategoryExactStructure C).K n) :
    ∃ s : Finset I, ∀ i, i ∉ s → (finiteCategoryEvaluation C i).KMap n a = 1 := by
  obtain ⟨s, b, rfl⟩ := stageKMap_jointlySurjective C n a
  refine ⟨s, fun i hi => ?_⟩
  rw [evaluationKMap_stage, stageEvaluationKMap_eq_one_of_notMem C s i hi,
    MonoidHom.one_apply]

/-- The original evaluation coordinates have finite nontrivial support. -/
theorem evaluationKMap_support_finite (n : ℕ)
    (a : (finiteCategoryExactStructure C).K n) :
    {i | (finiteCategoryEvaluation C i).KMap n a ≠ 1}.Finite := by
  obtain ⟨s, hs⟩ := evaluationKMap_support_bound C n a
  apply s.finite_toSet.subset
  intro i hi
  by_contra his
  exact hi (hs i his)

/-- The original evaluation K-maps jointly detect equality on the canonical
finite-support category in every nonnegative degree. -/
theorem evaluationK_ext (n : ℕ)
    {a b : (finiteCategoryExactStructure C).K n}
    (h : ∀ i, (finiteCategoryEvaluation C i).KMap n a =
      (finiteCategoryEvaluation C i).KMap n b) : a = b := by
  have hk (c : (finiteCategoryExactStructure C).K n)
      (hc : ∀ i, (finiteCategoryEvaluation C i).KMap n c = 1) : c = 1 := by
    obtain ⟨s, d, rfl⟩ := stageKMap_jointlySurjective C n c
    have hd : d = 1 := stageK_ext C s n (fun i => by
      calc
        (stageEvaluation C s i.1).KMap n d =
            (finiteCategoryEvaluation C i.1).KMap n
              ((stageExactToFiniteFamily C s).KMap n d) :=
          (evaluationKMap_stage C s n d i.1).symm
        _ = 1 := hc i.1
        _ = (stageEvaluation C s i.1).KMap n 1 := (map_one _).symm)
    rw [hd, map_one]
  apply mul_inv_eq_one.mp
  apply hk
  intro i
  rw [map_mul, map_inv, h i, mul_inv_cancel]

/-- Evaluation after the original singleton insertion is the identity K-map
at its selected coordinate. -/
theorem singletonKMap_evaluation (n : ℕ) (i : I)
    (a : (abelianExactStructure (C i)).K n) :
    (finiteCategoryEvaluation C i).KMap n ((singletonExactInclusion C i).KMap n a) = a := by
  have he : ((singletonExactInclusion C i).comp (finiteCategoryEvaluation C i)).toFunctor ≅
      (ExactFunctor.id (abelianExactStructure (C i))).toFunctor :=
    eqToIso (singletonInclusion_comp_evaluation C i)
  have h := ExactFunctor.KMap_eq_of_natIso he n
  rw [ExactFunctor.KMap_comp, ExactFunctor.KMap_id] at h
  exact DFunLike.congr_fun h a

/-- Evaluation after an original singleton insertion is trivial at every
other coordinate, by its canonical zero-object natural isomorphism. -/
theorem singletonKMap_evaluation_of_ne (n : ℕ) (i j : I) (hji : j ≠ i)
    (a : (abelianExactStructure (C i)).K n) :
    (finiteCategoryEvaluation C j).KMap n ((singletonExactInclusion C i).KMap n a) = 1 := by
  have he : ((singletonExactInclusion C i).comp (finiteCategoryEvaluation C j)).toFunctor ≅
      (ExactFunctor.zero (abelianExactStructure (C i))
        (abelianExactStructure (C j))).toFunctor :=
    eqToIso (singletonInclusion_comp_evaluation_zero C i j hji)
  have h := ExactFunctor.KMap_eq_of_natIso he n
  rw [ExactFunctor.KMap_comp, ExactFunctor.KMap_zero] at h
  exact DFunLike.congr_fun h a

/-- The canonical forward additive homomorphism consists of the original
evaluation K-maps. Finite-stage representability supplies its finite support. -/
def decompositionKMap (n : ℕ) : Additive ((finiteCategoryExactStructure C).K (n + 1)) →+
    ⨁ i, Additive ((abelianExactStructure (C i)).K (n + 1)) where
  toFun a :=
    let s := Classical.choose (evaluationKMap_support_bound C (n + 1) a.toMul)
    let hs := Classical.choose_spec (evaluationKMap_support_bound C (n + 1) a.toMul)
    DFinsupp.mk' (fun i => Additive.ofMul ((finiteCategoryEvaluation C i).KMap (n + 1) a.toMul))
      (Trunc.mk ⟨s.val, fun i => by
        by_cases hi : i ∈ s
        · exact Or.inl hi
        · exact Or.inr (congrArg Additive.ofMul (hs i hi))⟩)
  map_zero' := by
    apply DirectSum.ext
    intro i
    exact congrArg Additive.ofMul ((finiteCategoryEvaluation C i).KMap (n + 1)).map_one
  map_add' a b := by
    apply DirectSum.ext
    intro i
    exact congrArg Additive.ofMul
      (((finiteCategoryEvaluation C i).KMap (n + 1)).map_mul a.toMul b.toMul)

/-- The forward coordinate is exactly the original normalized evaluation K-map. -/
@[simp] theorem decompositionKMap_apply (n : ℕ)
    (a : Additive ((finiteCategoryExactStructure C).K (n + 1))) (i : I) :
    decompositionKMap C n a i =
      Additive.ofMul ((finiteCategoryEvaluation C i).KMap (n + 1) a.toMul) := rfl

/-- The original singleton K-maps induce the inverse direct-sum homomorphism. -/
def sumInclusionsKMap (n : ℕ) :
    (⨁ i, Additive ((abelianExactStructure (C i)).K (n + 1))) →+
      Additive ((finiteCategoryExactStructure C).K (n + 1)) :=
  DirectSum.toAddMonoid (fun i => ((singletonExactInclusion C i).KMap (n + 1)).toAdditive)

/-- The canonical evaluation map sends an original coordinate insertion to
the canonical direct-sum insertion. -/
@[simp] theorem decompositionKMap_singleton (n : ℕ) (i : I)
    (a : (abelianExactStructure (C i)).K (n + 1)) :
    decompositionKMap C n (Additive.ofMul ((singletonExactInclusion C i).KMap (n + 1) a)) =
      DirectSum.of (fun i => Additive ((abelianExactStructure (C i)).K (n + 1))) i
        (Additive.ofMul a) := by
  apply DirectSum.ext
  intro j
  by_cases hji : j = i
  · subst j
    rw [decompositionKMap_apply, toMul_ofMul, singletonKMap_evaluation,
      DirectSum.of_eq_same]
  · rw [decompositionKMap_apply, toMul_ofMul,
      singletonKMap_evaluation_of_ne C (n + 1) i j hji, ofMul_one,
      DirectSum.of_eq_of_ne i j _ hji]

/-- Evaluating the finite sum of the original inclusion K-maps recovers the
given direct-sum element. -/
@[simp] theorem decompositionKMap_sumInclusionsKMap (n : ℕ)
    (a : ⨁ i, Additive ((abelianExactStructure (C i)).K (n + 1))) :
    decompositionKMap C n (sumInclusionsKMap C n a) = a := by
  have h : (decompositionKMap C n).comp (sumInclusionsKMap C n) = AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro i a
    change decompositionKMap C n (sumInclusionsKMap C n (DirectSum.of _ i a)) = _
    rw [sumInclusionsKMap, DirectSum.toAddMonoid_of]
    exact decompositionKMap_singleton C n i a.toMul
  exact DFunLike.congr_fun h a

/-- Evaluation is injective because the finite-product theorem detects a
class in any finite stage representing its difference. -/
theorem decompositionKMap_injective (n : ℕ) : Function.Injective (decompositionKMap C n) := by
  intro a b h
  apply Additive.toMul.injective
  apply evaluationK_ext C (n + 1)
  intro i
  exact congrArg (fun a => (a i).toMul) h

/-- The finite sum of original inclusions recovers the original class. -/
@[simp] theorem sumInclusionsKMap_decompositionKMap (n : ℕ)
    (a : Additive ((finiteCategoryExactStructure C).K (n + 1))) :
    sumInclusionsKMap C n (decompositionKMap C n a) = a := by
  apply decompositionKMap_injective C n
  exact decompositionKMap_sumInclusionsKMap C n (decompositionKMap C n a)

/-- Positive-degree finite-support Quillen K-theory is the direct sum of the
original coordinate groups, on the original evaluation and inclusion K-maps. -/
def decompositionKEquiv (n : ℕ) : Additive ((finiteCategoryExactStructure C).K (n + 1)) ≃+
    ⨁ i, Additive ((abelianExactStructure (C i)).K (n + 1)) where
  toFun := decompositionKMap C n
  invFun := sumInclusionsKMap C n
  left_inv := sumInclusionsKMap_decompositionKMap C n
  right_inv := decompositionKMap_sumInclusionsKMap C n
  map_add' := (decompositionKMap C n).map_add

@[simp] theorem decompositionKEquiv_toAddMonoidHom (n : ℕ) :
    (↑(decompositionKEquiv C n) : Additive ((finiteCategoryExactStructure C).K (n + 1)) →+
      ⨁ i, Additive ((abelianExactStructure (C i)).K (n + 1))) = decompositionKMap C n := rfl

/-- The equivalence's coordinate equation uses the exact original evaluation. -/
@[simp] theorem decompositionKEquiv_apply (n : ℕ)
    (a : Additive ((finiteCategoryExactStructure C).K (n + 1))) (i : I) :
    decompositionKEquiv C n a i =
      Additive.ofMul ((finiteCategoryEvaluation C i).KMap (n + 1) a.toMul) := rfl

/-- The equivalence sends each original coordinate inclusion to the canonical
direct-sum inclusion. -/
@[simp] theorem decompositionKEquiv_singleton (n : ℕ) (i : I)
    (a : (abelianExactStructure (C i)).K (n + 1)) :
    decompositionKEquiv C n (Additive.ofMul ((singletonExactInclusion C i).KMap (n + 1) a)) =
      DirectSum.of (fun i => Additive ((abelianExactStructure (C i)).K (n + 1))) i
        (Additive.ofMul a) :=
  decompositionKMap_singleton C n i a

@[simp] theorem decompositionKEquiv_symm_toAddMonoidHom (n : ℕ) :
    (↑(decompositionKEquiv C n).symm :
      (⨁ i, Additive ((abelianExactStructure (C i)).K (n + 1))) →+
        Additive ((finiteCategoryExactStructure C).K (n + 1))) = sumInclusionsKMap C n := rfl

/-- The inverse is exactly the finite sum of the original coordinate-inclusion
K-maps over the support of the given direct-sum element. -/
theorem decompositionKEquiv_symm_apply (n : ℕ)
    (a : ⨁ i, Additive ((abelianExactStructure (C i)).K (n + 1))) :
    (decompositionKEquiv C n).symm a =
      ∑ i ∈ a.support,
        Additive.ofMul ((singletonExactInclusion C i).KMap (n + 1) (a i).toMul) := by
  change sumInclusionsKMap C n a = _
  calc
    sumInclusionsKMap C n a = sumInclusionsKMap C n
        (∑ i ∈ a.support,
          DirectSum.of (fun i => Additive ((abelianExactStructure (C i)).K (n + 1))) i (a i)) :=
      congrArg (sumInclusionsKMap C n) (DirectSum.sum_support_of a).symm
    _ = _ := by
      change (DirectSum.toAddMonoid
        (fun i => ((singletonExactInclusion C i).KMap (n + 1)).toAdditive))
          (∑ i ∈ a.support,
            DirectSum.of (fun i => Additive ((abelianExactStructure (C i)).K (n + 1))) i
              (a i)) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      exact DirectSum.toAddMonoid_of
        (fun i => ((singletonExactInclusion C i).KMap (n + 1)).toAdditive) i (a i)

/-- The inverse on a singleton is the original coordinate-inclusion K-map. -/
@[simp] theorem decompositionKEquiv_symm_of (n : ℕ) (i : I)
    (a : Additive ((abelianExactStructure (C i)).K (n + 1))) :
    (decompositionKEquiv C n).symm (DirectSum.of _ i a) =
      Additive.ofMul ((singletonExactInclusion C i).KMap (n + 1) a.toMul) := by
  change sumInclusionsKMap C n (DirectSum.of _ i a) = _
  exact DirectSum.toAddMonoid_of
    (fun i => ((singletonExactInclusion C i).KMap (n + 1)).toAdditive) i a

/-- The required degree-one specialization of the original-map decomposition. -/
abbrev K1DecompositionEquiv : Additive ((finiteCategoryExactStructure C).K 1) ≃+
    ⨁ i, Additive ((abelianExactStructure (C i)).K 1) := decompositionKEquiv C 0

/-- The required degree-two specialization of the original-map decomposition. -/
abbrev K2DecompositionEquiv : Additive ((finiteCategoryExactStructure C).K 2) ≃+
    ⨁ i, Additive ((abelianExactStructure (C i)).K 2) := decompositionKEquiv C 1

end CategoryTheory.Pi.FiniteSupport

attribute [colib_tag "COL-0281",
  colib_ref "quillen" "Quillen/KTheory/FiniteSupport/Decomposition.lean" "adaptation"
    "Positive direct-sum equivalence with original evaluation and singleton inclusion KMaps"]
  CategoryTheory.Pi.FiniteSupport.decompositionKEquiv
  CategoryTheory.Pi.FiniteSupport.decompositionKEquiv_apply
  CategoryTheory.Pi.FiniteSupport.decompositionKEquiv_singleton
  CategoryTheory.Pi.FiniteSupport.decompositionKEquiv_symm_apply
  CategoryTheory.Pi.FiniteSupport.decompositionKEquiv_symm_of
  CategoryTheory.Pi.FiniteSupport.K1DecompositionEquiv
  CategoryTheory.Pi.FiniteSupport.K2DecompositionEquiv

attribute [colib_ref "Quillen1973" "Section 2, equations (8)-(9), pp. 103-104"
  "ingredient"
  "Finite-support decomposition is a consequence of finite-product preservation \
  and filtered-colimit continuity; this endpoint retains the original coordinate \
  and singleton maps for abelian families in positive degrees"]
  CategoryTheory.Pi.FiniteSupport.decompositionKEquiv
  CategoryTheory.Pi.FiniteSupport.decompositionKEquiv_apply
  CategoryTheory.Pi.FiniteSupport.decompositionKEquiv_singleton
  CategoryTheory.Pi.FiniteSupport.decompositionKEquiv_symm_apply
  CategoryTheory.Pi.FiniteSupport.decompositionKEquiv_symm_of
  CategoryTheory.Pi.FiniteSupport.K1DecompositionEquiv
  CategoryTheory.Pi.FiniteSupport.K2DecompositionEquiv
