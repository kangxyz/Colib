/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.AcyclicTruncation

/-!
# The actual functorial acyclic truncation sequence

The existing canonical truncation maps and induced cokernel maps assemble
into a genuine functor to short complexes. The objectwise membership and
conflation results restrict it to bounded acyclic complexes with terms in
a kernel-closed exact subcategory. Exactness of this functor is a separate
statement and is not assumed here.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationFunctor`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u

namespace CochainComplex

attribute [local instance] Abelian.hasFiniteBiproducts

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A chain map acts on the genuine truncation sequence by the existing
truncation map, itself, and the actual induced map of cokernels. -/
def truncationSequenceMap {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    K.shortComplexTruncLE n ⟶ L.shortComplexTruncLE n where
  τ₁ := CochainComplex.truncLEMap f n
  τ₂ := f
  τ₃ := cokernel.map (K.ιTruncLE n) (L.ιTruncLE n)
    (CochainComplex.truncLEMap f n) f (CochainComplex.ιTruncLE_naturality f n).symm
  comm₁₂ := CochainComplex.ιTruncLE_naturality f n
  comm₂₃ := (cokernel.π_desc _ _ _).symm

@[simp]
theorem truncationSequenceMap_id (K : CochainComplex A ℤ) (n : ℤ) :
    truncationSequenceMap (𝟙 K) n = 𝟙 (K.shortComplexTruncLE n) := by
  apply ShortComplex.hom_ext
  · exact HomologicalComplex.truncLEMap_id K (ComplexShape.embeddingUpIntLE n)
  · rfl
  · exact cokernel.map_id (K.ιTruncLE n) (CochainComplex.truncLEMap (𝟙 K) n)
      (CochainComplex.ιTruncLE_naturality (𝟙 K) n).symm

@[simp]
theorem truncationSequenceMap_comp {K L M : CochainComplex A ℤ}
    (f : K ⟶ L) (g : L ⟶ M) (n : ℤ) :
    truncationSequenceMap (f ≫ g) n = truncationSequenceMap f n ≫ truncationSequenceMap g n := by
  apply ShortComplex.hom_ext
  · exact HomologicalComplex.truncLEMap_comp f g (ComplexShape.embeddingUpIntLE n)
  · rfl
  · apply (cancel_epi (cokernel.π (K.ιTruncLE n))).1
    simp only [truncationSequenceMap, ShortComplex.comp_τ₃, cokernel.map,
      cokernel.π_desc_assoc, cokernel.π_desc, Category.assoc]

/-- The genuine ambient truncation-to-short-complex functor. -/
def truncationSequenceFunctor (n : ℤ) :
    CochainComplex A ℤ ⥤ ShortComplex (CochainComplex A ℤ) where
  obj K := K.shortComplexTruncLE n
  map f := truncationSequenceMap f n
  map_id K := truncationSequenceMap_id K n
  map_comp f g := truncationSequenceMap_comp f g n

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- Functoriality lifts to the actual full subcategory without changing
any of the three ambient maps. -/
def acyclicTruncationSequenceMap
    {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) (n : ℤ) :
    acyclicTruncationSequence K.obj n P K.property ⟶
      acyclicTruncationSequence L.obj n P L.property where
  τ₁ := (boundedAcyclic P).homMk (truncationSequenceMap f.hom n).τ₁
  τ₂ := f
  τ₃ := (boundedAcyclic P).homMk (truncationSequenceMap f.hom n).τ₃
  comm₁₂ := ObjectProperty.hom_ext _ (truncationSequenceMap f.hom n).comm₁₂
  comm₂₃ := ObjectProperty.hom_ext _ (truncationSequenceMap f.hom n).comm₂₃

/-- The actual bounded-acyclic truncation functor into short complexes of
the same full subcategory. No exactness hypothesis is supplied. -/
def acyclicTruncationSequenceFunctor (n : ℤ) :
    (boundedAcyclic P).FullSubcategory ⥤ ShortComplex (boundedAcyclic P).FullSubcategory where
  obj K := acyclicTruncationSequence K.obj n P K.property
  map f := acyclicTruncationSequenceMap P f n
  map_id K := by
    apply ShortComplex.hom_ext
    · apply ObjectProperty.hom_ext
      exact congrArg (fun f ↦ f.τ₁) (truncationSequenceMap_id K.obj n)
    · rfl
    · apply ObjectProperty.hom_ext
      exact congrArg (fun f ↦ f.τ₃) (truncationSequenceMap_id K.obj n)
  map_comp f g := by
    apply ShortComplex.hom_ext
    · apply ObjectProperty.hom_ext
      exact congrArg (fun h ↦ h.τ₁) (truncationSequenceMap_comp f.hom g.hom n)
    · rfl
    · apply ObjectProperty.hom_ext
      exact congrArg (fun h ↦ h.τ₃) (truncationSequenceMap_comp f.hom g.hom n)

@[simp]
theorem acyclicTruncationSequenceFunctor_map_middle (n : ℤ)
    {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    ((acyclicTruncationSequenceFunctor P n).map f).τ₂ = f := rfl

variable [(abelianExactStructure A).IsExtensionClosed P]

/-- Every value of the actual functor is a proved inherited conflation. -/
theorem acyclicTruncationSequenceFunctor_conflation (n : ℤ)
    (K : (boundedAcyclic P).FullSubcategory) :
    (boundedAcyclicExactStructure P).conflation
      ((acyclicTruncationSequenceFunctor P n).obj K) :=
  acyclicTruncationSequence_conflation K.obj n P K.property

/-- The actual full subcategory of conflations of bounded acyclic complexes. -/
def boundedAcyclicConflations :
    ObjectProperty (ShortComplex (boundedAcyclic P).FullSubcategory) :=
  (boundedAcyclicExactStructure P).conflation

/-- The truncation functor lands in the category of actual conflations. -/
def acyclicTruncationConflationFunctor (n : ℤ) :
    (boundedAcyclic P).FullSubcategory ⥤ (boundedAcyclicConflations P).FullSubcategory :=
  (boundedAcyclicConflations P).lift (acyclicTruncationSequenceFunctor P n)
    (acyclicTruncationSequenceFunctor_conflation P n)

/-- Forgetting only the conflation proof recovers the same short-complex functor. -/
@[simp]
theorem acyclicTruncationConflationFunctor_comp_inclusion (n : ℤ) :
    acyclicTruncationConflationFunctor P n ⋙ (boundedAcyclicConflations P).ι =
      acyclicTruncationSequenceFunctor P n := rfl

end CochainComplex
