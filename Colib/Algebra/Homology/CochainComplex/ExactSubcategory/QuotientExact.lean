/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationExact
public import Colib.Algebra.Homology.CochainComplex.Cycles

/-!
# Exactness of the actual acyclic truncation quotient

The third projection of the canonical truncation sequence is an exact
functor on bounded acyclic complexes. The existing cokernel-boundary
identification is proved natural, so exactness follows from actual cycles
at the boundary, original terms above it, and zero terms below it.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.QuotientExact`
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

/-- The actual third-projection cokernel functor. -/
def truncationQuotientFunctor (n : ℤ) : CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  truncationSequenceFunctor n ⋙ ShortComplex.π₃

/-- The original quotient map is natural, with its original cokernel map. -/
@[reassoc]
theorem truncationQuotient_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (K.shortComplexTruncLE n).g ≫ (truncationQuotientFunctor n).map f =
      f ≫ (L.shortComplexTruncLE n).g :=
  (truncationSequenceMap f n).comm₂₃.symm

instance truncationQuotientFunctor_additive (n : ℤ) :
    (truncationQuotientFunctor (A := A) n).Additive where
  map_add {K L} f g := by
    apply (cancel_epi (CochainComplex.shortComplexTruncLE K n).g).1
    change (CochainComplex.shortComplexTruncLE K n).g ≫
      (truncationQuotientFunctor n).map (f + g) =
      (CochainComplex.shortComplexTruncLE K n).g ≫
        ((truncationQuotientFunctor n).map f + (truncationQuotientFunctor n).map g)
    simp only [Preadditive.comp_add, truncationQuotient_naturality, Preadditive.add_comp]

/-- The canonical boundary isomorphism respects the actual quotient projection. -/
@[reassoc]
theorem truncationQuotientBoundaryIso_projection (K : CochainComplex A ℤ) (n : ℤ)
    (hK : K.ExactAt (n + 1)) :
    (K.shortComplexTruncLE n).g.f n ≫ (truncationQuotientBoundaryIso K n hK).hom =
      K.toCycles n (n + 1) :=
  (truncationDegree_shortExact K n n).gIsCokernel.comp_coconePointUniqueUpToIso_hom
    (isCokernelEpiComp (_root_.CochainComplex.cycleSequence_shortExact K n hK).gIsCokernel
      (K.truncLEXIsoCycles n).hom (truncLE_inclusion_boundary K n).symm)
    WalkingParallelPair.one

/-- The actual quotient-boundary identification is natural on exact complexes. -/
@[reassoc]
theorem truncationQuotientBoundaryIso_naturality {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (n : ℤ) (hK : K.ExactAt (n + 1)) (hL : L.ExactAt (n + 1)) :
    ((truncationQuotientFunctor n).map f).f n ≫
        (truncationQuotientBoundaryIso L n hL).hom =
      (truncationQuotientBoundaryIso K n hK).hom ≫ cyclesMap f (n + 1) := by
  apply (cancel_epi ((K.shortComplexTruncLE n).g.f n)).1
  have h := congrArg (fun g ↦ g.f n) (truncationQuotient_naturality f n)
  change (K.shortComplexTruncLE n).g.f n ≫
    ((truncationQuotientFunctor n).map f).f n =
      f.f n ≫ (L.shortComplexTruncLE n).g.f n at h
  rw [← Category.assoc, h, Category.assoc, truncationQuotientBoundaryIso_projection,
    ← Category.assoc, truncationQuotientBoundaryIso_projection]
  exact (toCycles_naturality f n (n + 1)).symm

/-- Above the boundary the original quotient projection is an isomorphism. -/
theorem isIso_truncationQuotient_projection_above (K : CochainComplex A ℤ)
    (n i : ℤ) (hi : n < i) : IsIso ((K.shortComplexTruncLE n).g.f i) :=
  (truncationDegree_shortExact K n i).isIso_g_iff.2
    ((K.truncLE n).isZero_of_isStrictlyLE n i hi)

/-- The quotient preserves the actual short exact sequences of acyclic complexes. -/
theorem truncationQuotient_shortExact (S : ShortComplex (CochainComplex A ℤ))
    (hS : S.ShortExact) (h₁ : S.X₁.Acyclic) (h₂ : S.X₂.Acyclic)
    (h₃ : S.X₃.Acyclic) (n : ℤ) :
    (S.map (truncationQuotientFunctor n)).ShortExact := by
  apply (shortExact_iff_degreewise_shortExact _).2
  intro i
  change (S.map (truncationQuotientFunctor n ⋙ eval A (ComplexShape.up ℤ) i)).ShortExact
  rcases lt_trichotomy i n with hi | he | hi
  · exact {
      mono_f := (truncationQuotient_isZero_below S.X₁ n i hi).mono _
      epi_g := (truncationQuotient_isZero_below S.X₃ n i hi).epi _
      exact := ShortComplex.exact_of_isZero_X₂ _
        (truncationQuotient_isZero_below S.X₂ n i hi) }
  · subst i
    let e : S.map (truncationQuotientFunctor n ⋙ eval A (ComplexShape.up ℤ) n) ≅
        S.map (cyclesFunctor A (ComplexShape.up ℤ) (n + 1)) :=
      ShortComplex.isoMk
        (truncationQuotientBoundaryIso S.X₁ n (h₁ (n + 1)))
        (truncationQuotientBoundaryIso S.X₂ n (h₂ (n + 1)))
        (truncationQuotientBoundaryIso S.X₃ n (h₃ (n + 1)))
        (truncationQuotientBoundaryIso_naturality S.f n _ _).symm
        (truncationQuotientBoundaryIso_naturality S.g n _ _).symm
    exact (ShortComplex.shortExact_iff_of_iso e).2 (cycles_shortExact S hS h₃ (n + 1))
  · let e : S.map (eval A (ComplexShape.up ℤ) i) ≅
        S.map (truncationQuotientFunctor n ⋙ eval A (ComplexShape.up ℤ) i) := by
      let := isIso_truncationQuotient_projection_above S.X₁ n i hi
      let := isIso_truncationQuotient_projection_above S.X₂ n i hi
      let := isIso_truncationQuotient_projection_above S.X₃ n i hi
      exact ShortComplex.isoMk
        (asIso ((S.X₁.shortComplexTruncLE n).g.f i))
        (asIso ((S.X₂.shortComplexTruncLE n).g.f i))
        (asIso ((S.X₃.shortComplexTruncLE n).g.f i))
        (congrArg (fun g ↦ g.f i) (truncationQuotient_naturality S.f n))
        (congrArg (fun g ↦ g.f i) (truncationQuotient_naturality S.g n))
    exact ShortComplex.shortExact_of_iso e ((shortExact_iff_degreewise_shortExact S).1 hS i)

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The genuine bounded-acyclic quotient functor is exactly the third
projection of the previously constructed actual truncation sequence. -/
def boundedAcyclicQuotientFunctor (n : ℤ) :
    (boundedAcyclic P).FullSubcategory ⥤ (boundedAcyclic P).FullSubcategory :=
  acyclicTruncationSequenceFunctor P n ⋙ ShortComplex.π₃

instance boundedAcyclicQuotientFunctor_additive (n : ℤ) :
    (boundedAcyclicQuotientFunctor P n).Additive := by
  change Functor.Additive ((boundedAcyclic P).lift
    ((boundedAcyclic P).ι ⋙ truncationQuotientFunctor n)
    (fun K ↦ truncationQuotient_mem K.obj n P K.property))
  infer_instance

/-- At the boundary the quotient functor is naturally the next-cycle functor. -/
def boundedAcyclicQuotientEvalIsoCycles (n : ℤ) :
    boundedAcyclicQuotientFunctor P n ⋙ (boundedAcyclic P).ι ⋙
        eval A (ComplexShape.up ℤ) n ≅
      boundedAcyclicCyclesFunctor P (n + 1) ⋙ P.ι :=
  NatIso.ofComponents (fun K ↦ truncationQuotientBoundaryIso K.obj n (K.property.2.2 (n + 1)))
    (fun f ↦ truncationQuotientBoundaryIso_naturality f.hom n _ _)

variable [(abelianExactStructure A).IsExtensionClosed P]

/-- The actual truncation quotient is exact; no preservation conclusion is assumed. -/
def boundedAcyclicQuotientExactFunctor (n : ℤ) :
    ExactFunctor (boundedAcyclicExactStructure P) (boundedAcyclicExactStructure P) where
  toFunctor := boundedAcyclicQuotientFunctor P n
  map_conflation S hS := truncationQuotient_shortExact (S.map (boundedAcyclic P).ι) hS
    S.X₁.property.2.2 S.X₂.property.2.2 S.X₃.property.2.2 n

end CochainComplex
