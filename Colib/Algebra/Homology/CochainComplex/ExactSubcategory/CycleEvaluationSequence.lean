/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.CyclesExact
public import Colib.Algebra.Homology.CochainComplex.Cycles

/-!
# Actual cycle-to-term short exact sequences and functors

Cycle inclusion and the original map to the next cycle give the inherited
short exact sequence, naturally in bounded acyclic complexes. Evaluation and
cycle exactness retain the original object-property hypotheses and maps.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.CycleEvaluationSequence`
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
variable (P : ObjectProperty A)

/-- Evaluation at an actual term, as a functor into the original term subcategory. -/
def boundedAcyclicEvaluationFunctor (n : ℤ) :
    (boundedAcyclic P).FullSubcategory ⥤ P.FullSubcategory :=
  P.lift ((boundedAcyclic P).ι ⋙ eval A (ComplexShape.up ℤ) n)
    (fun K ↦ K.property.2.1 n)

@[simp]
theorem boundedAcyclicEvaluationFunctor_map (n : ℤ)
    {K L : (boundedAcyclic P).FullSubcategory} (f : K ⟶ L) :
    ((boundedAcyclicEvaluationFunctor P n).map f).hom = f.hom.f n := rfl

instance boundedAcyclicEvaluationFunctor_additive (n : ℤ) :
    (boundedAcyclicEvaluationFunctor P n).Additive :=
  inferInstanceAs (Functor.Additive (P.lift _ _))

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

local instance : P.IsClosedUnderFiniteProducts :=
  (abelianExactStructure A).extensionClosed_finiteProducts P

/-- The actual evaluation functor preserves inherited conflations.
Kernel closure is not required for evaluation. -/
def boundedAcyclicEvaluationExactFunctor (n : ℤ) :
    ExactFunctor (boundedAcyclicExactStructure P)
      (ExactSubcategory.exactStructure (abelianExactStructure A) P) where
  toFunctor := boundedAcyclicEvaluationFunctor P n
  map_conflation S hS :=
    (shortExact_iff_degreewise_shortExact (S.map (boundedAcyclic P).ι)).1 hS n

variable [(abelianExactStructure A).IsKernelClosed P]

/-- The original cycle inclusions, natural in every actual chain map. -/
def boundedAcyclicCycleInclusion (n : ℤ) :
    boundedAcyclicCyclesFunctor P n ⟶ boundedAcyclicEvaluationFunctor P n where
  app K := P.homMk (K.obj.iCycles n)
  naturality _ _ f := ObjectProperty.hom_ext _ (cyclesMap_i f.hom n)

/-- The original differential factorizations onto the next cycles. -/
def boundedAcyclicCycleProjection (n : ℤ) :
    boundedAcyclicEvaluationFunctor P n ⟶ boundedAcyclicCyclesFunctor P (n + 1) where
  app K := P.homMk (K.obj.toCycles n (n + 1))
  naturality _ _ f := ObjectProperty.hom_ext _ (toCycles_naturality f.hom n (n + 1)).symm

omit [P.ContainsZero] [(abelianExactStructure A).IsExtensionClosed P] in
@[simp]
theorem boundedAcyclicCycleInclusion_hom (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    ((boundedAcyclicCycleInclusion P n).app K).hom = K.obj.iCycles n := rfl

omit [P.ContainsZero] [(abelianExactStructure A).IsExtensionClosed P] in
@[simp]
theorem boundedAcyclicCycleProjection_hom (n : ℤ) (K : (boundedAcyclic P).FullSubcategory) :
    ((boundedAcyclicCycleProjection P n).app K).hom = K.obj.toCycles n (n + 1) := rfl

omit [P.ContainsZero] [(abelianExactStructure A).IsExtensionClosed P] in
@[reassoc]
theorem boundedAcyclicCycle_comp_zero (n : ℤ) :
    boundedAcyclicCycleInclusion P n ≫ boundedAcyclicCycleProjection P n = 0 := by
  apply NatTrans.ext
  funext K
  exact ObjectProperty.hom_ext _ (_root_.CochainComplex.iCycles_toCycles K.obj n)

/-- Every component is the original actual cycle short exact sequence. -/
theorem boundedAcyclicCycleEvaluation_conflation (n : ℤ)
    (K : (boundedAcyclic P).FullSubcategory) :
    (ExactSubcategory.exactStructure (abelianExactStructure A) P).conflation
      (ShortComplex.mk ((boundedAcyclicCycleInclusion P n).app K)
        ((boundedAcyclicCycleProjection P n).app K)
        (NatTrans.congr_app (boundedAcyclicCycle_comp_zero P n) K)) :=
  _root_.CochainComplex.cycleSequence_shortExact K.obj n (K.property.2.2 (n + 1))

end CochainComplex
