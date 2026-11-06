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
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationFunctor

/-!
# Exactness of the genuine acyclic truncation functor

The canonical truncation is exact on the inherited category of bounded
acyclic termwise-P complexes. Degreewise exactness uses the original terms
below the boundary, the actual exact cycle functor at the boundary, and
zero objects above it. The forward maps remain mathlib's actual truncation
maps throughout.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationExact`
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

/-- Below the boundary the actual truncation-evaluation functor is
naturally isomorphic to the original evaluation functor. -/
def truncLEEvalIsoBelow (n i : ℤ) (hi : i < n) :
    (ComplexShape.embeddingUpIntLE n).truncLEFunctor A ⋙ eval A (ComplexShape.up ℤ) i ≅
      eval A (ComplexShape.up ℤ) i :=
  NatIso.ofComponents (fun K ↦ by
    let := isIso_truncLE_inclusion_below K n i hi
    exact asIso ((CochainComplex.ιTruncLE K n).f i)) (by
      intro K L f
      exact congrArg (fun g ↦ g.f i) (CochainComplex.ιTruncLE_naturality f n))

/-- At the boundary the canonical cycle-object identification is natural
for every actual chain map. -/
def truncLEEvalIsoCycles (n : ℤ) :
    (ComplexShape.embeddingUpIntLE n).truncLEFunctor A ⋙ eval A (ComplexShape.up ℤ) n ≅
      cyclesFunctor A (ComplexShape.up ℤ) n :=
  NatIso.ofComponents (fun K ↦ CochainComplex.truncLEXIsoCycles K n) (by
    intro K L f
    apply (cancel_mono (L.iCycles n)).1
    change ((CochainComplex.truncLEMap f n).f n ≫ (CochainComplex.truncLEXIsoCycles L n).hom) ≫
      L.iCycles n = ((CochainComplex.truncLEXIsoCycles K n).hom ≫ cyclesMap f n) ≫ L.iCycles n
    rw [Category.assoc, truncLE_inclusion_boundary, Category.assoc, cyclesMap_i,
      ← Category.assoc, truncLE_inclusion_boundary]
    exact congrArg (fun g ↦ g.f n) (CochainComplex.ιTruncLE_naturality f n))

/-- Additivity of the actual truncation functor follows by cancellation of
its monomorphic natural inclusion. -/
instance canonicalTruncLEFunctor_additive (n : ℤ) :
    ((ComplexShape.embeddingUpIntLE n).truncLEFunctor A).Additive where
  map_add {K L} f g := by
    let : Mono (CochainComplex.ιTruncLE L n) := (CochainComplex.shortComplexTruncLE_shortExact L
      n).mono_f
    apply (cancel_mono (CochainComplex.ιTruncLE L n)).1
    change CochainComplex.truncLEMap (f + g) n ≫ CochainComplex.ιTruncLE L n =
      (CochainComplex.truncLEMap f n + CochainComplex.truncLEMap g n) ≫ CochainComplex.ιTruncLE L n
    simp only [Preadditive.add_comp, CochainComplex.ιTruncLE_naturality, Preadditive.comp_add]


/-- Canonical truncation preserves an ambient short exact sequence when its
rightmost term is acyclic. This is stronger than the acyclic-subcategory case. -/
theorem truncLE_shortExact (S : ShortComplex (CochainComplex A ℤ))
    (hS : S.ShortExact) (h₃ : S.X₃.Acyclic) (n : ℤ) :
    (S.map ((ComplexShape.embeddingUpIntLE n).truncLEFunctor A)).ShortExact := by
  apply (shortExact_iff_degreewise_shortExact _).2
  intro i
  change (S.map ((ComplexShape.embeddingUpIntLE n).truncLEFunctor A ⋙
    eval A (ComplexShape.up ℤ) i)).ShortExact
  rcases lt_trichotomy i n with hi | he | hi
  · exact (ShortComplex.shortExact_iff_of_iso (S.mapNatIso (truncLEEvalIsoBelow n i hi))).2
      ((shortExact_iff_degreewise_shortExact S).1 hS i)
  · subst i
    exact (ShortComplex.shortExact_iff_of_iso (S.mapNatIso (truncLEEvalIsoCycles n))).2
      (cycles_shortExact S hS h₃ n)
  · exact {
      mono_f := ((S.X₁.truncLE n).isZero_of_isStrictlyLE n i hi).mono _
      epi_g := ((S.X₃.truncLE n).isZero_of_isStrictlyLE n i hi).epi _
      exact := ShortComplex.exact_of_isZero_X₂ _
        ((S.X₂.truncLE n).isZero_of_isStrictlyLE n i hi) }


variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The existing canonical truncation functor, restricted to the actual
bounded acyclic termwise-P full subcategory. -/
def boundedAcyclicTruncLEFunctor (n : ℤ) :
    (boundedAcyclic P).FullSubcategory ⥤ (boundedAcyclic P).FullSubcategory :=
  (boundedAcyclic P).lift
    ((boundedAcyclic P).ι ⋙ (ComplexShape.embeddingUpIntLE n).truncLEFunctor A)
    (fun K ↦ truncLE_mem K.obj n P K.property)

instance boundedAcyclicTruncLEFunctor_additive (n : ℤ) :
    (boundedAcyclicTruncLEFunctor P n).Additive :=
  inferInstanceAs (Functor.Additive ((boundedAcyclic P).lift _ _))

/-- This is exactly the first projection of the previously constructed
actual truncation-sequence functor. -/
@[simp]
theorem boundedAcyclicTruncLEFunctor_eq_first (n : ℤ) :
    boundedAcyclicTruncLEFunctor P n =
      acyclicTruncationSequenceFunctor P n ⋙ ShortComplex.π₁ := rfl

variable [(abelianExactStructure A).IsExtensionClosed P]

/-- The actual canonical truncation is an exact functor on bounded acyclic
complexes. No preservation-of-conflations conclusion is supplied as input. -/
def boundedAcyclicTruncLEExactFunctor (n : ℤ) :
    ExactFunctor (boundedAcyclicExactStructure P) (boundedAcyclicExactStructure P) where
  toFunctor := boundedAcyclicTruncLEFunctor P n
  map_conflation S hS :=
    truncLE_shortExact (S.map (boundedAcyclic P).ι) hS S.X₃.property.2.2 n

end CochainComplex
