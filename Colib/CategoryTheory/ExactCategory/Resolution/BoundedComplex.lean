/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.Cycles
public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.KernelClosed
public import Colib.CategoryTheory.ExactCategory.Resolution.Transport
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
import Mathlib.Tactic.Order

/-!
# Finite exact resolutions from bounded cochain complexes

A bounded complex of objects in a replete, kernel-closed class containing zero,
quasi-isomorphic to a single object, gives an actual finite resolution of that
object. Only kernels of epimorphisms between objects in the class are used.
No projectivity, uniform resolution length, or global dimension is assumed.

The positive exact tail first shows that the cycles in degree zero belong to
the class. The negative exact tail supplies the successive syzygies. All rows
are short exact sequences in the ambient abelian category, built from the
native cycles and homology maps of the given complex.

The elementary consecutive-cycle row is reused from
`Colib.Algebra.Homology.CochainComplex.Cycles`. It is the same construction as
the private helper in the pinned Stacks file
`Algebra/Homology/DerivedCategory/RightDerivedBoundedCohomologicalDimension.lean`.
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

attribute [local instance] Abelian.hasFiniteBiproducts

variable (K : CochainComplex C ℤ)

variable (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] [P.ContainsZero]
  [(abelianExactStructure C).IsKernelClosed P]

/-- Descending through the positive exact tail proves that its cycles lie in the
resolving class. The input is a finite tail ending in an actual zero term. -/
lemma prop_cycles_of_exact_positive (hterms : ∀ i, P (K.X i))
    (hexact : ∀ i, 0 < i → K.ExactAt i) (n : ℕ) (i : ℤ) (hi : 0 ≤ i)
    (hz : IsZero (K.X (i + n))) : P (K.cycles i) := by
  induction n generalizing i with
  | zero =>
    exact P.prop_of_isZero (IsZero.of_mono (K.iCycles i) (by simpa using hz))
  | succ n ih =>
    have hn : P (K.cycles (i + 1)) := ih (i + 1) (by omega) (by
      convert hz using 1
      congr 1
      omega)
    exact ExactStructure.IsKernelClosed.prop_kernel
      (E := abelianExactStructure C) (P := P)
      (K.cycleSequence_shortExact i (hexact (i + 1) (by omega))) (hterms i) hn

/-- A bounded-above positive exact tail places the degree-zero cycles in `P`. -/
lemma prop_cycles_zero_of_boundedAbove (hterms : ∀ i, P (K.X i))
    (hexact : ∀ i, 0 < i → K.ExactAt i) (b : ℤ) [K.IsStrictlyLE b] :
    P (K.cycles 0) := by
  apply K.prop_cycles_of_exact_positive P hterms hexact (b.toNat + 1) 0 (by omega)
  exact K.isZero_of_isStrictlyLE b _ (by omega)

/-- Ascending through a finite exact interval produces an actual finite
resolution of the cycles at its right endpoint. -/
def finiteResolutionCycles (hterms : ∀ i, P (K.X i)) (a : ℤ)
    (hz : IsZero (K.X a)) (n : ℕ)
    (hexact : ∀ i, a < i → i ≤ a + n → K.ExactAt i) :
    (abelianExactStructure C).FiniteResolution P (K.cycles (a + n)) := by
  induction n with
  | zero =>
    apply ExactStructure.FiniteResolution.of_mem
    exact P.prop_of_isZero (IsZero.of_mono (K.iCycles _) (by simpa using hz))
  | succ n ih =>
    have R := ih (fun i hi hi' => hexact i hi (by omega))
    have hs := K.cycleSequence_shortExact (a + n)
      (hexact (a + n + 1) (by omega) (by omega))
    have R' := ExactStructure.FiniteResolution.step
      (E := abelianExactStructure C) (P := P) (K.cycleSequence (a + n))
      hs (hterms _) R
    convert R' using 1
    congr 1
    omega

/-- A bounded-below negative exact tail resolves the cycles in degree `-1`. -/
def finiteResolutionCyclesNegOne (hterms : ∀ i, P (K.X i))
    (hexact : ∀ i, i < 0 → K.ExactAt i) (a : ℤ) [K.IsStrictlyGE a] :
    (abelianExactStructure C).FiniteResolution P (K.cycles (-1)) := by
  let l : ℤ := min a (-1) - 1
  have hl : l < a := by dsimp [l]; omega
  have hl' : l ≤ -1 := by dsimp [l]; omega
  have hn : l + ((-1 - l).toNat : ℤ) = -1 := by omega
  have R := K.finiteResolutionCycles P hterms l (K.isZero_of_isStrictlyGE a l hl)
    (-1 - l).toNat (fun i hi hi' => hexact i (by omega))
  exact hn ▸ R

/-- The canonical presentation of degree-zero homology by degree-zero cycles. -/
@[implicit_reducible]
def homologyZeroPresentation : ShortComplex C :=
  ShortComplex.mk (K.toCycles (-1) 0) (K.homologyπ 0)
    (K.toCycles_comp_homologyπ (-1) 0)

lemma homologyZeroPresentation_exact : K.homologyZeroPresentation.Exact :=
  K.homologyZeroPresentation.exact_of_g_is_cokernel
    (K.homologyIsCokernel (-1) 0 (by simp))

/-- The last negative differential maps onto the kernel of the homology quotient.
Its kernel is precisely the cycles in degree `-1`. -/
@[implicit_reducible]
def homologyZeroSyzygySequence : ShortComplex C :=
  ShortComplex.mk (K.iCycles (-1)) K.homologyZeroPresentation.toCycles (by
    rw [← cancel_mono K.homologyZeroPresentation.iCycles, Category.assoc,
      ShortComplex.toCycles_i, zero_comp]
    change K.iCycles (-1) ≫ K.toCycles (-1) 0 = 0
    rw [← cancel_mono (K.iCycles 0), Category.assoc, K.toCycles_i,
      K.iCycles_d, zero_comp])

lemma homologyZeroSyzygySequence_shortExact : K.homologyZeroSyzygySequence.ShortExact := by
  have : Epi K.homologyZeroPresentation.toCycles :=
    K.homologyZeroPresentation_exact.epi_toCycles
  refine
    { exact := K.homologyZeroSyzygySequence.exact_of_f_is_kernel ?_
      mono_f := inferInstanceAs (Mono (K.iCycles (-1)))
      epi_g := inferInstanceAs (Epi K.homologyZeroPresentation.toCycles) }
  exact isKernelOfComp (K.homologyZeroPresentation.iCycles ≫ K.iCycles 0)
    (K.d (-1) 0) (K.cyclesIsKernel (-1) 0 (by simp))
    K.homologyZeroSyzygySequence.zero (by
      change K.homologyZeroPresentation.toCycles ≫
        (K.homologyZeroPresentation.iCycles ≫ K.iCycles 0) = K.d (-1) 0
      rw [← Category.assoc, ShortComplex.toCycles_i]
      exact K.toCycles_i (-1) 0)

/-- Actual finite resolution of degree-zero homology, extracted from a bounded
complex that is exact away from degree zero. -/
def finiteResolutionHomologyZero (hterms : ∀ i, P (K.X i))
    (hexact : ∀ i, i ≠ 0 → K.ExactAt i)
    (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    (abelianExactStructure C).FiniteResolution P (K.homology 0) := by
  let R := K.finiteResolutionCyclesNegOne P hterms (fun i hi => hexact i (by omega)) a
  let R' := ExactStructure.FiniteResolution.step
    (E := abelianExactStructure C) (P := P) K.homologyZeroSyzygySequence
    K.homologyZeroSyzygySequence_shortExact (hterms (-1)) R
  let S := ShortComplex.mk K.homologyZeroPresentation.iCycles (K.homologyπ 0)
    K.homologyZeroPresentation.iCycles_g
  have hs : S.ShortExact :=
    { exact := S.exact_of_f_is_kernel K.homologyZeroPresentation.cyclesIsKernel }
  exact .step S hs
    (K.prop_cycles_zero_of_boundedAbove P hterms (fun i hi => hexact i (by omega)) b) R'

/-- A bounded complex of resolving objects quasi-isomorphic to a single object
provides a finite tower of actual short exact sequences resolving that object. -/
def finiteResolutionOfQuasiIsoSingle (M : C)
    (f : K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) [QuasiIso f]
    (hterms : ∀ i, P (K.X i)) (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    (abelianExactStructure C).FiniteResolution P M :=
  (K.finiteResolutionHomologyZero P hterms
    (fun i hi => (exactAt_iff_of_quasiIsoAt f i).2
      (HomologicalComplex.exactAt_single_obj _ 0 M i hi)) a b).ofIso
    (isoOfQuasiIsoAt f 0 ≪≫
      HomologicalComplex.singleObjHomologySelfIso _ 0 M)

/-- Existence form of the bounded-complex resolution construction, with no
common bound required for different objects. -/
theorem nonempty_finiteResolution_of_quasiIso_single (M : C)
    (f : K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj M) [QuasiIso f]
    (hterms : ∀ i, P (K.X i))
    (hbounded : (∃ a : ℤ, K.IsStrictlyGE a) ∧ ∃ b : ℤ, K.IsStrictlyLE b) :
    Nonempty ((abelianExactStructure C).FiniteResolution P M) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hbounded
  have := ha
  have := hb
  exact ⟨K.finiteResolutionOfQuasiIsoSingle P M f hterms a b⟩

end CochainComplex

attribute [colib_tag "COL-0271",
  colib_ref "WeibelKBook" "V, Resolution Theorem 3.1, page 20" "background"
    "Actual finite admissible resolutions; bounded-complex extraction and \
    full-subcategory lifting are proved here"]
  CochainComplex.finiteResolutionOfQuasiIsoSingle
  CochainComplex.nonempty_finiteResolution_of_quasiIso_single
