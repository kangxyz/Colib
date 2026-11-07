/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedAcyclic
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationMaps
public import Colib.Algebra.Homology.CochainComplex.Cycles

/-!
# The actual acyclic truncation sequence stays in the bounded exact subcategory

This reuses mathlib's canonical truncation and its actual cokernel sequence.
Cycle closure proves membership at the truncation boundary; actual cokernel
uniqueness identifies the quotient boundary with the next cycle object.
Both outer complexes remain bounded, termwise in the chosen object
predicate, and acyclic. The resulting sequence is a genuine conflation in
the inherited full exact subcategory of bounded acyclic complexes.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.AcyclicTruncation`
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
  (K : CochainComplex A ℤ) (n : ℤ)

/-- The genuine termwise short exact truncation sequence. -/
theorem truncationDegree_shortExact (i : ℤ) :
    ((K.shortComplexTruncLE n).map (eval A (ComplexShape.up ℤ) i)).ShortExact :=
  (shortExact_iff_degreewise_shortExact _).1 (K.shortComplexTruncLE_shortExact n) i

/-- The actual quotient is zero strictly below the truncation boundary. -/
theorem truncationQuotient_isZero_below (i : ℤ) (hi : i < n) :
    IsZero ((K.shortComplexTruncLE n).X₃.X i) :=
  (truncationDegree_shortExact K n i).isIso_f_iff.1
    (isIso_truncLE_inclusion_below K n i hi)

/-- At the boundary the genuine cokernel is canonically the next cycle
object, by the two actual cokernel universal properties. -/
def truncationQuotientBoundaryIso (hK : K.ExactAt (n + 1)) :
    (K.shortComplexTruncLE n).X₃.X n ≅ K.cycles (n + 1) :=
  (truncationDegree_shortExact K n n).gIsCokernel.coconePointUniqueUpToIso
    (isCokernelEpiComp (_root_.CochainComplex.cycleSequence_shortExact K n hK).gIsCokernel
      (K.truncLEXIsoCycles n).hom (truncLE_inclusion_boundary K n).symm)

/-- Truncation of an actual acyclic complex remains acyclic. -/
theorem truncLE_acyclic (hK : K.Acyclic) : (K.truncLE n).Acyclic :=
  (K.acyclic_truncLE_iff n (n + 1)).2 ((K.isGE_iff (n + 1)).2 (fun i _ ↦ hK i))

/-- The actual cokernel of the acyclic truncation inclusion is acyclic. -/
theorem truncationQuotient_acyclic (hK : K.Acyclic) : (K.shortComplexTruncLE n).X₃.Acyclic := by
  apply (K.shortComplexTruncLE_shortExact n).acyclic_X₃
  rw [quasiIso_iff]
  intro i
  exact (quasiIsoAt_iff_exactAt' _ i (hK i)).2 (truncLE_acyclic K n hK i)

/-- The subcomplex inherits every strict term bound from the original complex. -/
theorem truncLE_termBounded (hK : TermBounded K) : TermBounded (K.truncLE n) := by
  obtain ⟨a, b, hab⟩ := hK
  refine ⟨a, b, fun i hi ↦ ?_⟩
  let : Mono ((K.ιTruncLE n).f i) := (truncationDegree_shortExact K n i).mono_f
  exact IsZero.of_mono ((K.ιTruncLE n).f i) (hab i hi)

/-- The actual quotient inherits every strict term bound too. -/
theorem truncationQuotient_termBounded (hK : TermBounded K) :
    TermBounded (K.shortComplexTruncLE n).X₃ := by
  obtain ⟨a, b, hab⟩ := hK
  exact ⟨a, b, fun i hi ↦ IsZero.of_epi ((K.shortComplexTruncLE n).g.f i) (hab i hi)⟩

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The canonical truncation stays bounded, termwise in P, and acyclic. -/
theorem truncLE_mem (hK : boundedAcyclic P K) : boundedAcyclic P (K.truncLE n) := by
  obtain ⟨a, b, hab⟩ := hK.1
  refine ⟨truncLE_termBounded K n hK.1, ?_, truncLE_acyclic K n hK.2.2⟩
  intro i
  rcases lt_trichotomy i n with hi | he | hi
  · exact P.prop_of_iso (K.truncLEXIso n i hi).symm (hK.2.1 i)
  · subst i
    exact P.prop_of_iso (K.truncLEXIsoCycles n).symm
      (_root_.CochainComplex.cycles_mem P K hK.2.1 hK.2.2 b (fun j hj ↦ hab j (Or.inr hj)) n)
  · exact P.prop_of_isZero ((K.truncLE n).isZero_of_isStrictlyLE n i hi)

/-- The genuine quotient also remains termwise in P, using zero objects
below the boundary, the next cycle at the boundary, and original terms above. -/
theorem truncationQuotient_mem (hK : boundedAcyclic P K) :
    boundedAcyclic P (K.shortComplexTruncLE n).X₃ := by
  obtain ⟨a, b, hab⟩ := hK.1
  refine ⟨truncationQuotient_termBounded K n hK.1, ?_,
    truncationQuotient_acyclic K n hK.2.2⟩
  intro i
  rcases lt_trichotomy i n with hi | he | hi
  · exact P.prop_of_isZero (truncationQuotient_isZero_below K n i hi)
  · subst i
    exact P.prop_of_iso (truncationQuotientBoundaryIso K n (hK.2.2 (n + 1))).symm
      (_root_.CochainComplex.cycles_mem P K hK.2.1 hK.2.2 b (fun j hj ↦ hab j (Or.inr hj)) (n + 1))
  · let S := (K.shortComplexTruncLE n).map (eval A (ComplexShape.up ℤ) i)
    let : IsIso S.g := (truncationDegree_shortExact K n i).isIso_g_iff.2
      ((K.truncLE n).isZero_of_isStrictlyLE n i hi)
    exact P.prop_of_iso (asIso S.g) (hK.2.1 i)

/-- The original truncation short exact sequence, lifted without changing
any ambient object or arrow to the actual bounded acyclic full subcategory. -/
def acyclicTruncationSequence (hK : boundedAcyclic P K) :
    ShortComplex (boundedAcyclic P).FullSubcategory :=
  ShortComplex.mk
    ((boundedAcyclic P).homMk (K.shortComplexTruncLE n).f :
      (⟨K.truncLE n, truncLE_mem K n P hK⟩ : (boundedAcyclic P).FullSubcategory) ⟶ ⟨K, hK⟩)
    ((boundedAcyclic P).homMk (K.shortComplexTruncLE n).g :
      (⟨K, hK⟩ : (boundedAcyclic P).FullSubcategory) ⟶
        ⟨(K.shortComplexTruncLE n).X₃, truncationQuotient_mem K n P hK⟩)
    (ObjectProperty.hom_ext _ (K.shortComplexTruncLE n).zero)

variable [(abelianExactStructure A).IsExtensionClosed P]

/-- The actual acyclic truncation sequence is an inherited conflation. -/
theorem acyclicTruncationSequence_conflation (hK : boundedAcyclic P K) :
    (boundedAcyclicExactStructure P).conflation (acyclicTruncationSequence K n P hK) :=
  K.shortComplexTruncLE_shortExact n

end CochainComplex
