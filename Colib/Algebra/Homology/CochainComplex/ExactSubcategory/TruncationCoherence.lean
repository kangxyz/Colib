/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationExact

/-! # Genuine nested-truncation coherence

For n<m, the existing truncation map of the original inclusion
truncLE m K → K induces an actual isomorphism
truncLE n (truncLE m K) → truncLE n K. This is natural on every chain map
and compatible with the original inclusions. No acyclicity is needed.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.TruncationCoherence`
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

/-- The actual inclusion of an upper truncation induces an iso on cycles
strictly below its boundary. -/
theorem cyclesMap_truncationInclusion_isIso (K : CochainComplex A ℤ) (n m : ℤ) (h : n < m) :
    IsIso (cyclesMap (K.ιTruncLE m) n) := by
  apply ShortComplex.isIso_cyclesMap_of_isIso_of_mono'
    ((shortComplexFunctor A (ComplexShape.up ℤ) n).map (K.ιTruncLE m))
  · exact isIso_truncLE_inclusion_below K m n h
  · change Mono ((K.ιTruncLE m).f ((ComplexShape.up ℤ).next n))
    exact (truncationDegree_shortExact K m ((ComplexShape.up ℤ).next n)).mono_f

/-- The canonical map of nested truncations is an actual chain isomorphism. -/
theorem truncLECompMap_isIso (K : CochainComplex A ℤ) (n m : ℤ) (h : n < m) :
    IsIso (CochainComplex.truncLEMap (K.ιTruncLE m) n) := by
  let φ := K.ιTruncLE m
  let (i : ℤ) : IsIso ((CochainComplex.truncLEMap φ n).f i) := by
    rcases lt_trichotomy i n with hi | he | hi
    · let e₁ := (truncLEEvalIsoBelow (A := A) n i hi).app (K.truncLE m)
      let e₂ := (truncLEEvalIsoBelow (A := A) n i hi).app K
      let := isIso_truncLE_inclusion_below K m i (hi.trans h)
      have hf : (CochainComplex.truncLEMap φ n).f i = e₁.hom ≫ φ.f i ≫ e₂.inv := by
        apply (cancel_mono e₂.hom).1
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        simpa only [e₁, e₂, Iso.app_hom, Functor.comp_map,
          ComplexShape.Embedding.truncLEFunctor, eval, cyclesFunctor] using
          (truncLEEvalIsoBelow (A := A) n i hi).hom.naturality φ
      rw [hf]
      infer_instance
    · subst i
      let e₁ := (truncLEEvalIsoCycles (A := A) n).app (K.truncLE m)
      let e₂ := (truncLEEvalIsoCycles (A := A) n).app K
      let : IsIso (cyclesMap φ n) := cyclesMap_truncationInclusion_isIso K n m h
      have hf : (CochainComplex.truncLEMap φ n).f n = e₁.hom ≫ cyclesMap φ n ≫ e₂.inv := by
        apply (cancel_mono e₂.hom).1
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        simpa only [e₁, e₂, Iso.app_hom, Functor.comp_map,
          ComplexShape.Embedding.truncLEFunctor, eval, cyclesFunctor] using
          (truncLEEvalIsoCycles (A := A) n).hom.naturality φ
      rw [hf]
      infer_instance
    · exact (((K.truncLE m).truncLE n).isZero_of_isStrictlyLE n i hi).isIso
        ((K.truncLE n).isZero_of_isStrictlyLE n i hi) _
  exact Hom.isIso_of_components _

/-- Nested upper truncation is naturally the smaller upper truncation,
with the forward map exactly the truncation of the original inclusion. -/
def truncLECompIso (n m : ℤ) (h : n < m) :
    (ComplexShape.embeddingUpIntLE m).truncLEFunctor A ⋙
        (ComplexShape.embeddingUpIntLE n).truncLEFunctor A ≅
      (ComplexShape.embeddingUpIntLE n).truncLEFunctor A :=
  NatIso.ofComponents (fun K ↦ by
    let := truncLECompMap_isIso K n m h
    exact asIso (CochainComplex.truncLEMap (CochainComplex.ιTruncLE K m) n)) (by
      intro K L f
      change CochainComplex.truncLEMap (CochainComplex.truncLEMap f m) n ≫
          CochainComplex.truncLEMap (CochainComplex.ιTruncLE L m) n =
        CochainComplex.truncLEMap (CochainComplex.ιTruncLE K m) n ≫ CochainComplex.truncLEMap f n
      rw [← HomologicalComplex.truncLEMap_comp, ← HomologicalComplex.truncLEMap_comp,
        CochainComplex.ιTruncLE_naturality])

/-- The natural coherence iso preserves the original inclusions exactly. -/
@[reassoc]
theorem truncLECompIso_inclusion (K : CochainComplex A ℤ) (n m : ℤ) (h : n < m) :
    (truncLECompIso (A := A) n m h).hom.app K ≫ K.ιTruncLE n =
      (K.truncLE m).ιTruncLE n ≫ K.ιTruncLE m :=
  CochainComplex.ιTruncLE_naturality (K.ιTruncLE m) n

variable (P : ObjectProperty A) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsKernelClosed P]

/-- The actual nested-truncation coherence lifted to the inherited category. -/
def boundedAcyclicTruncLECompIso (n m : ℤ) (h : n < m) :
    boundedAcyclicTruncLEFunctor P m ⋙ boundedAcyclicTruncLEFunctor P n ≅
      boundedAcyclicTruncLEFunctor P n :=
  NatIso.ofComponents (fun K ↦ (boundedAcyclic P).isoMk ((truncLECompIso n m h).app K.obj)) (by
    intro K L f
    apply ObjectProperty.hom_ext
    exact (truncLECompIso (A := A) n m h).hom.naturality f.hom)

end CochainComplex
