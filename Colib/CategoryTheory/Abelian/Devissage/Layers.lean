/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# The layer poset for classical dévissage

A layer of `M` is a pair of nested subobjects whose quotient belongs to `P`.
The ordering reverses the lower endpoint and preserves the upper endpoint,
exactly as in Quillen's proof. The intersection enlargement lemma below uses
subobject and binary-product closure, never extension closure.


## Implementation provenance

Adapted from `Quillen/Aglib/CategoryTheory/ExactCategory/Filtration/Layers.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and independent object/hom universes
are retained. No extension-closure assumption or Resolution structure is used.
The source `Quillen.Devissage` namespace is now
`CategoryTheory.Abelian.Devissage`; no K-theory dependency is introduced.
-/
@[expose] public section

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

namespace CategoryTheory.Abelian.Devissage

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A subquotient of `M` belonging to the dévissage subcategory. -/
@[ext]
structure Layer (P : ObjectProperty C) (M : C) where
  /-- The subobject divided out in the layer quotient. -/
  lower : Subobject M
  /-- The subobject containing `lower`; its quotient by `lower` is required to belong to `P`. -/
  upper : Subobject M
  le : lower ≤ upper
  property : P (cokernel (Subobject.ofLE lower upper le))

namespace Layer

variable {P : ObjectProperty C} {M : C}

/-- The object presented by a layer. -/
abbrev quotient (L : Layer P M) : C :=
  cokernel (Subobject.ofLE L.lower L.upper L.le)

instance : PartialOrder (Layer P M) where
  le L K := K.lower ≤ L.lower ∧ L.upper ≤ K.upper
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h k := ⟨k.1.trans h.1, h.2.trans k.2⟩
  le_antisymm L K h k := by
    apply Layer.ext
    · exact le_antisymm k.1 h.1
    · exact le_antisymm h.2 k.2

@[simp]
lemma le_iff (L K : Layer P M) :
    L ≤ K ↔ K.lower ≤ L.lower ∧ L.upper ≤ K.upper := Iff.rfl

end Layer

variable (P : ObjectProperty C) [P.IsClosedUnderSubobjects]
  [P.IsClosedUnderFiniteProducts]

/-- The quotient by an intersection embeds into the product of the two
quotients. The second quotient can be taken in any common ambient subobject.
This is the product argument in Quillen's one-filtration-step contraction. -/
lemma intersection_enlargement_mem {M : C} (L U A N : Subobject M)
    (hLU : L ≤ U) (hUN : U ≤ N) (hAN : A ≤ N)
    (hL : P (cokernel (Subobject.ofLE L U hLU)))
    (hA : P (cokernel (Subobject.ofLE A N hAN))) :
    P (cokernel (Subobject.ofLE (L ⊓ A) U (inf_le_left.trans hLU))) := by
  let f := Subobject.ofLE L U hLU
  let g := Subobject.ofLE U N hUN
  let b := Subobject.ofLE A N hAN
  let i := Subobject.ofLE (L ⊓ A) U (inf_le_left.trans hLU)
  let d := prod.lift (cokernel.π f) (g ≫ cokernel.π b)
  have wi : i ≫ d = 0 := by
    apply prod.hom_ext
    · simp only [d, assoc, prod.lift_fst, zero_comp]
      have hi : i = Subobject.ofLE (L ⊓ A) L inf_le_left ≫ f := by
        simp [i, f]
      rw [hi, assoc, cokernel.condition, comp_zero]
    · simp only [d, assoc, prod.lift_snd, zero_comp]
      have hi : i ≫ g = Subobject.ofLE (L ⊓ A) A inf_le_right ≫ b := by
        simp [i, g, b]
      rw [← assoc, hi, assoc, cokernel.condition, comp_zero]
  have hk : IsLimit (KernelFork.ofι i wi) := by
    apply KernelFork.IsLimit.ofι'
    intro T k hk
    have h₁ : k ≫ cokernel.π f = 0 := by
      have := congrArg (fun z => z ≫ prod.fst) hk
      simpa [d] using this
    have h₂ : (k ≫ g) ≫ cokernel.π b = 0 := by
      have := congrArg (fun z => z ≫ prod.snd) hk
      simpa [d, assoc] using this
    have hfac : (L ⊓ A).Factors (k ≫ U.arrow) := by
      rw [Subobject.inf_factors]
      constructor
      · apply (Subobject.factors_iff _ _).2
        refine ⟨Abelian.monoLift f k h₁, ?_⟩
        change Abelian.monoLift f k h₁ ≫ L.arrow = _
        rw [← Subobject.ofLE_arrow hLU, ← assoc]
        exact congrArg (fun z => z ≫ U.arrow) (Abelian.monoLift_comp f k h₁)
      · apply (Subobject.factors_iff _ _).2
        refine ⟨Abelian.monoLift b (k ≫ g) h₂, ?_⟩
        change Abelian.monoLift b (k ≫ g) h₂ ≫ A.arrow = _
        rw [← Subobject.ofLE_arrow hAN, ← assoc]
        rw [Abelian.monoLift_comp]
        simp [g]
    refine ⟨(L ⊓ A).factorThru (k ≫ U.arrow) hfac, ?_⟩
    apply (cancel_mono U.arrow).1
    simp [i]
  have hd : Mono (cokernel.desc i d wi) :=
    (ShortComplex.exact_of_f_is_kernel (ShortComplex.mk i d wi) hk).mono_cokernelDesc
  exact P.prop_of_mono (cokernel.desc i d wi) (P.prop_prod _ _ hL hA)

omit [P.IsClosedUnderFiniteProducts] in
/-- Intersecting both ends of a layer with a subobject gives a subobject of
its original quotient, and therefore preserves membership in `P`. -/
lemma intersection_restriction_mem {M : C} (L U A : Subobject M)
    (hLU : L ≤ U) (hL : P (cokernel (Subobject.ofLE L U hLU))) :
    P (cokernel (Subobject.ofLE (L ⊓ A) (U ⊓ A) (inf_le_inf_right A hLU))) := by
  have sq : IsPullback
      (Subobject.ofLE (L ⊓ A) L inf_le_left)
      (Subobject.ofLE (L ⊓ A) (U ⊓ A) (inf_le_inf_right A hLU))
      (Subobject.ofLE L U hLU)
      (Subobject.ofLE (U ⊓ A) U inf_le_left) := by
    apply IsPullback.of_bot (v₂₁ := Subobject.ofLE (U ⊓ A) A inf_le_right)
      (v₂₂ := U.arrow) (h₃₁ := A.arrow)
    · simpa using Subobject.inf_isPullback L A
    · simp
    · exact Subobject.inf_isPullback U A
  let := Abelian.mono_cokernel_map_of_isPullback sq.flip
  exact P.prop_of_mono (cokernel.map _ _ _ _ sq.flip.w) hL

namespace Layer

variable {P} {M : C}

/-- Layers supported inside a specified ambient subobject. The two endpoints
remain subobjects of `M`, avoiding arbitrary representative choices. -/
abbrev Supported (N : Subobject M) := { L : Layer P M // L.upper ≤ N }

/-- Intersect both endpoints with a subobject. -/
def restrict (A : Subobject M) (L : Layer P M) : Layer P M where
  lower := L.lower ⊓ A
  upper := L.upper ⊓ A
  le := inf_le_inf_right A L.le
  property := intersection_restriction_mem P L.lower L.upper A L.le L.property

omit [P.IsClosedUnderFiniteProducts] in
/-- Restriction is monotone for the layer ordering. -/
lemma restrict_mono (A : Subobject M) : Monotone (restrict (P := P) A) := by
  intro L K h
  exact ⟨inf_le_inf_right A h.1, inf_le_inf_right A h.2⟩

/-- Enlarge a layer by intersecting only its lower endpoint. -/
def enlarge {N A : Subobject M} (hAN : A ≤ N)
    (hA : P (cokernel (Subobject.ofLE A N hAN))) (L : Supported (P := P) N) :
    Supported (P := P) N :=
  ⟨{ lower := L.val.lower ⊓ A
     upper := L.val.upper
     le := inf_le_left.trans L.val.le
     property := intersection_enlargement_mem P L.val.lower L.val.upper A N
       L.val.le L.property hAN L.val.property hA }, L.property⟩

lemma enlarge_mono {N A : Subobject M} (hAN : A ≤ N)
    (hA : P (cokernel (Subobject.ofLE A N hAN))) :
    Monotone (enlarge (P := P) hAN hA) := by
  intro L K h
  exact ⟨inf_le_inf_right A h.1, h.2⟩

end Layer

end CategoryTheory.Abelian.Devissage
