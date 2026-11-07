/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.Algebra.Homology.CochainComplex.ExactSubcategory.FixedBounds
public import Mathlib.Data.Finset.Lattice.Fold

/-! # Canonical increasing bounds and genuine finite-family coverage

Every bounded acyclic complex, and every finite family of such complexes,
lies in one actual symmetric term-bound stratum. The canonical transition
functors are genuinely exact. No global bound on all complexes is assumed.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedStrata`
at pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe v u w
namespace CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Larger specified bounds retain all actual vanishing evidence. -/
theorem HasTermBounds.mono {K : CochainComplex A ℤ} {a b c d : ℤ}
    (hK : HasTermBounds K a b) (ha : c ≤ a) (hb : b ≤ d) : HasTermBounds K c d := by
  intro i hi
  exact hK i (hi.elim (fun h ↦ Or.inl (lt_of_lt_of_le h ha))
    (fun h ↦ Or.inr (lt_of_le_of_lt hb h)))

/-- Every actual term-bounded complex has some symmetric natural-number bound. -/
theorem TermBounded.exists_symmetric {K : CochainComplex A ℤ} (hK : TermBounded K) :
    ∃ N : ℕ, HasTermBounds K (-(N : ℤ)) N := by
  obtain ⟨a, b, hK⟩ := hK
  have ha := Int.self_le_toNat (-a)
  have hb := Int.self_le_toNat b
  exact ⟨(-a).toNat + b.toNat, HasTermBounds.mono hK (by omega) (by omega)⟩

variable (P : ObjectProperty A)

/-- The actual symmetric fixed-bound predicate inside the bounded acyclic category. -/
abbrev boundedStratum (N : ℕ) : ObjectProperty (boundedAcyclic P).FullSubcategory :=
  fixedAcyclicBounds P (-(N : ℤ)) N

/-- The actual strata form an increasing system. -/
theorem boundedStratum_mono {N M : ℕ} (h : N ≤ M) : boundedStratum P N ≤ boundedStratum P M := by
  intro K hK
  exact hK.mono (by omega) (by omega)

/-- Coverage is objectwise; no common bound is postulated for the whole category. -/
theorem boundedStratum_covers (K : (boundedAcyclic P).FullSubcategory) :
    ∃ N : ℕ, boundedStratum P N K := K.property.1.exists_symmetric

/-- A genuinely finite family has one common actual term bound. -/
theorem boundedStratum_covers_finite {I : Type w} [Finite I]
    (K : I → (boundedAcyclic P).FullSubcategory) :
    ∃ N : ℕ, ∀ i, boundedStratum P N (K i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  choose n hn using fun i ↦ boundedStratum_covers P (K i)
  refine ⟨Finset.univ.sup n, fun i ↦ ?_⟩
  exact boundedStratum_mono P (Finset.le_sup (Finset.mem_univ i)) _ (hn i)

variable [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure A).IsExtensionClosed P]

/-- The inherited exact structure at a specified symmetric bound. -/
abbrev boundedStratumExactStructure (N : ℕ) := fixedAcyclicExactStructure P (-(N : ℤ)) N

/-- The actual canonical inclusion from one bound to a larger one. -/
def boundedStratumTransition {N M : ℕ} (h : N ≤ M) :
    (boundedStratum P N).FullSubcategory ⥤ (boundedStratum P M).FullSubcategory :=
  ObjectProperty.ιOfLE (boundedStratum_mono P h)

instance boundedStratumTransition_additive {N M : ℕ} (h : N ≤ M) :
    (boundedStratumTransition P h).Additive where
  map_add := by intros; rfl

/-- Every canonical increasing inclusion is genuinely exact. -/
def boundedStratumTransitionExact {N M : ℕ} (h : N ≤ M) :
    ExactFunctor (boundedStratumExactStructure P N) (boundedStratumExactStructure P M) where
  toFunctor := boundedStratumTransition P h
  map_conflation _ hS := hS

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsExtensionClosed P] in
/-- These are strict transition functors, not merely chosen categorical equivalences. -/
@[simp]
theorem boundedStratumTransition_id (N : ℕ) : boundedStratumTransition P (le_refl N) = 𝟭 _ := rfl

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsExtensionClosed P] in
@[simp]
theorem boundedStratumTransition_comp {N M L : ℕ} (h : N ≤ M) (h' : M ≤ L) :
    boundedStratumTransition P h ⋙ boundedStratumTransition P h' =
      boundedStratumTransition P (h.trans h') := rfl

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [(abelianExactStructure A).IsExtensionClosed P] in
@[simp]
theorem boundedStratumTransition_inclusion {N M : ℕ} (h : N ≤ M) :
    boundedStratumTransition P h ⋙ (boundedStratum P M).ι = (boundedStratum P N).ι := rfl

/-- The actual bounded stratum reflects inherited inflations: an admissible
quotient of a bounded target has the same strict term bounds. -/
theorem boundedStratum_inflation_iff (N : ℕ)
    {X Y : (boundedStratum P N).FullSubcategory} (f : X ⟶ Y) :
    (boundedStratumExactStructure P N).inflation f ↔
      (boundedAcyclicExactStructure P).inflation f.hom := by
  constructor
  · exact (fixedAcyclicInclusionExactFunctor P (-(N : ℤ)) N).map_inflation f
  · intro hf
    obtain ⟨Z, p, w, hS⟩ := hf
    apply (ExactSubcategory.inflation_iff (boundedAcyclicExactStructure P)
      (boundedStratum P N) f).2
    refine ⟨Z, ?_, p, w, hS⟩
    intro i hi
    have hs := (shortExact_iff_degreewise_shortExact
      ((ShortComplex.mk f.hom p w).map (boundedAcyclic P).ι)).1 hS i
    let : Epi (p.hom.f i) := hs.epi_g
    exact IsZero.of_epi (p.hom.f i) (Y.property i hi)

end CochainComplex
