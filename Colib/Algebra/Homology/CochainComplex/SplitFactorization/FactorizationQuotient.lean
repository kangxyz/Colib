/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.Factorization
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ExactSequences
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# The actual quotient of the split-cofibration factorization

For `f : K ⟶ L`, the factorization inclusion into `Cone(id K) ⊞ L`
has quotient `Cone(-f)`. We construct the chain quotient map and a
splitting of its short exact sequence in every degree. This supplies the
quotient-closure input when restricting the factorization to perfect
complexes.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationQuotient`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

universe v u

namespace CochainComplex.SplitFactorization

variable {A : Type u} [Category.{v} A] [Abelian A]
  {K L : CochainComplex A ℤ} (f : K ⟶ L)

/-- The explicit quotient chain map onto the cone of `-f`. -/
def quotientMap : middle f ⟶ mappingCone (-f) :=
  biprod.desc (mappingCone.map (𝟙 K) (-f) (𝟙 K) (-f) (by simp))
    (mappingCone.inr (-f))

@[reassoc (attr := simp)]
theorem inclusion_quotientMap : inclusion f ≫ quotientMap f = 0 := by
  simp [inclusion, quotientMap, mappingCone.map]

/-- The actual short complex defining the quotient of the first factor. -/
def quotientSequence : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (inclusion f) (quotientMap f) (inclusion_quotientMap f)

/-- The chosen termwise retraction, not asserted to be a chain map. -/
def degreeRetraction (n : ℤ) : (middle f).X n ⟶ K.X n :=
  (biprod.fst : middle f ⟶ mappingCone (𝟙 K)).f n ≫
    (mappingCone.snd (𝟙 K)).v n n (add_zero n)

/-- The chosen termwise quotient section, not asserted to be a chain map. -/
def degreeSection (n : ℤ) : (mappingCone (-f)).X n ⟶ (middle f).X n :=
  (mappingCone.fst (-f)).1.v n (n + 1) rfl ≫
    (mappingCone.inl (𝟙 K)).v (n + 1) n (by omega) ≫
      (biprod.inl : mappingCone (𝟙 K) ⟶ middle f).f n +
    (mappingCone.snd (-f)).v n n (add_zero n) ≫
      (biprod.inr : L ⟶ middle f).f n

/-- The factorization's quotient sequence splits in every degree. -/
def quotientSequenceSplitting (n : ℤ) :
    ((quotientSequence f).map (eval A (ComplexShape.up ℤ) n)).Splitting where
  r := degreeRetraction f n
  s := degreeSection f n
  f_r := by
    simp [quotientSequence, degreeRetraction, inclusion, ← comp_f_assoc]
  s_g := by
    dsimp [quotientSequence]
    simp [degreeSection, quotientMap, mappingCone.map,
      mappingCone.ext_from_iff _ (n + 1) n rfl]
  id := by
    dsimp [quotientSequence]
    simp [degreeRetraction, degreeSection, inclusion, quotientMap, mappingCone.map,
      HomologicalComplex.biprodX_ext_from_iff, HomologicalComplex.biprodX_ext_to_iff,
      mappingCone.ext_from_iff _ (n + 1) n rfl,
      mappingCone.ext_to_iff _ _ (n + 1) rfl]

/-- The quotient is an actual short exact sequence of complexes. -/
theorem quotientSequence_shortExact : (quotientSequence f).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (fun n ↦ (quotientSequenceSplitting f n).shortExact)

end CochainComplex.SplitFactorization
