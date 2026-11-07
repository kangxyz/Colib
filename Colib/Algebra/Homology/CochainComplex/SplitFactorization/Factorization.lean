/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.DegreewiseSplitMono
public import Colib.Algebra.Homology.CochainComplex.QuasiIsoGluing
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# A split-cofibration factorization of every chain map

The map `f : K ⟶ L` factors through `Cone(id K) ⊞ L`. The first arrow
is split in each degree, although generally not split as a chain map.
The second arrow is an actual chain homotopy equivalence, proved using the
contracting homotopy of the identity cone. This is an ambient factorization;
closure of a chosen full subcategory and its quotient is a separate issue.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.Factorization`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CochainComplex



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

universe v u

namespace CochainComplex.SplitFactorization

variable {A : Type u} [Category.{v} A] [Abelian A]
  {K L : CochainComplex A ℤ} (f : K ⟶ L)

/-- A chain-map factorization object with a contractible summand. -/
abbrev middle (_f : K ⟶ L) := mappingCone (𝟙 K) ⊞ L

/-- The first arrow records both the cone inclusion and the original map. -/
def inclusion : K ⟶ middle f := biprod.lift (mappingCone.inr (𝟙 K)) f

/-- The projection back to the target. -/
abbrev projection : middle f ⟶ L := biprod.snd

@[reassoc (attr := simp)]
theorem inclusion_projection : inclusion f ≫ projection f = f := by
  simp [inclusion]

/-- The explicit degreewise retraction of the first factor. -/
theorem inclusion_degreewiseSplitMono : degreewiseSplitMono (inclusion f) := by
  intro n
  refine IsSplitMono.mk' {
    retraction := (biprod.fst : middle f ⟶ mappingCone (𝟙 K)).f n ≫
      (mappingCone.snd (𝟙 K)).v n n (add_zero n)
    id := ?_ }
  simp [inclusion, ← comp_f_assoc]

/-- The second factor is a genuine homotopy equivalence. Its contracting
homotopy is obtained from the identity cone's standard contracting homotopy. -/
def projectionHomotopyEquiv : HomotopyEquiv (middle f) L where
  hom := projection f
  inv := biprod.inr
  homotopyHomInvId :=
    let h₀ : Homotopy (𝟙 (mappingCone (𝟙 K))) 0 :=
      mappingCone.liftHomotopy _ _ _ (mappingCone.snd _) 0 (by simp) (by simp)
    let h₁ := (h₀.compRight
      (biprod.inl : _ ⟶ middle f)).compLeft
        (biprod.fst : middle f ⟶ _)
    let h₂ := Homotopy.add h₁ (Homotopy.refl (biprod.snd ≫ biprod.inr))
    (Homotopy.ofEq (by simp [projection])).trans
      (h₂.symm.trans (Homotopy.ofEq (by simp)))
  homotopyInvHomId := Homotopy.ofEq (by simp)

instance projection_quasiIso : QuasiIso (projection f) :=
  (projectionHomotopyEquiv f).quasiIso_hom

/-- Every actual chain map admits a split-cofibration/quasi-isomorphism
factorization, without boundedness or projective/injective hypotheses. -/
theorem exists_factorization :
    ∃ (M : CochainComplex A ℤ) (i : K ⟶ M) (p : M ⟶ L),
      degreewiseSplitMono i ∧ QuasiIso p ∧ i ≫ p = f :=
  ⟨middle f, inclusion f, projection f, inclusion_degreewiseSplitMono f,
    (show QuasiIso (projection f) from inferInstance), inclusion_projection f⟩

end CochainComplex.SplitFactorization
