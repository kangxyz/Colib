/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.DegreewiseSplitMono
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Joint endpoints of the complex cylinder

The source and target inclusions into the functorial factorization jointly
form a degreewise split monomorphism. Its actual cokernel is the shifted
source. The explicit short exact sequence supplies the joint-endpoint
cofibration condition in any shift-closed full complex subcategory.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.JointEndpoints`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CochainComplex



noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

universe v u

namespace CochainComplex.SplitFactorization

variable {A : Type u} [Category.{v} A] [Abelian A]
  {K L : CochainComplex A ℤ} (f : K ⟶ L)

/-- Both endpoints mapped into the factorization object. -/
def jointInclusion : K ⊞ L ⟶ middle f := biprod.desc (inclusion f) biprod.inr

/-- The quotient of both endpoints is the shifted source. -/
def jointProjection : middle f ⟶ K⟦(1 : ℤ)⟧ :=
  biprod.fst ≫ (mappingCone.triangle (𝟙 K)).mor₃

@[reassoc (attr := simp)]
theorem jointInclusion_projection : jointInclusion f ≫ jointProjection f = 0 := by
  apply biprod.hom_ext' <;> simp [jointInclusion, jointProjection, inclusion]

/-- The joint-endpoint short complex with the actual shifted-source quotient. -/
def jointSequence : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk (jointInclusion f) (jointProjection f) (jointInclusion_projection f)

/-- A degreewise retraction of the joint endpoint map. -/
def jointRetraction (n : ℤ) : (middle f).X n ⟶ (K ⊞ L).X n :=
  degreeRetraction f n ≫ (biprod.inl : K ⟶ K ⊞ L).f n +
    ((biprod.snd : middle f ⟶ L).f n - degreeRetraction f n ≫ f.f n) ≫
      (biprod.inr : L ⟶ K ⊞ L).f n

/-- The joint endpoint sequence is split exact in every degree. -/
def jointSequenceSplitting (n : ℤ) :
    ((jointSequence f).map (eval A (ComplexShape.up ℤ) n)).Splitting where
  r := jointRetraction f n
  s := (mappingCone.triangleRotateShortComplexSplitting (𝟙 K) n).s ≫
    (biprod.inl : mappingCone (𝟙 K) ⟶ middle f).f n
  f_r := by
    dsimp [jointSequence]
    simp [jointRetraction, degreeRetraction, jointInclusion, inclusion,
      biprodX_ext_from_iff, biprodX_ext_to_iff]
  s_g := by
    dsimp [jointSequence]
    simp [jointProjection, ← comp_f_assoc]
  id := by
    dsimp [jointSequence]
    simp [jointRetraction, degreeRetraction, jointInclusion, jointProjection, inclusion,
      biprodX_ext_from_iff, biprodX_ext_to_iff,
      mappingCone.ext_from_iff _ (n + 1) n rfl,
      mappingCone.ext_to_iff _ _ (n + 1) rfl]

/-- Both endpoints together form a degreewise split cofibration. -/
theorem jointInclusion_degreewiseSplitMono : degreewiseSplitMono (jointInclusion f) :=
  fun n ↦ (jointSequenceSplitting f n).isSplitMono_f

/-- The joint endpoint sequence is an actual short exact sequence of complexes. -/
theorem jointSequence_shortExact : (jointSequence f).ShortExact :=
  shortExact_of_degreewise_shortExact _ (fun n ↦ (jointSequenceSplitting f n).shortExact)

end CochainComplex.SplitFactorization
