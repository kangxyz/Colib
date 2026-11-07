/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.ComplexQuotient
public import Colib.CategoryTheory.ExactCategory.RelativePushout

/-!
# Monicity and exactness of the actual relative cylinder sequence

An ordinary monomorphism on sources makes the displayed relative joint map
monic and its actual shifted-source-cokernel sequence short exact.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.AmbientRelative`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
universe u v

namespace CochainComplex.SplitFactorization
attribute [local instance] Abelian.hasFiniteBiproducts
variable {A : Type u} [Category.{v} A] [Abelian A]
  {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g)
  {R : CochainComplex A ℤ} {i : middle f.hom ⟶ R} {j : g.left ⊞ g.right ⟶ R}
  (h : IsPushout (jointInclusion f.hom) (biprod.map α.left α.right) i j)
  (k : R ⟶ middle g.hom) (hi : i ≫ k = middleFunctor.map α)
  (hj : j ≫ k = jointInclusion g.hom)

include h hi hj in
/-- A monic source map suffices for the actual relative endpoint map to be monic.
No splitting, boundedness, or condition on the target map is used. -/
theorem relative_jointInclusion_mono [Mono α.left] : Mono k := by
  let E := abelianExactStructure (CochainComplex A ℤ)
  let q := pushout.desc (f := jointInclusion f.hom) (g := biprod.map α.left α.right)
    (middleFunctor.map α) (jointInclusion g.hom) (jointInclusion_naturality α)
  have hq : E.inflation q := CategoryTheory.ExactCategory.relativePushout_inflation E
    (jointSequenceMap α) (jointSequence_shortExact f.hom) (jointSequence_shortExact g.hom)
    ((abelianExactStructure_inflation_iff _ _).2 (by
      change Mono (α.left⟦(1 : ℤ)⟧')
      infer_instance))
  let : Mono q := (abelianExactStructure_inflation_iff _ _).1 hq
  let h₀ := IsPushout.of_hasPushout (jointInclusion f.hom) (biprod.map α.left α.right)
  let e := h₀.isoIsPushout _ _ h
  have he : e.hom ≫ k = q := by
    apply h₀.hom_ext
    · rw [← Category.assoc, h₀.inl_isoIsPushout_hom, hi]
      exact (pushout.inl_desc _ _ _).symm
    · rw [← Category.assoc, h₀.inr_isoIsPushout_hom, hj]
      exact (pushout.inr_desc _ _ _).symm
  have hk : k = e.inv ≫ q := by rw [← he]; simp
  rw [hk]
  infer_instance

include h hi hj in
/-- The original relative quotient sequence is short exact under the ordinary
monomorphism condition, with no degreewise split hypothesis. -/
theorem relativeQuotientSequence_shortExact_of_mono [Mono α.left] :
    (relativeQuotientSequence α h k hi hj).ShortExact where
  mono_f := relative_jointInclusion_mono α h k hi hj
  epi_g := Cofork.IsColimit.epi (relativeQuotientIsCokernel α h k hi hj)
  exact := (relativeQuotientSequence α h k hi hj).exact_of_g_is_cokernel
    (relativeQuotientIsCokernel α h k hi hj)

end CochainComplex.SplitFactorization
