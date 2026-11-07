/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.DegreewiseSplitMono
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.RelativeQuotient
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # The actual shifted-source quotient of the relative complex cylinder -/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.ComplexQuotient`
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
  {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g)

/-- The projection to the shifted actual cokernel of the map on sources. -/
def relativeQuotientProjection : middle g.hom ⟶ (cokernel α.left)⟦(1 : ℤ)⟧ :=
  jointProjection g.hom ≫ (cokernel.π α.left)⟦(1 : ℤ)⟧'

variable {P : CochainComplex A ℤ} {i : middle f.hom ⟶ P}
  {j : g.left ⊞ g.right ⟶ P}
  (h : IsPushout (jointInclusion f.hom) (biprod.map α.left α.right) i j)
  (k : P ⟶ middle g.hom)
  (hi : i ≫ k = middleFunctor.map α) (hj : j ≫ k = jointInclusion g.hom)

include h hi hj in
/-- The genuine relative map is annihilated by the actual shifted-source quotient. -/
theorem relativeQuotient_zero : k ≫ relativeQuotientProjection α = 0 := by
  apply h.hom_ext
  · simp only [relativeQuotientProjection, ← Category.assoc, hi, comp_zero]
    rw [jointProjection_naturality, Category.assoc, ← Functor.map_comp,
      cokernel.condition, Functor.map_zero, comp_zero]
  · simp only [relativeQuotientProjection, ← Category.assoc, hj,
      jointInclusion_projection, zero_comp, comp_zero]

/-- The relative joint-endpoint sequence uses the actual shifted source cokernel. -/
def relativeQuotientSequence : ShortComplex (CochainComplex A ℤ) :=
  ShortComplex.mk k (relativeQuotientProjection α) (relativeQuotient_zero α h k hi hj)

/-- The actual displayed quotient is a cokernel, by the two genuine cokernel
universal properties and shift preservation. -/
def relativeQuotientIsCokernel :
    IsColimit (CokernelCofork.ofπ (relativeQuotientSequence α h k hi hj).g
      (relativeQuotientSequence α h k hi hj).zero) := by
  let : Epi (jointSequence f.hom).g := (jointSequence_shortExact f.hom).epi_g
  let c := CokernelCofork.ofπ (cokernel.π α.left) (cokernel.condition α.left)
  let q := (cokernel.π α.left)⟦(1 : ℤ)⟧'
  have hq : α.left⟦(1 : ℤ)⟧' ≫ q = 0 := by
    dsimp [q]
    rw [← Functor.map_comp, cokernel.condition, Functor.map_zero]
  have hc : IsColimit (CokernelCofork.ofπ q hq) :=
    CokernelCofork.mapIsColimit c (cokernelIsCokernel α.left)
      (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (1 : ℤ))
  exact relativeMiddleCokernelIsColimit (jointSequenceMap α)
    (jointSequence_shortExact g.hom).gIsCokernel k hi hj q hq hc
    (relativeQuotient_zero α h k hi hj)

/-- The relative map is a genuine degreewise-split short exact inclusion,
with exactly the shifted actual cokernel of the source map. -/
theorem relativeQuotientSequence_shortExact (hα : degreewiseSplitMono α.left) :
    (relativeQuotientSequence α h k hi hj).ShortExact where
  mono_f := degreewiseSplitMono_mono
    (relative_jointInclusion_degreewiseSplitMono α hα h k hi hj)
  epi_g := Cofork.IsColimit.epi (relativeQuotientIsCokernel α h k hi hj)
  exact := (relativeQuotientSequence α h k hi hj).exact_of_g_is_cokernel
    (relativeQuotientIsCokernel α h k hi hj)

end CochainComplex.SplitFactorization
