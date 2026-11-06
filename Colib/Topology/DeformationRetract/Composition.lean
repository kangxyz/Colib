/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DeformationRetract.FiberwisePushout

/-! Composition of actual strong deformation retractions, including its
strict base-preservation equation. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/DeformationRetract/Composition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and hypotheses. -/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.CylinderStrongDeformationRetract
variable {A B C T : TopCat.{u}} {i : A ⟶ B} {j : B ⟶ C}
  (R : TopCat.CylinderStrongDeformationRetract i) (S : TopCat.CylinderStrongDeformationRetract j)

/-- The explicit two-stage deformation underlying composition. -/
def compHomotopy : TopCat.Homotopy ((S.r ≫ R.r) ≫ (i ≫ j)) (𝟙 C) :=
  ((((TopCat.Homotopy.refl j).comp (TopCat.homotopyOfCylinder R.H R.H₀ R.H₁)).compContinuousMap
    S.r.hom).cast (by ext x; rfl) (by ext x; rfl)).trans (TopCat.homotopyOfCylinder S.H S.H₀ S.H₁)

/-- Strong deformation retractions compose as actual maps. -/
def comp : TopCat.CylinderStrongDeformationRetract (i ≫ j) where
  r := S.r ≫ R.r
  retract := by simp only [Category.assoc, ← Category.assoc j, S.retract, Category.id_comp,
    R.retract]
  H := (compHomotopy R S).h
  H₀ := (compHomotopy R S).ι₀_h
  H₁ := (compHomotopy R S).ι₁_h
  fixed := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    change compHomotopy R S (t.down, j (i a)) = j (i a)
    simp only [compHomotopy, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · have hs : S.r (j (i a)) = i a := ConcreteCategory.congr_hom S.retract (i a)
      change j (R.H (S.r (j (i a)), _)) = j (i a)
      rw [hs]
      exact congrArg j (ConcreteCategory.congr_hom R.fixed (a, _))
    · exact ConcreteCategory.congr_hom S.fixed (i a, _)

/-- A projection fixed by a deformation is fixed by its retraction too. -/
theorem retraction_over {A B T : TopCat.{u}} {i : A ⟶ B}
    (R : TopCat.CylinderStrongDeformationRetract i) (p : B ⟶ T)
    (hR : R.H ≫ p = fst B TopCat.I ≫ p) : R.r ≫ i ≫ p = p := by
  have hh := congrArg (fun k : B ⊗ TopCat.I ⟶ T ↦ TopCat.ι₀ ≫ k) hR
  simpa only [← Category.assoc, R.H₀, TopCat.ι₀_fst, Category.id_comp] using hh

/-- Composition preserves strict fiberwise deformation equations. -/
theorem comp_over (p : C ⟶ T)
    (hR : R.H ≫ j ≫ p = fst B TopCat.I ≫ j ≫ p)
    (hS : S.H ≫ p = fst C TopCat.I ≫ p) :
    (R.comp S).H ≫ p = fst C TopCat.I ≫ p := by
  apply ConcreteCategory.hom_ext
  rintro ⟨c, t⟩
  change p (compHomotopy R S (t.down, c)) = p c
  simp only [compHomotopy, ContinuousMap.Homotopy.trans_apply]
  split_ifs
  · exact (ConcreteCategory.congr_hom hR (S.r c, _)).trans
      (ConcreteCategory.congr_hom (S.retraction_over p hS) c)
  · exact ConcreteCategory.congr_hom hS (c, _)

end TopCat.CylinderStrongDeformationRetract
