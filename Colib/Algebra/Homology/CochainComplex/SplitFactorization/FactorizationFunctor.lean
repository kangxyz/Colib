/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.MappingCone.Identity
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationQuotient

/-!
# Functorial split-complex factorization

The identity-cone construction defines a middle-object functor with natural inclusion and
    projection maps on complexes.
-/
/-! Adapted from
`Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.FactorizationFunctor`
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

/-- The actual factorization object depends functorially on the input arrow. -/
def middleFunctor : Arrow (CochainComplex A ℤ) ⥤ CochainComplex A ℤ where
  obj f := middle f.hom
  map α := biprod.map (CochainComplex.identityConeFunctor.map α.left) α.right
  map_id f := by
    apply biprod.hom_ext
    · simp only [Arrow.id_left, CategoryTheory.Functor.map_id, Arrow.id_right,
        biprod.map_fst, Category.id_comp]
      exact Category.comp_id _
    · simp
  map_comp α β := by
    apply biprod.hom_ext <;> simp

/-- Naturality of the first factor, for actual commutative squares. -/
theorem inclusion_naturality {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g) :
    inclusion f.hom ≫ middleFunctor.map α = α.left ≫ inclusion g.hom := by
  apply biprod.hom_ext
  · ext n
    simp [inclusion, middleFunctor, identityConeFunctor, mappingCone.map]
  · simp [inclusion, middleFunctor]

/-- Naturality of the target section. -/
theorem section_naturality {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g) :
    (biprod.inr : f.right ⟶ middle f.hom) ≫ middleFunctor.map α =
      α.right ≫ (biprod.inr : g.right ⟶ middle g.hom) := by
  simp [middleFunctor]

/-- Naturality of the second factor. -/
theorem projection_naturality {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g) :
    middleFunctor.map α ≫ projection g.hom = projection f.hom ≫ α.right := by
  simp [middleFunctor, projection]

/-- The first factor as a natural transformation on the arrow category. -/
def inclusionNat : Arrow.leftFunc ⟶ middleFunctor (A := A) where
  app f := inclusion f.hom
  naturality _ _ α := (inclusion_naturality α).symm

/-- The target section as a natural transformation on the arrow category. -/
def sectionNat : Arrow.rightFunc ⟶ middleFunctor (A := A) where
  app _ := biprod.inr
  naturality _ _ α := (section_naturality α).symm

/-- The second factor as a natural transformation on the arrow category. -/
def projectionNat : middleFunctor (A := A) ⟶ Arrow.rightFunc where
  app f := projection f.hom
  naturality _ _ α := projection_naturality α

/-- The functorial factorization satisfies its cylinder-axiom projection
condition, separately from the other cylinder-functor conditions. -/
theorem projectionNat_quasiIso (f : Arrow (CochainComplex A ℤ)) :
    QuasiIso (projectionNat.app f) := projection_quasiIso f.hom

/-- A quasi-isomorphism on the targets of a commutative square suffices for
a quasi-isomorphism on the factorization objects. -/
theorem middleFunctor_map_quasiIso {f g : Arrow (CochainComplex A ℤ)} (α : f ⟶ g)
    [QuasiIso α.right] : QuasiIso (middleFunctor.map α) := by
  have h : QuasiIso (middleFunctor.map α ≫ projection g.hom) := by
    rw [projection_naturality]
    infer_instance
  exact (quasiIso_iff_comp_right _ (projection g.hom)).1 h

end CochainComplex.SplitFactorization

end
