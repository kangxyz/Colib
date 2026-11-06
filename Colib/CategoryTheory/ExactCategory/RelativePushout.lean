/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Isomorphisms
public import Colib.CategoryTheory.ExactCategory.CommonKernel

public import Colib.CategoryTheory.Limits.Shapes.CokernelPushout
public import Colib.CategoryTheory.ExactCategory.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Colib.CategoryTheory.ExactCategory.Functor.Pullbacks
public import Colib.CategoryTheory.ExactCategory.PullbackQuotient

/-!
# Actual conflation sequences of exact functors are cofibration sequences

The relative-cofibration axiom is derived from exactness of the quotient
functor. The genuine relative pushout fits in a conflation with the same
kernel as the target; its comparison is the pullback of an admissible
inclusion along an admissible epimorphism. No additivity conclusion occurs
among the hypotheses.


Implementation provenance:
`Quillen/Aglib/CategoryTheory/ExactCategory/RelativePushout.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps, bounds, hypotheses
and independent object/hom universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
universe v u v' u'

namespace CategoryTheory.ExactCategory

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- The actual relative pushout comparison of two conflations is admissible
whenever the map on their actual quotients is admissible. -/
theorem relativePushout_inflation (E : ExactStructure C)
    {S T : ShortComplex C} (φ : S ⟶ T) (hS : E.conflation S)
    (hT : E.conflation T) (hφ : E.inflation φ.τ₃)
    [HasPushout S.f φ.τ₁] :
    E.inflation (pushout.desc φ.τ₂ T.f φ.comm₁₂.symm) := by
  let q := pushout.desc (f := S.f) (g := φ.τ₁) φ.τ₂ T.f φ.comm₁₂.symm
  let U := CategoryTheory.ExactCategory.ExactStructure.pushoutConflation T.X₁ φ.τ₁ (S := S)
  have hU : E.conflation U := E.pushoutConflation_mem hS φ.τ₁
  have hiq : U.f ≫ q = T.f := by simp [U, q,
    CategoryTheory.ExactCategory.ExactStructure.pushoutConflation]
  have hpq : U.g ≫ φ.τ₃ = q ≫ T.g := by
    apply pushout.hom_ext
    · simp only [U, CategoryTheory.ExactCategory.ExactStructure.pushoutConflation, q,
      pushout.inl_desc_assoc]
      exact φ.comm₂₃.symm
    · simp [U, CategoryTheory.ExactCategory.ExactStructure.pushoutConflation, q, T.zero]
  have sq := E.isPullback_of_conflations_same_kernel hU hT q φ.τ₃ hiq hpq
  obtain ⟨Q, p, w, hQ⟩ := hφ
  exact E.inflation_of_conflation
    (ExactStructure.pullback_conflation_same_quotient E sq w hQ
      (E.deflation_of_conflation hT))

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
variable (E : ExactStructure C) (E' : ExactStructure D)
variable {F G H : C ⥤ D} (a : F ⟶ G) (b : G ⟶ H) (w : a ≫ b = 0)
variable (hc : ∀ X, E'.conflation
  (ShortComplex.mk (a.app X) (b.app X) (NatTrans.congr_app w X)))

/-- The pointwise actual conflations, without modifying their arrows. -/
def exactFunctorSequenceAt (X : C) : ShortComplex D :=
  ShortComplex.mk (a.app X) (b.app X) (NatTrans.congr_app w X)

/-- The actual map of pointwise conflations induced by a source morphism. -/
def exactFunctorSequenceMap {X Y : C} (f : X ⟶ Y) :
    exactFunctorSequenceAt a b w X ⟶ exactFunctorSequenceAt a b w Y where
  τ₁ := F.map f
  τ₂ := G.map f
  τ₃ := H.map f
  comm₁₂ := a.naturality f
  comm₂₃ := b.naturality f

end CategoryTheory.ExactCategory
