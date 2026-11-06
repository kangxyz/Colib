/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.JointEndpoints

public import Colib.Algebra.Homology.CochainComplex.DegreewiseSplitMono
public import Colib.Algebra.Homology.MappingCone.Identity
public import Colib.CategoryTheory.ExactCategory.RelativeSplitMono

/-!
# Relative joint-endpoint maps of the actual complex cylinder

The identity-cone factorization gives a natural split short exact joint-endpoint
sequence. Its relative pushout map is degreewise split whenever the map on
sources is degreewise split. These are structural cylinder calculations, not a
fibration or K-theory comparison theorem.
-/
/-! Adapted from `Quillen.Aglib.Algebra.Homology.CochainComplex.SplitFactorization.RelativeComplex`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd. -/

@[expose] public section

open CochainComplex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory.ExactCategory
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
universe v u

namespace CochainComplex.SplitFactorization

variable {A : Type u} [Category.{v} A] [Abelian A]
  {f g : Arrow (CochainComplex A ℤ)}

/-- Naturality of both cylinder endpoints together. -/
theorem jointInclusion_naturality (α : f ⟶ g) :
    jointInclusion f.hom ≫ middleFunctor.map α =
      biprod.map α.left α.right ≫ jointInclusion g.hom := by
  apply biprod.hom_ext' <;>
    simp [jointInclusion, inclusion_naturality, section_naturality]

/-- Naturality of the actual shifted-source cylinder quotient. -/
theorem jointProjection_naturality (α : f ⟶ g) :
    middleFunctor.map α ≫ jointProjection g.hom =
      jointProjection f.hom ≫ α.left⟦(1 : ℤ)⟧' := by
  ext n
  simp [jointProjection, middleFunctor, identityConeFunctor, mappingCone.map,
    biprodX_ext_from_iff, mappingCone.ext_from_iff _ (n + 1) n rfl]

/-- A commutative square induces the genuine map of joint-endpoint sequences. -/
def jointSequenceMap (α : f ⟶ g) : jointSequence f.hom ⟶ jointSequence g.hom where
  τ₁ := biprod.map α.left α.right
  τ₂ := middleFunctor.map α
  τ₃ := α.left⟦(1 : ℤ)⟧'
  comm₁₂ := (jointInclusion_naturality α).symm
  comm₂₃ := jointProjection_naturality α

/-- The relative joint-endpoint pushout map is split in every degree.
Only the source map needs to be degreewise split for this relative statement. -/
theorem relative_jointInclusion_degreewiseSplitMono (α : f ⟶ g)
    (hα : degreewiseSplitMono α.left)
    {P : CochainComplex A ℤ} {i : middle f.hom ⟶ P}
    {j : g.left ⊞ g.right ⟶ P}
    (h : IsPushout (jointInclusion f.hom) (biprod.map α.left α.right) i j)
    (k : P ⟶ middle g.hom)
    (hi : i ≫ k = middleFunctor.map α) (hj : j ≫ k = jointInclusion g.hom) :
    degreewiseSplitMono k := by
  intro n
  let φ := (eval A (ComplexShape.up ℤ) n).mapShortComplex.map (jointSequenceMap α)
  let : IsSplitMono φ.τ₃ := hα (n + 1)
  exact isSplitMono_relative_of_splittings
    (jointSequenceSplitting f.hom n) (jointSequenceSplitting g.hom n) φ
    (h.map (eval A (ComplexShape.up ℤ) n)) (k.f n)
    (congrArg (fun t ↦ t.f n) hi) (congrArg (fun t ↦ t.f n) hj)

/-- Biprod maps retain degreewise splittings, without requiring the chosen
retractions to be chain maps. -/
theorem degreewiseSplitMono_biprodMap {K L K' L' : CochainComplex A ℤ}
    (a : K ⟶ K') (b : L ⟶ L') (ha : degreewiseSplitMono a)
    (hb : degreewiseSplitMono b) : degreewiseSplitMono (biprod.map a b) := by
  intro n
  let : IsSplitMono (a.f n) := ha n
  let : IsSplitMono (b.f n) := hb n
  refine IsSplitMono.mk' ⟨
    (biprod.fst : K' ⊞ L' ⟶ K').f n ≫ retraction (a.f n) ≫
      (biprod.inl : K ⟶ K ⊞ L).f n +
    (biprod.snd : K' ⊞ L' ⟶ L').f n ≫ retraction (b.f n) ≫
      (biprod.inr : L ⟶ K ⊞ L).f n, ?_⟩
  simp [← comp_f_assoc]

/-- The actual cylinder functor preserves degreewise split cofibrations
of squares. The proof factors its map through the relative endpoint pushout. -/
theorem middleFunctor_map_degreewiseSplitMono (α : f ⟶ g)
    (ha : degreewiseSplitMono α.left) (hb : degreewiseSplitMono α.right) :
    degreewiseSplitMono (middleFunctor.map α) := by
  let a := jointInclusion f.hom
  let b := biprod.map α.left α.right
  let k : pushout a b ⟶ middle g.hom := pushout.desc
    (middleFunctor.map α) (jointInclusion g.hom) (jointInclusion_naturality α)
  have hi : degreewiseSplitMono (pushout.inl a b) :=
    degreewiseSplitMono_pushout (degreewiseSplitMono_biprodMap α.left α.right ha hb)
      (IsPushout.of_hasPushout a b).flip
  have hk : degreewiseSplitMono k :=
    relative_jointInclusion_degreewiseSplitMono α ha (IsPushout.of_hasPushout a b)
      k (pushout.inl_desc _ _ _) (pushout.inr_desc _ _ _)
  have hcomp := (degreewiseSplitMono (A := A)).comp_mem _ _ hi hk
  simpa only [k, pushout.inl_desc] using hcomp

end CochainComplex.SplitFactorization
