/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DeformationRetract.Composition
public import Colib.Topology.MappingCylinder.Fiberwise.RelativeHomotopy
public import Colib.Topology.HomotopyPullback.StrictComparison

/-!
# A genuine two-ended bridge for equivalent fibrations

Two actual mapping cylinders glued at their common source form a bridge
with strong deformations to both target ends over the unchanged base.
This retains a strict map from the original span, avoiding an assumption
of coherence for chosen homotopy inverses.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/FiberwiseBridge/Basic.lean` at
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
namespace TopCat.MappingCylinder

/-- The concrete fiberwise inverse data give the source SDR used by a
mapping-cylinder bridge. -/
theorem mappingCylinder_sourceStrongDeformationRetract_of_fiberwiseEquiv
    {A B M T : TopCat.{u}} {f : A ⟶ B}
    {l : A ⊗ TopCat.I ⟶ M} {c : B ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : B ⟶ T)
    (E : FiberwiseHomotopyEquiv (f ≫ base).hom base.hom) (he : E.toMap = f.hom) :
    ∃ R : TopCat.CylinderStrongDeformationRetract (TopCat.ι₀ ≫ l),
      R.r ≫ f ≫ base = TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base ∧
        R.H ≫ TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base =
          fst M TopCat.I ≫ TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base := by
  let H : TopCat.Homotopy (f ≫ TopCat.ofHom E.invMap) (𝟙 A) :=
    E.left.cast (by rw [he]; rfl) rfl
  let K : TopCat.Homotopy (TopCat.ofHom E.invMap ≫ f) (𝟙 B) :=
    E.right.cast (by rw [he]; rfl) rfl
  apply mappingCylinder_sourceStrongDeformationRetract_over sq base
    (TopCat.ofHom E.invMap) H K
  · ext x
    exact E.inv_over x
  · exact E.left_over
  · exact E.right_over

/-- Ordinary equivalence over a base between genuine fibrations suffices;
the required fiberwise inverse and deformation data are constructed. -/
theorem mappingCylinder_sourceStrongDeformationRetract_of_fibrations
    {A B M T : TopCat.{u}} {f : A ⟶ B}
    {l : A ⊗ TopCat.I ⟶ M} {c : B ⟶ M}
    (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (base : B ⟶ T)
    (hA : HomotopyLiftingProperty (f ≫ base).hom) (hB : HomotopyLiftingProperty base.hom)
    (E : ContinuousMap.HomotopyEquiv A B) (he : E.toFun = f.hom) :
    ∃ R : TopCat.CylinderStrongDeformationRetract (TopCat.ι₀ ≫ l),
      R.r ≫ f ≫ base = TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base ∧
        R.H ≫ TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base =
          fst M TopCat.I ≫ TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base := by
  let F := fiberwiseEquivOfFibrationHomotopyEquiv (f ≫ base).hom base.hom hA hB E
    (by rw [he]; rfl)
  apply mappingCylinder_sourceStrongDeformationRetract_of_fiberwiseEquiv sq base F
  exact (fiberwiseEquivOfFibrationHomotopyEquiv_toMap _ _ _ _ _ _).trans he

end TopCat.MappingCylinder

namespace TopCat.FiberwiseBridge
open TopCat.MappingCylinder
variable {A B C M N Z T : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {lM : A ⊗ TopCat.I ⟶ M} {cM : B ⟶ M}
  {lN : A ⊗ TopCat.I ⟶ N} {cN : C ⟶ N}
  (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f lM cM)
  (sqN : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) g lN cN)
  {m : M ⟶ Z} {n : N ⟶ Z}
  (sq : IsPushout (TopCat.ι₀ ≫ lM) (TopCat.ι₀ ≫ lN) m n)
  (b : B ⟶ T) (c : C ⟶ T) (w : f ≫ b = g ≫ c)

/-- The bridge projection to `T`, induced by the two mapping-cylinder projections followed by `b`
and `c`; the equality `f ≫ b = g ≫ c` identifies their values on the common source. -/
def projection : Z ⟶ T := sq.desc
  (TopCat.MappingCylinder.mappingCylinderProjection sqM ≫ b)
  (TopCat.MappingCylinder.mappingCylinderProjection sqN ≫ c) (by
    simp only [Category.assoc, TopCat.MappingCylinder.mappingCylinderProjection_start_assoc]
    exact w)

@[reassoc (attr := simp)] theorem projection_left :
    m ≫ projection sqM sqN sq b c w = TopCat.MappingCylinder.mappingCylinderProjection sqM ≫ b :=
  sq.inl_desc _ _ _
@[reassoc (attr := simp)] theorem projection_right :
    n ≫ projection sqM sqN sq b c w = TopCat.MappingCylinder.mappingCylinderProjection sqN ≫ c :=
  sq.inr_desc _ _ _

/-- Both ends of the actual glued bridge strongly deform over its common
base, using only the two original fiberwise equivalences. -/
theorem exists_strongDeformationRetracts
    (E : FiberwiseHomotopyEquiv (f ≫ b).hom b.hom) (he : E.toMap = f.hom)
    (F : FiberwiseHomotopyEquiv (g ≫ c).hom c.hom) (hf : F.toMap = g.hom) :
    ∃ (R : TopCat.CylinderStrongDeformationRetract (cM ≫ m))
      (S : TopCat.CylinderStrongDeformationRetract (cN ≫ n)),
      R.H ≫ projection sqM sqN sq b c w = fst Z TopCat.I ≫ projection sqM sqN sq b c w ∧
      S.H ≫ projection sqM sqN sq b c w = fst Z TopCat.I ≫ projection sqM sqN sq b c w := by
  obtain ⟨R₀, _, hR₀⟩ := mappingCylinder_sourceStrongDeformationRetract_of_fiberwiseEquiv sqM b E he
  obtain ⟨R₁, _, hR₁⟩ := mappingCylinder_sourceStrongDeformationRetract_of_fiberwiseEquiv sqN c F hf
  let S₀ := R₁.pushout sq.flip
  let S₁ := R₀.pushout sq
  let T₀ := TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sqM
  let T₁ := TopCat.MappingCylinder.mappingCylinderTargetStrongDeformationRetract sqN
  refine ⟨T₀.comp S₀, T₁.comp S₁, ?_, ?_⟩
  · apply T₀.comp_over S₀
    · simp only [projection_left]
      exact mappingCylinderTargetDeformation_over sqM b
    · apply R₁.pushout_homotopy_over sq.flip
      simpa only [projection_right] using hR₁
  · apply T₁.comp_over S₁
    · simp only [projection_right]
      exact mappingCylinderTargetDeformation_over sqN c
    · apply R₀.pushout_homotopy_over sq
      simpa only [projection_left] using hR₀

include sq in
/-- The common source maps strictly into the bridge from either cylinder. -/
theorem source_square : (TopCat.ι₀ ≫ lM) ≫ m = (TopCat.ι₀ ≫ lN) ≫ n := sq.w

end TopCat.FiberwiseBridge
