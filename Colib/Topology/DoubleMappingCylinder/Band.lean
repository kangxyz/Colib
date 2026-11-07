/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.Collars
public import Colib.Topology.HomotopyPullback.ProductChart

/-! The exact overlap product charts and genuine fibration pullbacks in
an actual double mapping cylinder. -/
/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/Band.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and proofs
with native namespace and import ownership. -/
@[expose] public section

open Topology

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.DoubleCylinder

/-- The open subinterval of the unit interval between the bounds `lo` and `hi`. -/
abbrev Band (lo hi : I) := {t : I // lo < t ∧ t < hi}

/-- The inclusion of the band between `lo` and `hi` into the open unit interval. -/
def bandToInterior (lo hi : I) : C(Band lo hi, OpenInterval) :=
  ⟨fun t ↦ ⟨t.1, lt_of_le_of_lt lo.2.1 t.2.1, lt_of_lt_of_le t.2.2 hi.2.2⟩, by fun_prop⟩

theorem bandToInterior_isEmbedding (lo hi : I) : IsEmbedding (bandToInterior lo hi) :=
  IsEmbedding.subtypeVal.of_comp_iff.mp IsEmbedding.subtypeVal

variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e) (lo hi : I)

/-- The middle band with its actual subspace topology. -/
abbrev BandSpace := {d : D // lo < height f g sq d ∧ height f g sq d < hi}

/-- The cylinder parametrization restricted to `A` times the band, with codomain the
corresponding height-band subspace. -/
def bandMap : C(A × Band lo hi, BandSpace f g sq lo hi) where
  toFun z := ⟨l (z.1, ULift.up z.2.1), by rw [height_cylinder]; exact z.2.2⟩
  continuous_toFun := by fun_prop

/-- Any open height band in the double cylinder is the literal product
of the attaching space with that same open interval. -/
def bandHomeomorph : A × Band lo hi ≃ₜ BandSpace f g sq lo hi := by
  have hcomp : IsEmbedding (fun z : A × Band lo hi ↦ l (z.1, ULift.up z.2.1)) :=
    (interior_isOpenEmbedding f g sq).isEmbedding.comp
      ((Homeomorph.refl A).isEmbedding.prodMap (bandToInterior_isEmbedding lo hi))
  have hm : IsEmbedding (bandMap f g sq lo hi) := IsEmbedding.subtypeVal.of_comp_iff.mp hcomp
  apply hm.toHomeomorphOfSurjective
  intro d
  obtain ⟨z, hz⟩ := interior_surjective f g sq d.1
    ⟨lt_of_le_of_lt lo.2.1 d.2.1, lt_of_lt_of_le d.2.2 hi.2.2⟩
  have ht : lo < z.2.1 ∧ z.2.1 < hi := by
    have hh : height f g sq d.1 = z.2.1 := by rw [← hz, height_cylinder]
    simpa only [hh] using d.2
  exact ⟨(z.1, ⟨z.2.1, ht⟩), Subtype.ext hz⟩

@[simp] theorem bandHomeomorph_apply (z : A × Band lo hi) :
    (bandHomeomorph f g sq lo hi z).1 = l (z.1, ULift.up z.2.1) := rfl

/-- The same band expressed as the right-open restriction of the left collar. -/
def leftBandHomeomorph : A × Band lo hi ≃ₜ
    {d : LeftCollar f g sq hi // lo < height f g sq d.1} :=
  (bandHomeomorph f g sq lo hi).trans {
    toFun := fun d ↦ ⟨⟨d.1, d.2.2⟩, d.2.1⟩
    invFun := fun d ↦ ⟨d.1.1, d.2, d.1.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-- The band expressed as the left-open restriction of the right collar. -/
def rightBandHomeomorph : A × Band lo hi ≃ₜ
    {d : RightCollar f g sq lo // height f g sq d.1 < hi} :=
  (bandHomeomorph f g sq lo hi).trans {
    toFun := fun d ↦ ⟨⟨d.1, d.2.1⟩, d.2.2⟩
    invFun := fun d ↦ ⟨d.1.1, d.1.2, d.2⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

variable {E : TopCat.{u}}

/-- The genuine left collar pullback restricted to the overlap is exactly
the pullback over the left attaching map, times the open interval band. -/
def leftPullbackBandHomeomorph (hhi : 0 < hi) (p : E ⟶ B) :
    {z : A × E // p z.2 = f z.1} × Band lo hi ≃ₜ
      {z : RetractionPullback.Space (leftCollarStrongDeformationRetract f g sq hi hhi) p //
        lo < height f g sq z.1.1.1} := by
  let r := (leftCollarProjection f g sq hi hhi).hom
  let S : Set (LeftCollar f g sq hi) := {d | lo < height f g sq d.1}
  let e := leftBandHomeomorph f g sq lo hi
  let r' : C(S, B) := ⟨fun z ↦ r z.1, by fun_prop⟩
  let h := HomotopyPullback.strictProductChartHomeomorph p.hom f.hom r' e
    (fun (a : A) (t : Band lo hi) ↦ leftCollarProjection_apply_cylinder f g sq hi hhi a
      (ULift.up t.1)
      t.2.2)
  exact h.trans (HomotopyPullback.strictRestrictionHomeomorph p.hom r S).symm

/-- The analogous exact product chart for the genuine right collar pullback. -/
def rightPullbackBandHomeomorph (hlo : lo < 1) (p : E ⟶ C) :
    {z : A × E // p z.2 = g z.1} × Band lo hi ≃ₜ
      {z : RetractionPullback.Space (rightCollarStrongDeformationRetract f g sq lo hlo) p //
        height f g sq z.1.1.1 < hi} := by
  let r := (rightCollarProjection f g sq lo hlo).hom
  let S : Set (RightCollar f g sq lo) := {d | height f g sq d.1 < hi}
  let e := rightBandHomeomorph f g sq lo hi
  let r' : C(S, C) := ⟨fun z ↦ r z.1, by fun_prop⟩
  let h := HomotopyPullback.strictProductChartHomeomorph p.hom g.hom r' e
    (fun (a : A) (t : Band lo hi) ↦ rightCollarProjection_apply_cylinder f g sq lo hlo a
      (ULift.up t.1)
      t.2.1)
  exact h.trans (HomotopyPullback.strictRestrictionHomeomorph p.hom r S).symm

end TopCat.DoubleCylinder
