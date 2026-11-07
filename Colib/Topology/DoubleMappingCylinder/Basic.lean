/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Homotopy.IntervalEndpoints
public import Colib.Topology.Category.TopCat.PushoutInteriors

/-!
# Actual double-cylinder height and interior charts

The open interior is an actual product chart. All statements concern the
ordinary TopCat pushout, and use no arbitrary quotient base-change rule.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/Basic.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and proofs
with native namespace and import ownership. -/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Topology
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat

/-- Both endpoint inclusions together form a closed embedding. -/
theorem isClosedEmbedding_intervalEndpoints (A : TopCat.{u}) :
    IsClosedEmbedding (TopCat.intervalEndpoints A) := by
  change IsClosedEmbedding (Sum.elim (fun a : A ↦ (a, ULift.up (0 : I)))
    (fun a : A ↦ (a, ULift.up (1 : I))))
  have h (t : ULift.{u} I) : IsClosedEmbedding (fun a : A ↦ (a, t)) := by
    refine ⟨isEmbedding_prodMkLeft t, ?_⟩
    have he : Set.range (fun a : A ↦ (a, t)) = Prod.snd ⁻¹' {t} := by
      ext ⟨a, s⟩
      change (∃ x, (x, t) = (a, s)) ↔ s = t
      constructor
      · rintro ⟨x, hx⟩
        exact (congrArg Prod.snd hx).symm
      · intro hs
        exact ⟨a, Prod.ext rfl hs.symm⟩
    rw [he]
    exact isClosed_singleton.preimage continuous_snd
  apply (h 0).sumElim (h 1)
  rintro (a | a) (b | b) hab
  · exact congrArg Sum.inl (congrArg Prod.fst hab)
  · have hh := congrArg (fun z : A × ULift.{u} I ↦ z.2.down) hab
    exact False.elim (zero_ne_one hh)
  · have hh := congrArg (fun z : A × ULift.{u} I ↦ z.2.down) hab
    exact False.elim (zero_ne_one hh.symm)
  · exact congrArg Sum.inr (congrArg Prod.fst hab)

namespace DoubleCylinder
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- The attachment map of the two ends. -/
def endMap : TopCat.of (A ⊕ A) ⟶ TopCat.of (B ⊕ C) :=
  TopCat.ofHom ⟨Sum.elim (fun a ↦ Sum.inl (f a)) (fun a ↦ Sum.inr (g a)),
    continuous_sum_dom.mpr ⟨by fun_prop, by fun_prop⟩⟩

variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)

/-- The interval projection on the central cylinder of the double mapping cylinder. -/
def heightCylinderMap : A ⊗ TopCat.I ⟶ TopCat.I := snd A TopCat.I

/-- The endpoint height map on `B ⊕ C`, equal to zero on `B` and one on `C`. -/
def heightEndMap : TopCat.of (B ⊕ C) ⟶ TopCat.I := TopCat.ofHom
  ⟨Sum.elim (fun _ ↦ 0) (fun _ ↦ 1), continuous_sum_dom.mpr ⟨continuous_const, continuous_const⟩⟩

theorem height_square : TopCat.intervalEndpoints A ≫ heightCylinderMap =
    endMap f g ≫ heightEndMap := by
  ext a
  cases a <;> rfl

/-- Height on the actual double mapping cylinder. -/
def height : C(D, I) :=
  ⟨fun d ↦ (sq.desc heightCylinderMap heightEndMap (height_square f g) d).down, by fun_prop⟩

@[simp] theorem height_cylinder (a : A) (t : TopCat.I) : height f g sq (l (a, t)) = t.down :=
  congrArg (fun z : TopCat.I ↦ z.down) (ConcreteCategory.congr_hom
    (sq.inl_desc heightCylinderMap heightEndMap (height_square f g)) (a, t))
@[simp] theorem height_left (b : B) : height f g sq (e (Sum.inl b)) = 0 :=
  congrArg (fun z : TopCat.I ↦ z.down) (ConcreteCategory.congr_hom
    (sq.inr_desc heightCylinderMap heightEndMap (height_square f g)) (Sum.inl b))
@[simp] theorem height_right (c : C) : height f g sq (e (Sum.inr c)) = 1 :=
  congrArg (fun z : TopCat.I ↦ z.down) (ConcreteCategory.congr_hom
    (sq.inr_desc heightCylinderMap heightEndMap (height_square f g)) (Sum.inr c))

/-- The open unit interval, used for the product interior chart. -/
abbrev OpenInterval := {t : I // 0 < t ∧ t < 1}

/-- The complement of the cylinder endpoint pair is literally the open
interval product, with its ordinary subspace topology. -/
def cylinderInteriorHomeomorph (A : TopCat.{u}) : A × OpenInterval ≃ₜ
    {z : A × ULift.{u} I // z ∉ Set.range (TopCat.intervalEndpoints A)} where
  toFun z := ⟨(z.1, ULift.up z.2.1), by
    rintro ⟨a | a, ha⟩
    · have ht : (0 : I) = z.2.1 := congrArg (fun w : A × TopCat.I ↦ w.2.down) ha
      exact (ne_of_gt z.2.2.1) ht.symm
    · have ht : (1 : I) = z.2.1 := congrArg (fun w : A × TopCat.I ↦ w.2.down) ha
      exact (ne_of_lt z.2.2.2) ht.symm⟩
  invFun z := (z.1.1, ⟨z.1.2.down, by
    constructor
    · apply lt_of_le_of_ne (z.1.2.down).2.1
      intro hz
      apply z.2
      refine ⟨Sum.inl z.1.1, ?_⟩
      change (z.1.1, ULift.up (0 : I)) = z.1
      have ht : (0 : I) = z.1.2.down := Subtype.ext hz
      rw [ht]
    · apply lt_of_le_of_ne (z.1.2.down).2.2
      intro hz
      apply z.2
      refine ⟨Sum.inr z.1.1, ?_⟩
      change (z.1.1, ULift.up (1 : I)) = z.1
      have ht : (1 : I) = z.1.2.down := Subtype.ext hz.symm
      rw [ht]⟩)
  left_inv _ := rfl
  right_inv z := by apply Subtype.ext; rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

include sq in
/-- The central open cylinder embeds openly into the actual pushout. -/
theorem interior_isOpenEmbedding :
    IsOpenEmbedding (fun z : A × OpenInterval ↦ l (z.1, ULift.up z.2.1)) :=
  (isOpenEmbedding_pushout_cell_compl sq (isClosedEmbedding_intervalEndpoints A)).comp
    (cylinderInteriorHomeomorph A).isOpenEmbedding

/-- Interior height points have unique cylinder coordinates. -/
theorem interior_surjective (d : D) (hd : 0 < height f g sq d ∧ height f g sq d < 1) :
    ∃ z : A × OpenInterval, l (z.1, ULift.up z.2.1) = d := by
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) d with ⟨⟨a, t⟩, ht⟩ | ⟨b | c, hbc⟩
  · change l (a, t) = d at ht
    have hh : height f g sq d = t.down := by rw [← ht, height_cylinder]
    refine ⟨(a, ⟨t.down, hh ▸ hd⟩), ?_⟩
    cases t
    exact ht
  · change e (Sum.inl b) = d at hbc
    have hh : height f g sq d = 0 := by rw [← hbc, height_left]
    exact False.elim ((ne_of_gt hd.1) hh)
  · change e (Sum.inr c) = d at hbc
    have hh : height f g sq d = 1 := by rw [← hbc, height_right]
    exact False.elim ((ne_of_lt hd.2) hh)

/-- The interior product chart with its exact height-restricted codomain. -/
def interiorMap : C(A × OpenInterval, {d : D // 0 < height f g sq d ∧ height f g sq d < 1}) where
  toFun z := ⟨l (z.1, ULift.up z.2.1), by
    rw [height_cylinder]
    exact z.2.2⟩
  continuous_toFun := by fun_prop

/-- The actual open interior is homeomorphic to the product with `(0,1)`. -/
def interiorHomeomorph : A × OpenInterval ≃ₜ
    {d : D // 0 < height f g sq d ∧ height f g sq d < 1} := by
  have h : IsEmbedding (interiorMap f g sq) :=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp (interior_isOpenEmbedding f g sq).isEmbedding
  apply h.toHomeomorphOfSurjective
  intro d
  obtain ⟨z, hz⟩ := interior_surjective f g sq d.1 d.2
  exact ⟨z, Subtype.ext hz⟩

@[simp] theorem interiorHomeomorph_apply (z : A × OpenInterval) :
    (interiorHomeomorph f g sq z).1 = l (z.1, ULift.up z.2.1) := rfl

/-- The double mapping cylinder of the span `B ← A → C`, defined by its endpoint pushout. -/
abbrev Cylinder {A B C : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C) : TopCat.{u} :=
  pushout (TopCat.intervalEndpoints A) (DoubleCylinder.endMap f g)
/-- The canonical map of `A × I` into the double mapping cylinder of `f` and `g`. -/
abbrev cylinderLine {A B C : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C) : A ⊗ TopCat.I ⟶ Cylinder f g :=
  pushout.inl _ _
/-- The canonical map of `B ⊕ C` into the double mapping cylinder of `f` and `g`. -/
abbrev cylinderEnd {A B C : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C) : TopCat.of (B ⊕ C) ⟶ Cylinder f
    g :=
  pushout.inr _ _
theorem cylinderSquare {A B C : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C) :
    IsPushout (TopCat.intervalEndpoints A) (DoubleCylinder.endMap f g) (cylinderLine f g)
      (cylinderEnd f g) :=
  IsPushout.of_hasPushout _ _


end DoubleCylinder
end TopCat
