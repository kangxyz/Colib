/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.MappingCylinder.TargetCollar
public import Colib.Topology.Pushout.Open.Restriction

/-!
# The actual product source collar of a mapping cylinder

The open source collar is the literal product of the original attaching
space and a half-open interval. Its genuine source-end SDR preserves every
base map induced from the cylinder collapse. No weakness, lifting, or
homotopy-inverse hypothesis on the attaching map is used.


Implementation provenance:
`Quillen/Topology/MappingCylinder/SourceCollar.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
namespace TopCat.MappingCylinder.SourceCollar

/-- An open pushout restriction with empty opposite corner has precisely
its original left corner topology.

For an open subset of a pushout disjoint from the right-hand image, its left preimage is
homeomorphic to the subset via the left pushout map. -/
def leftOnlyHomeomorph {A B C D : TopCat.{u}}
    {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
    (sq : IsPushout i f g j) (U : Set D) (hU : IsOpen U) (hj : ∀ x, j x ∉ U) :
    OpenPushout.left (g := g) U ≃ₜ U := by
  let empty (x : OpenPushout.right (j := j) U) : False := hj x.val x.property
  let e : OpenPushout.right (j := j) U ⟶ OpenPushout.left (g := g) U :=
    TopCat.ofHom ⟨fun x ↦ False.elim (empty x),
      continuous_iff_continuousAt.mpr (fun x ↦ False.elim (empty x))⟩
  let R := OpenPushout.desc sq U (𝟙 _) e (by
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim (empty (OpenPushout.rightLeg sq U x))) hU
  have hl : OpenPushout.leftInclusion (g := g) U ≫ R = 𝟙 _ := OpenPushout.left_desc _ _ _ _ _ _
  have hr : R ≫ OpenPushout.leftInclusion (g := g) U = 𝟙 _ := by
    apply OpenPushout.hom_ext sq U
    · rw [← Category.assoc, hl, Category.id_comp, Category.comp_id]
    · apply ConcreteCategory.hom_ext
      intro x
      exact False.elim (empty x)
  exact TopCat.homeoOfIso {
    hom := OpenPushout.leftInclusion (g := g) U
    inv := R
    hom_inv_id := hl
    inv_hom_id := hr }

variable {A B M T : TopCat.{u}} {f : A ⟶ B}
  {l : A ⊗ TopCat.I ⟶ M} {c : B ⟶ M}
  (sq : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f l c) (cut : I)

/-- The same original cylinder height is used by source and target collars. -/
def collarSet : Set M := {x | TopCat.MappingCylinder.TargetCollar.height sq x < cut}

theorem collar_isOpen : IsOpen (collarSet sq cut) :=
  isOpen_lt (TopCat.MappingCylinder.TargetCollar.height sq).continuous continuous_const

/-- The mapping-cylinder subspace whose height is strictly less than `cut`. -/
abbrev Collar : TopCat.{u} := TopCat.of (collarSet sq cut)
/-- The initial interval of unit-interval parameters strictly less than `cut`. -/
abbrev Interval := {t : I // t < cut}

/-- The subspace inclusion of the source collar into the original mapping cylinder. -/
def inclusion : Collar sq cut ⟶ M := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem preimage_cylinder :
    l ⁻¹' collarSet sq cut = {z : A × TopCat.I | z.2.down < cut} := by
  ext z
  exact Iff.of_eq (congrArg (fun t ↦ t < cut)
    (TopCat.MappingCylinder.TargetCollar.height_cylinder sq z))

@[simp] theorem preimage_target : c ⁻¹' collarSet sq cut = ∅ := by
  ext b
  change TopCat.MappingCylinder.TargetCollar.height sq (c b) < cut ↔ False
  rw [TopCat.MappingCylinder.TargetCollar.height_target]
  exact iff_false_intro (not_lt.mpr cut.2.2)

/-- The open cylinder piece is the exact original half-open product. -/
def cylinderHomeomorph : A × Interval cut ≃ₜ OpenPushout.left (g := l) (collarSet sq cut) where
  toFun z := ⟨(z.1, ULift.up z.2.1), by
    change TopCat.MappingCylinder.TargetCollar.height sq (l (z.1, ULift.up z.2.1)) < cut
    rw [TopCat.MappingCylinder.TargetCollar.height_cylinder]
    exact z.2.2⟩
  invFun z := (z.1.1, ⟨z.1.2.down, by
    have h := z.2
    change TopCat.MappingCylinder.TargetCollar.height sq (l z.1) < cut at h
    rw [TopCat.MappingCylinder.TargetCollar.height_cylinder] at h
    exact h⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    change Continuous (fun z : {z : A × TopCat.I // l z ∈ collarSet sq cut} ↦
      (z.1.1, (⟨z.1.2.down, _⟩ : Interval cut)))
    fun_prop

/-- The actual source collar is a genuine product, not a quotient replacement. -/
def collarHomeomorph : A × Interval cut ≃ₜ Collar sq cut :=
  (cylinderHomeomorph sq cut).trans
    (leftOnlyHomeomorph sq (collarSet sq cut) (collar_isOpen sq cut) (fun b ↦ by
      change ¬ TopCat.MappingCylinder.TargetCollar.height sq (c b) < cut
      rw [TopCat.MappingCylinder.TargetCollar.height_target]
      exact not_lt.mpr cut.2.2))

@[simp] theorem collarHomeomorph_val (z : A × Interval cut) :
    (collarHomeomorph sq cut z).val = l (z.1, ULift.up z.2.1) := rfl

/-- The original source-end inclusion, packed only in the collar subtype. -/
def source (hcut : 0 < cut) : A ⟶ Collar sq cut := TopCat.ofHom
  ⟨fun a ↦ ⟨(TopCat.ι₀ ≫ l) a, by
    change TopCat.MappingCylinder.TargetCollar.height sq ((TopCat.ι₀ ≫ l) a) < cut
    rw [TopCat.MappingCylinder.TargetCollar.height_start]
    exact hcut⟩, by fun_prop⟩

@[simp] theorem source_val (hcut : 0 < cut) (a : A) :
    (source sq cut hcut a).val = (TopCat.ι₀ ≫ l) a := rfl

@[reassoc (attr := simp)] theorem source_inclusion (hcut : 0 < cut) :
    source sq cut hcut ≫ inclusion sq cut = TopCat.ι₀ ≫ l := rfl

/-- Every source endpoint lies in the positive source collar. -/
@[simp] theorem preimage_source_coe (hcut : 0 < cut) :
    (l.hom ∘ (TopCat.ι₀ : A ⟶ A ⊗ TopCat.I).hom) ⁻¹' collarSet sq cut = Set.univ := by
  ext a
  change TopCat.MappingCylinder.TargetCollar.height sq ((TopCat.ι₀ ≫ l) a) < cut ↔ True
  rw [TopCat.MappingCylinder.TargetCollar.height_start]
  exact iff_true_intro hcut

@[simp] theorem collarHomeomorph_source (hcut : 0 < cut) (a : A) :
    collarHomeomorph sq cut (a, ⟨0, hcut⟩) = source sq cut hcut a := rfl

@[simp] theorem collarHomeomorph_symm_source (hcut : 0 < cut) (a : A) :
    (collarHomeomorph sq cut).symm (source sq cut hcut a) = (a, ⟨0, hcut⟩) :=
  (collarHomeomorph sq cut).symm_apply_apply (a, ⟨0, hcut⟩)

/-- Contract the actual half-open time coordinate to zero, keeping the
original attaching-space point fixed at every time. -/
def strongDeformationRetract (hcut : 0 < cut) :
    TopCat.CylinderStrongDeformationRetract (source sq cut hcut) where
  r := TopCat.ofHom ⟨fun x ↦ ((collarHomeomorph sq cut).symm x).1, by fun_prop⟩
  retract := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg Prod.fst (collarHomeomorph_symm_source sq cut hcut a)
  H := TopCat.ofHom ⟨fun z ↦ collarHomeomorph sq cut
    (((collarHomeomorph sq cut).symm z.1).1,
      ⟨z.2.down * ((collarHomeomorph sq cut).symm z.1).2.1,
        lt_of_le_of_lt unitInterval.mul_le_right ((collarHomeomorph sq cut).symm z.1).2.2⟩),
    by
      apply (collarHomeomorph sq cut).continuous.comp
      apply Continuous.prodMk
      · exact ((collarHomeomorph sq cut).symm.continuous.comp continuous_fst).fst
      · apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        change Continuous (fun z : Collar sq cut × TopCat.I ↦
          (z.2.down : ℝ) * (((collarHomeomorph sq cut).symm z.1).2.1 : ℝ))
        exact ((continuous_subtype_val.comp continuous_uliftDown).comp continuous_snd).mul
          (continuous_subtype_val.comp (continuous_subtype_val.comp
            ((collarHomeomorph sq cut).symm.continuous.comp continuous_fst).snd))⟩
  H₀ := by
    apply ConcreteCategory.hom_ext
    intro x
    change collarHomeomorph sq cut
      (((collarHomeomorph sq cut).symm x).1, ⟨0 * _, _⟩) =
        source sq cut hcut ((collarHomeomorph sq cut).symm x).1
    rw [← collarHomeomorph_source]
    congr 1
    exact Prod.ext rfl (Subtype.ext (zero_mul _))
  H₁ := by
    apply ConcreteCategory.hom_ext
    intro x
    change collarHomeomorph sq cut
      (((collarHomeomorph sq cut).symm x).1, ⟨1 * _, _⟩) = x
    refine Eq.trans ?_ ((collarHomeomorph sq cut).apply_symm_apply x)
    apply congrArg (collarHomeomorph sq cut)
    exact Prod.ext rfl (Subtype.ext (one_mul _))
  fixed := by
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    change collarHomeomorph sq cut
      (((collarHomeomorph sq cut).symm (source sq cut hcut a)).1,
        ⟨t.down * ((collarHomeomorph sq cut).symm (source sq cut hcut a)).2.1, _⟩) =
      source sq cut hcut a
    apply (Eq.trans · (collarHomeomorph_source sq cut hcut a))
    apply congrArg (collarHomeomorph sq cut)
    apply Prod.ext
    · change ((collarHomeomorph sq cut).symm (source sq cut hcut a)).1 = a
      exact congrArg (fun z : A × Interval cut ↦ z.1) (collarHomeomorph_symm_source sq cut hcut a)
    · apply Subtype.ext
      change t.down * ((collarHomeomorph sq cut).symm (source sq cut hcut a)).2.1 = 0
      rw [collarHomeomorph_symm_source]
      exact mul_zero _

@[simp] theorem retraction_apply (hcut : 0 < cut) (x : Collar sq cut) :
    (strongDeformationRetract sq cut hcut).r x = ((collarHomeomorph sq cut).symm x).1 := rfl

/-- The collar's original collapsed base depends only on its attaching point. -/
theorem projection_apply (base : B ⟶ T) (x : Collar sq cut) :
    (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base) x.val =
      (f ≫ base) ((collarHomeomorph sq cut).symm x).1 := by
  have hx := congrArg Subtype.val ((collarHomeomorph sq cut).apply_symm_apply x)
  rw [collarHomeomorph_val] at hx
  rw [← hx]
  exact ConcreteCategory.congr_hom (TopCat.MappingCylinder.mappingCylinderProjection_cylinder_assoc
    sq base) _

/-- The whole genuine source-collar deformation is over the original base. -/
theorem deformation_over (hcut : 0 < cut) (base : B ⟶ T) :
    (strongDeformationRetract sq cut hcut).H ≫ inclusion sq cut ≫
        TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base =
      fst (Collar sq cut) TopCat.I ≫ inclusion sq cut ≫
        TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base := by
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  change (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base)
    (collarHomeomorph sq cut
      (((collarHomeomorph sq cut).symm x).1,
        ⟨t.down * ((collarHomeomorph sq cut).symm x).2.1, _⟩)).val =
    (TopCat.MappingCylinder.mappingCylinderProjection sq ≫ base) x.val
  rw [collarHomeomorph_val]
  exact (ConcreteCategory.congr_hom
    (TopCat.MappingCylinder.mappingCylinderProjection_cylinder_assoc sq base) _).trans
      (projection_apply sq cut
      base x).symm

end TopCat.MappingCylinder.SourceCollar
