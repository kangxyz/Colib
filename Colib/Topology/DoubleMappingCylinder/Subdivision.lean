/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.Basic
public import Colib.Topology.MappingCylinder.PushoutCollapse

/-!
# Subdividing an actual double mapping cylinder

The double mapping cylinder of a span is canonically homeomorphic to the
pushout of its two mapping cylinders along their source ends. The comparison
uses the reversed first cylinder and the forward second cylinder, each at
twice speed, and respects both target ends exactly.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/Subdivision.lean` at commit
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
namespace TopCat.DoubleCylinder.Subdivision

/-- The first cylinder runs backwards over the first half of the interval. -/
def leftHalf (t : I) : I := ⟨(1 - (t : ℝ)) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
/-- The second cylinder runs forwards over the second half of the interval. -/
def rightHalf (t : I) : I := ⟨(1 + (t : ℝ)) / 2, by constructor <;> linarith [t.2.1, t.2.2]⟩
@[fun_prop] theorem continuous_leftHalf : Continuous leftHalf := by
  unfold leftHalf; fun_prop
@[fun_prop] theorem continuous_rightHalf : Continuous rightHalf := by
  unfold rightHalf; fun_prop
@[simp] theorem leftHalf_one : leftHalf 1 = 0 := by apply Subtype.ext; norm_num [leftHalf]
@[simp] theorem rightHalf_one : rightHalf 1 = 1 := by apply Subtype.ext; norm_num [rightHalf]
theorem half_zero : leftHalf 0 = rightHalf 0 := by apply Subtype.ext; norm_num [leftHalf, rightHalf]

variable {A B C D M N Z : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sqD : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
  {lM : A ⊗ TopCat.I ⟶ M} {cM : B ⟶ M}
  {lN : A ⊗ TopCat.I ⟶ N} {cN : C ⟶ N}
  (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) f lM cM)
  (sqN : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) g lN cN)
  {m : M ⟶ Z} {n : N ⟶ Z}
  (sq : IsPushout (TopCat.ι₀ ≫ lM) (TopCat.ι₀ ≫ lN) m n)

/-- Travel from the left target to the common source. -/
def leftPath : TopCat.Homotopy (f ≫ cM ≫ m) ((TopCat.ι₀ ≫ lM) ≫ m) where
  toFun p := m (lM (p.2, ULift.up (unitInterval.symm p.1)))
  continuous_toFun := by fun_prop
  map_zero_left a := by
    change m (lM (a, ULift.up (unitInterval.symm 0))) = m (cM (f a))
    rw [unitInterval.symm_zero]
    exact congrArg m (ConcreteCategory.congr_hom sqM.w a)
  map_one_left a := by simp; rfl

/-- Travel from the common source to the right target. -/
def rightPath : TopCat.Homotopy ((TopCat.ι₀ ≫ lM) ≫ m) (g ≫ cN ≫ n) where
  toFun p := n (lN (p.2, ULift.up p.1))
  continuous_toFun := by fun_prop
  map_zero_left a := (ConcreteCategory.congr_hom sq.w a).symm
  map_one_left a := congrArg n (ConcreteCategory.congr_hom sqN.w a)

/-- The concatenated route through the two mapping cylinders. -/
def path : TopCat.Homotopy (f ≫ cM ≫ m) (g ≫ cN ≫ n) :=
  (leftPath sqM).trans (rightPath sqN sq)

/-- Map the original cylinder into the glued pair of mapping cylinders along the path that
traverses the reversed left half and the forward right half. -/
def cylinderMap : A ⊗ TopCat.I ⟶ Z := TopCat.ofHom
  ⟨fun p ↦ path sqM sqN sq (p.2.down, p.1), by fun_prop⟩

/-- Map `B ⊕ C` into the glued pair of mapping cylinders through their respective target
inclusions. -/
def endsMap : TopCat.of (B ⊕ C) ⟶ Z := TopCat.ofHom
  ⟨Sum.elim (fun b ↦ m (cM b)) (fun c ↦ n (cN c)),
    continuous_sum_dom.mpr ⟨by fun_prop, by fun_prop⟩⟩

theorem forward_square : TopCat.intervalEndpoints A ≫ cylinderMap sqM sqN sq =
    endMap f g ≫ endsMap (cM := cM) (cN := cN) (m := m) (n := n) := by
  ext a
  cases a with
  | inl a => exact (path sqM sqN sq).map_zero_left a
  | inr a => exact (path sqM sqN sq).map_one_left a

/-- The canonical subdivision map from the usual double cylinder. -/
def forward : D ⟶ Z := sqD.desc (cylinderMap sqM sqN sq) endsMap
  (forward_square sqM sqN sq)

@[reassoc (attr := simp)] theorem forward_cylinder :
    l ≫ forward sqD sqM sqN sq = cylinderMap sqM sqN sq := sqD.inl_desc _ _ _
@[reassoc (attr := simp)] theorem forward_ends :
    e ≫ forward sqD sqM sqN sq = endsMap (cM := cM) (cN := cN) (m := m) (n := n) := sqD.inr_desc
      _ _ _

@[simp] theorem forward_left (b : B) :
    forward sqD sqM sqN sq (e (Sum.inl b)) = m (cM b) :=
  ConcreteCategory.congr_hom (forward_ends sqD sqM sqN sq) (Sum.inl b)
@[simp] theorem forward_right (c : C) :
    forward sqD sqM sqN sq (e (Sum.inr c)) = n (cN c) :=
  ConcreteCategory.congr_hom (forward_ends sqD sqM sqN sq) (Sum.inr c)

/-- Reassemble the first half of the interval. -/
def leftCylinderMap : A ⊗ TopCat.I ⟶ D := TopCat.ofHom
  ⟨fun p ↦ l (p.1, ULift.up (leftHalf p.2.down)), by fun_prop⟩
/-- Reassemble the second half of the interval. -/
def rightCylinderMap : A ⊗ TopCat.I ⟶ D := TopCat.ofHom
  ⟨fun p ↦ l (p.1, ULift.up (rightHalf p.2.down)), by fun_prop⟩

/-- The left endpoint map from `B` into the original double cylinder. -/
def leftEnd : B ⟶ D := TopCat.ofHom ⟨fun b ↦ e (Sum.inl b), by fun_prop⟩
/-- The right endpoint map from `C` into the original double cylinder. -/
def rightEnd : C ⟶ D := TopCat.ofHom ⟨fun c ↦ e (Sum.inr c), by fun_prop⟩

/-- The map from the left mapping cylinder to the original double cylinder induced by its
left-half parametrization and left endpoint. -/
def inverseLeft : M ⟶ D := sqM.desc (leftCylinderMap (l := l)) (leftEnd (e := e)) (by
  ext a
  change l (a, ULift.up (leftHalf 1)) = e (Sum.inl (f a))
  rw [leftHalf_one]
  exact ConcreteCategory.congr_hom sqD.w (Sum.inl a))

/-- The map from the right mapping cylinder to the original double cylinder induced by its
right-half parametrization and right endpoint. -/
def inverseRight : N ⟶ D := sqN.desc (rightCylinderMap (l := l)) (rightEnd (e := e)) (by
  ext a
  change l (a, ULift.up (rightHalf 1)) = e (Sum.inr (g a))
  rw [rightHalf_one]
  exact ConcreteCategory.congr_hom sqD.w (Sum.inr a))

@[reassoc (attr := simp)] theorem inverseLeft_cylinder :
    lM ≫ inverseLeft sqD sqM = leftCylinderMap (l := l) := sqM.inl_desc _ _ _
@[reassoc (attr := simp)] theorem inverseLeft_end :
    cM ≫ inverseLeft sqD sqM = leftEnd (e := e) := sqM.inr_desc _ _ _
@[reassoc (attr := simp)] theorem inverseRight_cylinder :
    lN ≫ inverseRight sqD sqN = rightCylinderMap (l := l) := sqN.inl_desc _ _ _
@[reassoc (attr := simp)] theorem inverseRight_end :
    cN ≫ inverseRight sqD sqN = rightEnd (e := e) := sqN.inr_desc _ _ _

theorem inverse_square : (TopCat.ι₀ ≫ lM) ≫ inverseLeft sqD sqM =
    (TopCat.ι₀ ≫ lN) ≫ inverseRight sqD sqN := by
  simp only [Category.assoc, inverseLeft_cylinder, inverseRight_cylinder]
  ext a
  change l (a, ULift.up (leftHalf 0)) = l (a, ULift.up (rightHalf 0))
  rw [half_zero]

/-- The inverse map is obtained solely from the three actual pushouts. -/
def inverse : Z ⟶ D := sq.desc (inverseLeft sqD sqM) (inverseRight sqD sqN)
  (inverse_square sqD sqM sqN)

@[reassoc (attr := simp)] theorem inverse_left :
    m ≫ inverse sqD sqM sqN sq = inverseLeft sqD sqM := sq.inl_desc _ _ _
@[reassoc (attr := simp)] theorem inverse_right :
    n ≫ inverse sqD sqM sqN sq = inverseRight sqD sqN := sq.inr_desc _ _ _

@[simp] theorem inverse_left_cylinder (a : A) (t : I) :
    inverse sqD sqM sqN sq (m (lM (a, ULift.up t))) = l (a, ULift.up (leftHalf t)) :=
  ConcreteCategory.congr_hom (by simp : lM ≫ m ≫ inverse sqD sqM sqN sq = leftCylinderMap)
    (a, ULift.up t)
@[simp] theorem inverse_right_cylinder (a : A) (t : I) :
    inverse sqD sqM sqN sq (n (lN (a, ULift.up t))) = l (a, ULift.up (rightHalf t)) :=
  ConcreteCategory.congr_hom (by simp : lN ≫ n ≫ inverse sqD sqM sqN sq = rightCylinderMap)
    (a, ULift.up t)
@[simp] theorem inverse_left_end (b : B) :
    inverse sqD sqM sqN sq (m (cM b)) = e (Sum.inl b) :=
  ConcreteCategory.congr_hom (by simp : cM ≫ m ≫ inverse sqD sqM sqN sq = leftEnd) b
@[simp] theorem inverse_right_end (c : C) :
    inverse sqD sqM sqN sq (n (cN c)) = e (Sum.inr c) :=
  ConcreteCategory.congr_hom (by simp : cN ≫ n ≫ inverse sqD sqM sqN sq = rightEnd) c

/-- The first half of the concatenation recovers the first mapping cylinder. -/
@[simp] theorem cylinderMap_leftHalf (a : A) (t : I) :
    cylinderMap sqM sqN sq (a, ULift.up (leftHalf t)) = m (lM (a, ULift.up t)) := by
  change path sqM sqN sq (leftHalf t, a) = _
  rw [path, ContinuousMap.Homotopy.trans_apply]
  have h : (leftHalf t : ℝ) ≤ 1 / 2 := by
    change (1 - (t : ℝ)) / 2 ≤ 1 / 2
    linarith [t.2.1]
  rw [dite_eq_left h]
  change m (lM (a, ULift.up (unitInterval.symm _))) = _
  have ht : ∀ h, unitInterval.symm (⟨2 * (leftHalf t : ℝ), h⟩ : I) = t := by
    intro h
    apply Subtype.ext
    dsimp [unitInterval.symm, leftHalf]
    ring
  rw [ht]

/-- The second half recovers the second mapping cylinder, including the
common source where the two pieces are glued. -/
@[simp] theorem cylinderMap_rightHalf (a : A) (t : I) :
    cylinderMap sqM sqN sq (a, ULift.up (rightHalf t)) = n (lN (a, ULift.up t)) := by
  change path sqM sqN sq (rightHalf t, a) = _
  rw [path, ContinuousMap.Homotopy.trans_apply]
  split_ifs with h
  · have ht : t = 0 := by
      apply Subtype.ext
      change (t : ℝ) = 0
      change (1 + (t : ℝ)) / 2 ≤ 1 / 2 at h
      linarith [t.2.1]
    subst t
    change m (lM (a, ULift.up (unitInterval.symm _))) = n (lN (a, ULift.up 0))
    have hi : ∀ h, unitInterval.symm (⟨2 * (rightHalf 0 : ℝ), h⟩ : I) = 0 := by
      intro h
      apply Subtype.ext
      norm_num [unitInterval.symm, rightHalf]
    rw [hi]
    exact ConcreteCategory.congr_hom sq.w a
  · change n (lN (a, ULift.up _)) = _
    have ht : ∀ h, (⟨2 * (rightHalf t : ℝ) - 1, h⟩ : I) = t := by
      intro h
      apply Subtype.ext
      dsimp [rightHalf]
      ring
    rw [ht]

@[simp] theorem inverse_cylinderMap (a : A) (t : I) :
    inverse sqD sqM sqN sq (cylinderMap sqM sqN sq (a, ULift.up t)) =
      l (a, ULift.up t) := by
  change inverse sqD sqM sqN sq (path sqM sqN sq (t, a)) = _
  rw [path, ContinuousMap.Homotopy.trans_apply]
  split_ifs with h
  · change inverse sqD sqM sqN sq (m (lM (a, ULift.up (unitInterval.symm _)))) = _
    rw [inverse_left_cylinder]
    have ht : ∀ h, leftHalf (unitInterval.symm (⟨2 * (t : ℝ), h⟩ : I)) = t := by
      intro h
      apply Subtype.ext
      dsimp [leftHalf, unitInterval.symm]
      ring
    rw [ht]
  · change inverse sqD sqM sqN sq (n (lN (a, ULift.up _))) = _
    rw [inverse_right_cylinder]
    have ht : ∀ h, rightHalf (⟨2 * (t : ℝ) - 1, h⟩ : I) = t := by
      intro h
      apply Subtype.ext
      dsimp [rightHalf]
      ring
    rw [ht]

@[reassoc (attr := simp)] theorem forward_inverse :
    forward sqD sqM sqN sq ≫ inverse sqD sqM sqN sq = 𝟙 D := by
  apply sqD.hom_ext
  · rw [← Category.assoc, forward_cylinder]
    ext ⟨a, t⟩
    exact inverse_cylinderMap sqD sqM sqN sq a t.down
  · ext x
    rcases x with b | c
    · change inverse sqD sqM sqN sq (forward sqD sqM sqN sq (e (Sum.inl b))) = _
      rw [forward_left, inverse_left_end]
      rfl
    · change inverse sqD sqM sqN sq (forward sqD sqM sqN sq (e (Sum.inr c))) = _
      rw [forward_right, inverse_right_end]
      rfl

@[reassoc (attr := simp)] theorem inverse_forward :
    inverse sqD sqM sqN sq ≫ forward sqD sqM sqN sq = 𝟙 Z := by
  apply sq.hom_ext
  · apply sqM.hom_ext
    · simp only [inverse_left_assoc, inverseLeft_cylinder_assoc]
      ext ⟨a, t⟩
      change forward sqD sqM sqN sq (l (a, ULift.up (leftHalf t.down))) = m (lM (a, t))
      have he := ConcreteCategory.congr_hom (forward_cylinder sqD sqM sqN sq)
        (a, ULift.up (leftHalf t.down))
      exact he.trans (cylinderMap_leftHalf sqM sqN sq a t.down)
    · ext b
      change forward sqD sqM sqN sq (inverse sqD sqM sqN sq (m (cM b))) = m (cM b)
      rw [inverse_left_end, forward_left]
  · apply sqN.hom_ext
    · simp only [inverse_right_assoc, inverseRight_cylinder_assoc]
      ext ⟨a, t⟩
      change forward sqD sqM sqN sq (l (a, ULift.up (rightHalf t.down))) = n (lN (a, t))
      have he := ConcreteCategory.congr_hom (forward_cylinder sqD sqM sqN sq)
        (a, ULift.up (rightHalf t.down))
      exact he.trans (cylinderMap_rightHalf sqM sqN sq a t.down)
    · ext c
      change forward sqD sqM sqN sq (inverse sqD sqM sqN sq (n (cN c))) = n (cN c)
      rw [inverse_right_end, forward_right]

/-- The ordinary double mapping cylinder is genuinely homeomorphic to
its two-cylinder subdivision. -/
def homeomorph : D ≃ₜ Z where
  toFun := forward sqD sqM sqN sq
  invFun := inverse sqD sqM sqN sq
  left_inv d := ConcreteCategory.congr_hom (forward_inverse sqD sqM sqN sq) d
  right_inv z := ConcreteCategory.congr_hom (inverse_forward sqD sqM sqN sq) z
  continuous_toFun := (forward sqD sqM sqN sq).hom.continuous
  continuous_invFun := (inverse sqD sqM sqN sq).hom.continuous

@[simp] theorem homeomorph_left (b : B) :
    homeomorph sqD sqM sqN sq (e (Sum.inl b)) = m (cM b) := forward_left _ _ _ _ b
@[simp] theorem homeomorph_right (c : C) :
    homeomorph sqD sqM sqN sq (e (Sum.inr c)) = n (cN c) := forward_right _ _ _ _ c

/-- The same comparison as a categorical topological isomorphism. -/
def iso : D ≅ Z where
  hom := forward sqD sqM sqN sq
  inv := inverse sqD sqM sqN sq
  hom_inv_id := forward_inverse sqD sqM sqN sq
  inv_hom_id := inverse_forward sqD sqM sqN sq

/-- In particular subdivision is an actual homotopy equivalence. -/
def homotopyEquiv : ContinuousMap.HomotopyEquiv D Z :=
  (homeomorph sqD sqM sqN sq).toHomotopyEquiv

@[simp] theorem homotopyEquiv_toFun :
    (homotopyEquiv sqD sqM sqN sq).toFun = (forward sqD sqM sqN sq).hom := rfl
@[simp] theorem homotopyEquiv_invFun :
    (homotopyEquiv sqD sqM sqN sq).invFun = (inverse sqD sqM sqN sq).hom := rfl

/-- The inverse comparison respects any maps to a common base that are
constant on cylinder coordinates and agree at the two target ends. -/
theorem inverse_over {T : TopCat.{u}} (p : D ⟶ T) (q : Z ⟶ T) (a : A ⟶ T)
    (hl : l ≫ p = fst A TopCat.I ≫ a)
    (hM : lM ≫ m ≫ q = fst A TopCat.I ≫ a)
    (hN : lN ≫ n ≫ q = fst A TopCat.I ≫ a)
    (hB : cM ≫ m ≫ q = leftEnd (e := e) ≫ p)
    (hC : cN ≫ n ≫ q = rightEnd (e := e) ≫ p) :
    inverse sqD sqM sqN sq ≫ p = q := by
  apply sq.hom_ext
  · apply sqM.hom_ext
    · simp only [inverse_left_assoc, inverseLeft_cylinder_assoc]
      rw [hM]
      ext ⟨x, t⟩
      exact ConcreteCategory.congr_hom hl (x, ULift.up (leftHalf t.down))
    · simp only [inverse_left_assoc, inverseLeft_end_assoc]
      exact hB.symm
  · apply sqN.hom_ext
    · simp only [inverse_right_assoc, inverseRight_cylinder_assoc]
      rw [hN]
      ext ⟨x, t⟩
      exact ConcreteCategory.congr_hom hl (x, ULift.up (rightHalf t.down))
    · simp only [inverse_right_assoc, inverseRight_end_assoc]
      exact hC.symm

/-- The forward homeomorphism is strictly over a common base whenever the
cylinder and endpoint maps are. -/
theorem forward_over {T : TopCat.{u}} (p : D ⟶ T) (q : Z ⟶ T) (a : A ⟶ T)
    (hl : l ≫ p = fst A TopCat.I ≫ a)
    (hM : lM ≫ m ≫ q = fst A TopCat.I ≫ a)
    (hN : lN ≫ n ≫ q = fst A TopCat.I ≫ a)
    (hB : cM ≫ m ≫ q = leftEnd (e := e) ≫ p)
    (hC : cN ≫ n ≫ q = rightEnd (e := e) ≫ p) :
    forward sqD sqM sqN sq ≫ q = p := by
  rw [← inverse_over sqD sqM sqN sq p q a hl hM hN hB hC,
    ← Category.assoc, forward_inverse, Category.id_comp]

end TopCat.DoubleCylinder.Subdivision
