/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.Invariance

/-!
# The cofibrant double-cylinder collapse

An actual double mapping cylinder is an iterated pushout with the mapping
cylinder of the right leg. If the left leg has HEP, its canonical collapse
to the ordinary pushout is a homotopy equivalence. The collapse is strictly
natural, including its maps on the cylinder and the two endpoint spaces.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/Collapse.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and proofs
with native namespace and import ownership. -/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.DoubleCylinder

/-- The continuous map defined independently on the two summands. -/
def sumElim {B C X : TopCat.{u}} (b : B ⟶ X) (c : C ⟶ X) :
    TopCat.of (B ⊕ C) ⟶ X :=
  TopCat.ofHom ⟨Sum.elim b c, continuous_sum_dom.mpr ⟨b.hom.continuous, c.hom.continuous⟩⟩

@[simp] theorem sumElim_inl {B C X : TopCat.{u}} (b : B ⟶ X) (c : C ⟶ X) (x : B) :
    sumElim b c (Sum.inl x) = b x := rfl
@[simp] theorem sumElim_inr {B C X : TopCat.{u}} (b : B ⟶ X) (c : C ⟶ X) (x : C) :
    sumElim b c (Sum.inr x) = c x := rfl

variable {A B C D M P : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sqD : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)

/-- The left endpoint inclusion into the actual double cylinder. -/
def leftEnd (e : TopCat.of (B ⊕ C) ⟶ D) : B ⟶ D :=
  TopCat.ofHom ⟨fun b ↦ e (Sum.inl b), by fun_prop⟩
/-- The right endpoint inclusion into the actual double cylinder. -/
def rightEnd (e : TopCat.of (B ⊕ C) ⟶ D) : C ⟶ D :=
  TopCat.ofHom ⟨fun c ↦ e (Sum.inr c), by fun_prop⟩

include sqD

@[reassoc] theorem cylinder_zero : TopCat.ι₀ ≫ l = f ≫ leftEnd e := by
  ext a
  exact ConcreteCategory.congr_hom sqD.w (Sum.inl a)
@[reassoc] theorem cylinder_one : TopCat.ι₁ ≫ l = g ≫ rightEnd e := by
  ext a
  exact ConcreteCategory.congr_hom sqD.w (Sum.inr a)

variable {lM : A ⊗ TopCat.I ⟶ M} {cM : C ⟶ M}
  (sqM : IsPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) g lM cM)

/-- The right mapping cylinder maps into the double cylinder without rescaling. -/
def mappingCylinderMap : M ⟶ D := sqM.desc l (rightEnd e) (cylinder_one sqD)

@[reassoc (attr := simp)] theorem mappingCylinderMap_cylinder :
    lM ≫ mappingCylinderMap sqD sqM = l := sqM.inl_desc _ _ _
@[reassoc (attr := simp)] theorem mappingCylinderMap_target :
    cM ≫ mappingCylinderMap sqD sqM = rightEnd e := sqM.inr_desc _ _ _

theorem mappingCylinderPushout_square :
    f ≫ leftEnd e = (TopCat.ι₀ ≫ lM) ≫ mappingCylinderMap sqD sqM := by
  rw [Category.assoc, mappingCylinderMap_cylinder, cylinder_zero sqD]

/-- Descent on the right mapping cylinder and left endpoint. -/
def mappingCylinderPushoutDesc {X : TopCat.{u}} (b : B ⟶ X) (m : M ⟶ X)
    (h : f ≫ b = (TopCat.ι₀ ≫ lM) ≫ m) : D ⟶ X :=
  sqD.desc (lM ≫ m) (sumElim b (cM ≫ m)) (by
    ext a
    cases a with
    | inl a => exact (ConcreteCategory.congr_hom h a).symm
    | inr a => exact congrArg m (ConcreteCategory.congr_hom sqM.w a))

@[reassoc (attr := simp)] theorem mappingCylinderPushoutDesc_cylinder
    {X : TopCat.{u}} (b : B ⟶ X) (m : M ⟶ X)
    (h : f ≫ b = (TopCat.ι₀ ≫ lM) ≫ m) :
    l ≫ mappingCylinderPushoutDesc sqD sqM b m h = lM ≫ m := sqD.inl_desc _ _ _

@[reassoc (attr := simp)] theorem mappingCylinderPushoutDesc_ends
    {X : TopCat.{u}} (b : B ⟶ X) (m : M ⟶ X)
    (h : f ≫ b = (TopCat.ι₀ ≫ lM) ≫ m) :
    e ≫ mappingCylinderPushoutDesc sqD sqM b m h = sumElim b (cM ≫ m) := sqD.inr_desc _ _ _

@[reassoc (attr := simp)] theorem mappingCylinderPushoutDesc_left
    {X : TopCat.{u}} (b : B ⟶ X) (m : M ⟶ X)
    (h : f ≫ b = (TopCat.ι₀ ≫ lM) ≫ m) :
    leftEnd e ≫ mappingCylinderPushoutDesc sqD sqM b m h = b := by
  ext x
  exact ConcreteCategory.congr_hom (mappingCylinderPushoutDesc_ends sqD sqM b m h) (Sum.inl x)

@[reassoc (attr := simp)] theorem mappingCylinderPushoutDesc_right
    {X : TopCat.{u}} (b : B ⟶ X) (m : M ⟶ X)
    (h : f ≫ b = (TopCat.ι₀ ≫ lM) ≫ m) :
    rightEnd e ≫ mappingCylinderPushoutDesc sqD sqM b m h = cM ≫ m := by
  ext x
  exact ConcreteCategory.congr_hom (mappingCylinderPushoutDesc_ends sqD sqM b m h) (Sum.inr x)

/-- Reassociation of the actual double-cylinder universal property. -/
theorem mappingCylinderPushout :
    IsPushout f (TopCat.ι₀ ≫ lM) (leftEnd e) (mappingCylinderMap sqD sqM) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (mappingCylinderPushout_square sqD sqM))
  apply PushoutCocone.IsColimit.mk (mappingCylinderPushout_square sqD sqM)
    (fun s ↦ mappingCylinderPushoutDesc sqD sqM s.inl s.inr s.condition)
  · intro s
    exact mappingCylinderPushoutDesc_left sqD sqM _ _ _
  · intro s
    apply sqM.hom_ext <;> simp only [← Category.assoc, mappingCylinderMap_cylinder,
      mappingCylinderMap_target, mappingCylinderPushoutDesc_cylinder,
      mappingCylinderPushoutDesc_right]
  · intro s m hm₁ hm₂
    apply sqD.hom_ext
    · rw [mappingCylinderPushoutDesc_cylinder]
      have hh := congrArg (fun k ↦ lM ≫ k) hm₂
      simpa only [← Category.assoc, mappingCylinderMap_cylinder] using hh
    · rw [mappingCylinderPushoutDesc_ends]
      ext x
      cases x with
      | inl x => exact ConcreteCategory.congr_hom hm₁ x
      | inr x =>
        have hh := congrArg (fun k ↦ cM ≫ k) hm₂
        have hh' : rightEnd e ≫ m = cM ≫ s.inr := by
          simpa only [← Category.assoc, mappingCylinderMap_target] using hh
        exact ConcreteCategory.congr_hom hh' x


variable {bP : B ⟶ P} {cP : C ⟶ P} (sqP : IsPushout f g bP cP)

include sqP

omit sqD in
/-- The cylinder is collapsed to the common image of its source. -/
theorem collapse_square :
    TopCat.intervalEndpoints A ≫ (fst A TopCat.I ≫ f ≫ bP) =
      endMap f g ≫ sumElim bP cP := by
  ext x
  cases x with
  | inl x => rfl
  | inr x => exact ConcreteCategory.congr_hom sqP.w x

/-- The canonical map from the actual double cylinder to the ordinary pushout. -/
def collapse : D ⟶ P :=
  sqD.desc (fst A TopCat.I ≫ f ≫ bP) (sumElim bP cP) (collapse_square sqP)

@[reassoc (attr := simp)] theorem collapse_cylinder :
    l ≫ collapse sqD sqP = fst A TopCat.I ≫ f ≫ bP := sqD.inl_desc _ _ _
@[reassoc (attr := simp)] theorem collapse_ends :
    e ≫ collapse sqD sqP = sumElim bP cP := sqD.inr_desc _ _ _
@[reassoc (attr := simp)] theorem collapse_leftEnd :
    leftEnd e ≫ collapse sqD sqP = bP := by
  ext x
  exact ConcreteCategory.congr_hom (collapse_ends sqD sqP) (Sum.inl x)
@[reassoc (attr := simp)] theorem collapse_rightEnd :
    rightEnd e ≫ collapse sqD sqP = cP := by
  ext x
  exact ConcreteCategory.congr_hom (collapse_ends sqD sqP) (Sum.inr x)

@[simp] theorem collapse_cylinder_apply (a : A) (t : TopCat.I) :
    collapse sqD sqP (l (a, t)) = bP (f a) :=
  ConcreteCategory.congr_hom (collapse_cylinder sqD sqP) (a, t)
@[simp] theorem collapse_left (b : B) : collapse sqD sqP (e (Sum.inl b)) = bP b :=
  ConcreteCategory.congr_hom (collapse_ends sqD sqP) (Sum.inl b)
@[simp] theorem collapse_right (c : C) : collapse sqD sqP (e (Sum.inr c)) = cP c :=
  ConcreteCategory.congr_hom (collapse_ends sqD sqP) (Sum.inr c)

/-- The collapse restricted to the right mapping cylinder is its ordinary projection. -/
@[reassoc (attr := simp)] theorem mappingCylinderMap_collapse :
    mappingCylinderMap sqD sqM ≫ collapse sqD sqP =
      TopCat.MappingCylinder.mappingCylinderProjection sqM ≫ cP := by
  apply sqM.hom_ext
  · rw [← Category.assoc, mappingCylinderMap_cylinder, collapse_cylinder,
      TopCat.MappingCylinder.mappingCylinderProjection_cylinder_assoc, sqP.w]
  · rw [← Category.assoc, mappingCylinderMap_target, collapse_rightEnd,
      ← Category.assoc, TopCat.MappingCylinder.mappingCylinderProjection_target, Category.id_comp]

/-- The iterated-pushout comparison is precisely the double-cylinder collapse. -/
theorem mappingCylinderPushoutCollapse_eq :
    (mappingCylinderPushout sqD sqM).desc bP
      (TopCat.MappingCylinder.mappingCylinderProjection sqM ≫ cP)
      (by rw [Category.assoc, TopCat.MappingCylinder.mappingCylinderProjection_start_assoc, sqP.w])
        =
        collapse sqD sqP := by
  apply (mappingCylinderPushout sqD sqM).hom_ext
  · rw [IsPushout.inl_desc, collapse_leftEnd]
  · rw [IsPushout.inr_desc, mappingCylinderMap_collapse]

/-- With a cofibrant left leg, the collapse is a homotopy equivalence,
using any actual mapping cylinder of the right leg. -/
def collapseHomotopyEquivOfMappingCylinder (hf : TopCat.HomotopyExtensionProperty f) :
    ContinuousMap.HomotopyEquiv D P := by
  let E := TopCat.MappingCylinder.mappingCylinderPushoutCollapseHomotopyEquiv sqM
    (mappingCylinderPushout sqD sqM) sqP hf
  have hE : E.toFun = (collapse sqD sqP).hom :=
    congrArg TopCat.Hom.hom (mappingCylinderPushoutCollapse_eq sqD sqM sqP)
  exact { E with
    toFun := (collapse sqD sqP).hom
    left_inv := by simpa only [hE] using E.left_inv
    right_inv := by simpa only [hE] using E.right_inv }

@[simp] theorem collapseHomotopyEquivOfMappingCylinder_toFun
    (hf : TopCat.HomotopyExtensionProperty f) :
    (collapseHomotopyEquivOfMappingCylinder sqD sqM sqP hf).toFun =
      (collapse sqD sqP).hom := rfl

/-- The canonical collapse from any actual double cylinder to the ordinary
pushout is an actual homotopy equivalence when the left leg has HEP.
Neither leg is assumed to be a homotopy equivalence. -/
def collapseHomotopyEquiv (hf : TopCat.HomotopyExtensionProperty f) :
    ContinuousMap.HomotopyEquiv D P :=
  collapseHomotopyEquivOfMappingCylinder sqD
    (IsPushout.of_hasPushout (TopCat.ι₁ : A ⟶ A ⊗ TopCat.I) g) sqP hf

@[simp] theorem collapseHomotopyEquiv_toFun (hf : TopCat.HomotopyExtensionProperty f) :
    (collapseHomotopyEquiv sqD sqP hf).toFun = (collapse sqD sqP).hom := rfl


variable {A' B' C' D' P' : TopCat.{u}} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}
  (sqD' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
  {bP' : B' ⟶ P'} {cP' : C' ⟶ P'} (sqP' : IsPushout f' g' bP' cP')

/-- Strict naturality of the collapse for specified compatible maps of
actual double cylinders and ordinary pushouts. -/
theorem collapse_naturality_of_map
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D') (p : P ⟶ P')
    (wf : f ≫ b = a ≫ f')
    (wl : (a ▷ TopCat.I) ≫ l' = l ≫ d)
    (we : sumMap b c ≫ e' = e ≫ d)
    (wb : bP ≫ p = b ≫ bP') (wc : cP ≫ p = c ≫ cP') :
    d ≫ collapse sqD' sqP' = collapse sqD sqP ≫ p := by
  apply sqD.hom_ext
  · rw [← Category.assoc l d, ← wl, Category.assoc, collapse_cylinder,
      collapse_cylinder_assoc]
    ext x
    change bP' (f' (a x.1)) = p (bP (f x.1))
    exact (congrArg bP' (ConcreteCategory.congr_hom wf x.1)).symm.trans
      (ConcreteCategory.congr_hom wb (f x.1)).symm
  · rw [← Category.assoc e d, ← we, Category.assoc, collapse_ends, collapse_ends_assoc]
    ext x
    cases x with
    | inl x => exact (ConcreteCategory.congr_hom wb x).symm
    | inr x => exact (ConcreteCategory.congr_hom wc x).symm

/-- The canonical maps of double cylinders commute exactly with collapse. -/
theorem collapse_naturality
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (p : P ⟶ P')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
    (wb : bP ≫ p = b ≫ bP') (wc : cP ≫ p = c ≫ cP') :
    map sqD sqD' a b c wf wg ≫ collapse sqD' sqP' = collapse sqD sqP ≫ p :=
  collapse_naturality_of_map sqD sqP sqD' sqP' a b c _ p wf
    (map_cylinder sqD sqD' a b c wf wg).symm
    (map_ends sqD sqD' a b c wf wg).symm wb wc

/-- The actual homotopy equivalences supplied by cofibrant collapse form
a strictly commuting square over every compatible pushout map. -/
theorem collapseHomotopyEquiv_naturality
    (hf : TopCat.HomotopyExtensionProperty f)
    (hf' : TopCat.HomotopyExtensionProperty f')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (p : P ⟶ P')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
    (wb : bP ≫ p = b ≫ bP') (wc : cP ≫ p = c ≫ cP') :
    map sqD sqD' a b c wf wg ≫ TopCat.ofHom (collapseHomotopyEquiv sqD' sqP' hf').toFun =
      TopCat.ofHom (collapseHomotopyEquiv sqD sqP hf).toFun ≫ p :=
  collapse_naturality sqD sqP sqD' sqP' a b c p wf wg wb wc

/-- Collapse the canonical double cylinder to the given ordinary pushout. -/
abbrev collapseOfPushout {A B C P : TopCat.{u}} {f : A ⟶ B} {g : A ⟶ C}
    {i : B ⟶ P} {j : C ⟶ P} (sq : IsPushout f g i j) : Cylinder f g ⟶ P :=
  collapse (cylinderSquare f g) sq


end TopCat.DoubleCylinder
