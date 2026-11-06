/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.GroupTheory.Steinberg.Matrix

/-!
# Field change on the stable Steinberg presentation

A field homomorphism acts on the existing finite-rank-labelled presentation by
keeping its rank and both indices and applying the homomorphism to its coefficient.
The actual target root and stabilization laws kill all four defining relator
families. The resulting homomorphisms preserve identities and composition.

The canonical maps to the original stable general linear group form a commuting
square with its original `StableGeneralLinear.map`. Corestricting that same matrix
map to the original stable elementary subgroups gives the elementary square.
Every formula retains the original finite-stage elementary generator values.

No characteristic or cardinality restriction is used. No kernel identification,
universal central extension, or Quillen K2 comparison is asserted.

## Implementation provenance

Adapted from `Quillen/Algebra/Group/StableSteinbergNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving ranks, indices and entries.
-/
@[expose] public section

noncomputable section

universe u v w

namespace StableSteinberg

variable {F : Type u} [Field F] {L : Type v} [Field L] {M : Type w} [Field M]

/-- Field change on the actual Steinberg presentation, with unchanged finite rank and indices. -/
def map (f : F →+* L) : Group F →* Group L :=
  PresentedGroup.toGroup (f := fun g : Generator F =>
    x L g.rank g.row g.col g.ne (f g.entry)) (by
      intro r hr
      cases hr with
      | rootAdd n i j hij a b =>
          simp only [map_mul, map_inv, word, FreeGroup.lift_apply_of, map_add]
          rw [x_add]
          exact mul_inv_cancel _
      | disjoint n i j k l hij hkl hjk hli a b =>
          simp only [map_commutatorElement, word, FreeGroup.lift_apply_of]
          exact commutatorElement_eq_one_iff_commute.mpr
            (x_commute L n i j k l hij hkl hjk hli (f a) (f b))
      | chain n i j k hij hjk hik a b =>
          simp only [map_mul, map_inv, map_commutatorElement, word, FreeGroup.lift_apply_of]
          rw [x_commutator]
          exact mul_inv_cancel _
      | stabilize n i j hij a =>
          simp only [map_mul, map_inv, word, FreeGroup.lift_apply_of]
          rw [x_stabilize]
          exact mul_inv_cancel _)

/-- Field change retains the same finite root and changes only its coefficient. -/
@[simp] lemma map_x (f : F →+* L) (n : ℕ) (i j : Fin n) (hij : i ≠ j) (a : F) :
    map f (x F n i j hij a) = x L n i j hij (f a) :=
  PresentedGroup.toGroup.of _

/-- The identity field homomorphism induces the original identity group homomorphism. -/
@[simp] lemma map_id : map (RingHom.id F) = MonoidHom.id (Group F) := by
  apply PresentedGroup.ext
  rintro ⟨n, i, j, hij, a⟩
  change map (RingHom.id F) (x F n i j hij a) = x F n i j hij a
  rw [map_x, RingHom.id_apply]

/-- Composition of field homomorphisms induces composition on the actual presentation. -/
@[simp] lemma map_comp (f : F →+* L) (g : L →+* M) :
    map (g.comp f) = (map g).comp (map f) := by
  apply PresentedGroup.ext
  rintro ⟨n, i, j, hij, a⟩
  change map (g.comp f) (x F n i j hij a) = map g (map f (x F n i j hij a))
  rw [map_x, map_x, map_x, RingHom.comp_apply]

/-- The original stable-matrix homomorphisms commute with actual field change. -/
lemma toStableGeneralLinear_naturality (f : F →+* L) :
    (toStableGeneralLinear L).comp (map f) =
      (StableGeneralLinear.map f).comp (toStableGeneralLinear F) := by
  apply PresentedGroup.ext
  rintro ⟨n, i, j, hij, a⟩
  change toStableGeneralLinear L (map f (x F n i j hij a)) =
    StableGeneralLinear.map f (toStableGeneralLinear F (x F n i j hij a))
  rw [map_x, toStableGeneralLinear_x, toStableGeneralLinear_x, StableGeneralLinear.map_of]
  change StableGeneralLinear.of L n (Matrix.GeneralLinearGroup.elementary i j hij (f a)) =
    StableGeneralLinear.of L n (Units.map (RingHom.mapMatrix f).toMonoidHom
      (Matrix.GeneralLinearGroup.elementary i j hij a))
  rw [Matrix.GeneralLinearGroup.mapMatrixUnits_elementary]

/-- The original stable matrix field map corestricted to the actual elementary subgroups. -/
def elementaryMap (f : F →+* L) :
    StableGeneralLinear.elementary F →* StableGeneralLinear.elementary L where
  toFun a := ⟨StableGeneralLinear.map f a,
    StableGeneralLinear.map_elementary_le f
      (Subgroup.mem_map_of_mem (StableGeneralLinear.map f) a.property)⟩
  map_one' := Subtype.ext (map_one (StableGeneralLinear.map f))
  map_mul' a b := Subtype.ext (map_mul (StableGeneralLinear.map f)
    (a : StableGeneralLinear.Group F) (b : StableGeneralLinear.Group F))

/-- The underlying stable matrix is the original coefficient-change map. -/
@[simp] lemma elementaryMap_coe (f : F →+* L) (a : StableGeneralLinear.elementary F) :
    (elementaryMap f a : StableGeneralLinear.Group L) = StableGeneralLinear.map f a := rfl

/-- The actual elementary field map retains identity homomorphisms. -/
@[simp] lemma elementaryMap_id :
    elementaryMap (RingHom.id F) = MonoidHom.id (StableGeneralLinear.elementary F) := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  change StableGeneralLinear.map (RingHom.id F) a = a
  rw [StableGeneralLinear.map_id, MonoidHom.id_apply]

/-- The actual elementary field maps retain composition. -/
@[simp] lemma elementaryMap_comp (f : F →+* L) (g : L →+* M) :
    elementaryMap (g.comp f) = (elementaryMap g).comp (elementaryMap f) := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  change StableGeneralLinear.map (g.comp f) a =
    StableGeneralLinear.map g (StableGeneralLinear.map f a)
  rw [StableGeneralLinear.map_comp, MonoidHom.comp_apply]

/-- The original canonical maps onto actual elementary subgroups commute with field change. -/
lemma toElementary_naturality (f : F →+* L) :
    (toElementary L).comp (map f) = (elementaryMap f).comp (toElementary F) := by
  apply MonoidHom.ext
  intro a
  apply Subtype.ext
  exact DFunLike.congr_fun (toStableGeneralLinear_naturality f) a

end StableSteinberg
