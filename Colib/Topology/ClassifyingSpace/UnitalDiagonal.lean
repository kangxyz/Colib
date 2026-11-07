/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.Product
public import Colib.Topology.ClassifyingSpace.NaturalTransformationTracks
public import Colib.Topology.ClassifyingSpace.Constant
public import Colib.Topology.ClassifyingSpace.ArrowPathTransport
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportGroup
public import Colib.Topology.Homotopy.HomotopyGroup.WeakEquivalenceConnected
public import Colib.Topology.ClassifyingSpace.Connectivity

/-!
# Weak contractibility from a unital categorical multiplication and diagonal

A bifunctor with left and right unit isomorphisms induces a unital multiplication
on the actual positive homotopy groups of its classifying space. If the identity
functor maps naturally to the square and the unit component is the inverse unit
isomorphism, each original homotopy class equals its square and hence is trivial.
Categorical connectedness supplies degree zero and gives a weak equivalence to
a point. No global contraction or Whitehead theorem is asserted or assumed.

Only agreement of the two unit components at the unit is required. Associators,
braidings, and their coherence laws are unnecessary.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Topology SSet HomotopyGroup

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Insert a specified unit as the first coordinate. -/
abbrev categoryUnitPairLeft (e : C) : C ⥤ C × C :=
  ((Functor.const C).obj e).prod' (𝟭 C)

/-- Insert a specified unit as the second coordinate. -/
abbrev categoryUnitPairRight (e : C) : C ⥤ C × C :=
  (𝟭 C).prod' ((Functor.const C).obj e)

variable (e : C) (μ : C × C ⥤ C)
  (left : categoryUnitPairLeft e ⋙ μ ≅ 𝟭 C)

/-- The actual multiplication uses product comparison and the original left-unit edge. -/
def classifyingPiMultiplication (n : ℕ) :
    (ShiftedHomotopyGroup C e n × ShiftedHomotopyGroup C e n) →*
      ShiftedHomotopyGroup C e n :=
  (pathTransportMulEquiv (classifyingSpacePath (left.hom.app e)) n).toMonoidHom.comp
    ((shiftedHomotopyGroupMap μ (e, e) n).comp
      (classifyingSpaceProductPiEquiv C C e e n).symm.toMonoidHom)

lemma classifyingSpaceProductPiEquiv_categoryUnitPairLeft (n : ℕ)
    (a : ShiftedHomotopyGroup C e n) :
    classifyingSpaceProductPiEquiv C C e e n
      (shiftedHomotopyGroupMap (categoryUnitPairLeft e) e n a) = (1, a) := by
  have h := classifyingSpaceProductPiEquiv_pairing C C
    ((Functor.const C).obj e) (𝟭 C) e n a
  have hc : shiftedHomotopyGroupMap ((Functor.const C).obj e) e n = 1 := by
    unfold shiftedHomotopyGroupMap
    simp only [classifyingSpaceMap_const_direct]
    exact piMap_const n
  rw [hc, shiftedHomotopyGroupMap_id] at h
  exact h

lemma classifyingSpaceProductPiEquiv_categoryUnitPairRight (n : ℕ)
    (a : ShiftedHomotopyGroup C e n) :
    classifyingSpaceProductPiEquiv C C e e n
      (shiftedHomotopyGroupMap (categoryUnitPairRight e) e n a) = (a, 1) := by
  have h := classifyingSpaceProductPiEquiv_pairing C C
    (𝟭 C) ((Functor.const C).obj e) e n a
  have hc : shiftedHomotopyGroupMap ((Functor.const C).obj e) e n = 1 := by
    unfold shiftedHomotopyGroupMap
    simp only [classifyingSpaceMap_const_direct]
    exact piMap_const n
  rw [hc, shiftedHomotopyGroupMap_id] at h
  exact h

@[simp]
lemma classifyingPiMultiplication_one_left (n : ℕ)
    (a : ShiftedHomotopyGroup C e n) :
    classifyingPiMultiplication e μ left n (1, a) = a := by
  have hi := (classifyingSpaceProductPiEquiv C C e e n).symm_apply_apply
    (shiftedHomotopyGroupMap (categoryUnitPairLeft e) e n a)
  rw [classifyingSpaceProductPiEquiv_categoryUnitPairLeft] at hi
  change pathTransportMulEquiv (classifyingSpacePath (left.hom.app e)) n
    (shiftedHomotopyGroupMap μ (e, e) n
      ((classifyingSpaceProductPiEquiv C C e e n).symm (1, a))) = a
  rw [hi, pathTransportMulEquiv_apply]
  have h := pathTransport_classifyingSpaceMap_naturalTransformation left.hom e (n + 1) a
  change pathTransport (classifyingSpacePath (left.hom.app e)) (n + 1)
    (shiftedHomotopyGroupMap (categoryUnitPairLeft e ⋙ μ) e n a) =
      shiftedHomotopyGroupMap (𝟭 C) e n a at h
  rw [shiftedHomotopyGroupMap_comp, shiftedHomotopyGroupMap_id] at h
  exact h

variable (right : categoryUnitPairRight e ⋙ μ ≅ 𝟭 C)
  (hunit : left.hom.app e = right.hom.app e)

include right hunit in
lemma classifyingPiMultiplication_one_right (n : ℕ)
    (a : ShiftedHomotopyGroup C e n) :
    classifyingPiMultiplication e μ left n (a, 1) = a := by
  have hi := (classifyingSpaceProductPiEquiv C C e e n).symm_apply_apply
    (shiftedHomotopyGroupMap (categoryUnitPairRight e) e n a)
  rw [classifyingSpaceProductPiEquiv_categoryUnitPairRight] at hi
  change pathTransportMulEquiv (classifyingSpacePath (left.hom.app e)) n
    (shiftedHomotopyGroupMap μ (e, e) n
      ((classifyingSpaceProductPiEquiv C C e e n).symm (a, 1))) = a
  rw [hi, pathTransportMulEquiv_apply, hunit]
  have h := pathTransport_classifyingSpaceMap_naturalTransformation right.hom e (n + 1) a
  change pathTransport (classifyingSpacePath (right.hom.app e)) (n + 1)
    (shiftedHomotopyGroupMap (categoryUnitPairRight e ⋙ μ) e n a) =
      shiftedHomotopyGroupMap (𝟭 C) e n a at h
  rw [shiftedHomotopyGroupMap_comp, shiftedHomotopyGroupMap_id] at h
  exact h

include right hunit in
/-- The multiplication induced by the actual bifunctor agrees with the group operation. -/
theorem classifyingPiMultiplication_eq_mul (n : ℕ)
    (a b : ShiftedHomotopyGroup C e n) :
    classifyingPiMultiplication e μ left n (a, b) = a * b := by
  let m := classifyingPiMultiplication e μ left n
  calc
    m (a, b) = m ((a, 1) * (1, b)) := by simp
    _ = m (a, 1) * m (1, b) := m.map_mul _ _
    _ = a * b := by
      rw [classifyingPiMultiplication_one_right e μ left right hunit]
      simp [m]

variable (δ : 𝟭 C ⟶ Functor.diag C ⋙ μ)
  (hδ : δ.app e = left.inv.app e)

include δ hδ in
/-- The normalized natural diagonal acts as the identity after the original unit transport. -/
theorem classifyingPiMultiplication_diagonal (n : ℕ)
    (a : ShiftedHomotopyGroup C e n) :
    classifyingPiMultiplication e μ left n (a, a) = a := by
  have hd : classifyingSpaceProductPiEquiv C C e e n
      (shiftedHomotopyGroupMap (Functor.diag C) e n a) = (a, a) := by
    have h := classifyingSpaceProductPiEquiv_pairing C C (𝟭 C) (𝟭 C) e n a
    rw [shiftedHomotopyGroupMap_id] at h
    exact h
  have hi := (classifyingSpaceProductPiEquiv C C e e n).symm_apply_apply
    (shiftedHomotopyGroupMap (Functor.diag C) e n a)
  rw [hd] at hi
  change pathTransportMulEquiv (classifyingSpacePath (left.hom.app e)) n
    (shiftedHomotopyGroupMap μ (e, e) n
      ((classifyingSpaceProductPiEquiv C C e e n).symm (a, a))) = a
  rw [hi, pathTransportMulEquiv_apply]
  have h := pathTransport_classifyingSpaceMap_naturalTransformation δ e (n + 1) a
  change pathTransport (classifyingSpacePath (δ.app e)) (n + 1)
    (shiftedHomotopyGroupMap (𝟭 C) e n a) =
      shiftedHomotopyGroupMap (Functor.diag C ⋙ μ) e n a at h
  rw [shiftedHomotopyGroupMap_comp, shiftedHomotopyGroupMap_id, hδ] at h
  change pathTransport (classifyingSpacePath (left.inv.app e)) (n + 1) a =
    shiftedHomotopyGroupMap μ (e, e) n
      (shiftedHomotopyGroupMap (Functor.diag C) e n a) at h
  rw [← h]
  exact pathTransport_classifyingSpacePath_inv_hom (left.app e).symm (n + 1) a

include right hunit δ hδ in
/-- Every actual positive homotopy group at the unit is trivial. -/
theorem classifyingSpace_unitPi_subsingleton_of_unitalDiagonal (n : ℕ) :
    Subsingleton (ShiftedHomotopyGroup C e n) := by
  have hall (a : ShiftedHomotopyGroup C e n) : a = 1 := by
    have h := classifyingPiMultiplication_diagonal e μ left δ hδ n a
    rw [classifyingPiMultiplication_eq_mul e μ left right hunit] at h
    exact (mul_left_cancel (a := a) (h.trans (mul_one a).symm))
  exact ⟨fun a b ↦ (hall a).trans (hall b).symm⟩

include right hunit δ hδ in
/-- A connected category with a normalized unital natural diagonal has weakly contractible
classifying space, including degree zero and actual surjectivity on components. -/
theorem classifyingSpace_weaklyContractible_of_unitalDiagonal [IsConnected C] :
    IsWeakHomotopyEquivalence
      (ContinuousMap.const (ClassifyingSpace C) (PUnit.unit : PUnit.{max u v + 1})) := by
  apply isWeakHomotopyEquivalence_of_connected _ (classifyingSpacePoint e)
  intro n
  let : Subsingleton (HomotopyGroup.Pi (n + 1) (ClassifyingSpace C)
      (classifyingSpacePoint e)) :=
    classifyingSpace_unitPi_subsingleton_of_unitalDiagonal e μ left right hunit δ hδ n
  let := subsingleton_pi_of_contractible (n + 1) PUnit.{max u v + 1} PUnit.unit
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun a ↦ ⟨1, Subsingleton.elim _ _⟩⟩

end CategoryTheory
