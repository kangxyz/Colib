/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.Product
public import Colib.Topology.ClassifyingSpace.NaturalTransformationTracks
public import Colib.Topology.ClassifyingSpace.Constant
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransportGroup
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Homotopy groups at the unit of a monoidal classifying space

The multiplication is induced by the actual tensor functor and the actual
product comparison on homotopy groups. Its output is transported along the
original left-unitor edge. In particular, no unrestricted realization-product
homeomorphism or based version of an unbased homotopy is assumed.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Topology SSet HomotopyGroup MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

@[simp]
lemma shiftedHomotopyGroupMap_const (c d : C) (n : ℕ) :
    shiftedHomotopyGroupMap ((Functor.const C).obj d) c n = 1 := by
  unfold shiftedHomotopyGroupMap
  simp only [classifyingSpaceMap_const_direct]
  exact piMap_const n

variable [MonoidalCategory C]

/-- Insert the monoidal unit as the first coordinate. -/
abbrev unitPairLeft : C ⥤ C × C := ((Functor.const C).obj (𝟙_ C)).prod' (𝟭 C)

/-- Insert the monoidal unit as the second coordinate. -/
abbrev unitPairRight : C ⥤ C × C := (𝟭 C).prod' ((Functor.const C).obj (𝟙_ C))

/-- The actual left unitor after multiplying the unit insertion. -/
def unitPairLeftNatTrans : unitPairLeft (C := C) ⋙ tensor C ⟶ 𝟭 C where
  app X := (λ_ X).hom
  naturality X Y f := by
    change (𝟙 (𝟙_ C) ⊗ₘ f) ≫ (λ_ Y).hom = (λ_ X).hom ≫ f
    simp

/-- The actual right unitor after multiplying the unit insertion. -/
def unitPairRightNatTrans : unitPairRight (C := C) ⋙ tensor C ⟶ 𝟭 C where
  app X := (ρ_ X).hom
  naturality X Y f := by
    change (f ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ Y).hom = (ρ_ X).hom ≫ f
    simp

/-- Multiplication of homotopy groups uses the explicit left-unitor basepoint path. -/
def classifyingUnitPiMultiplication (n : ℕ) :
    (ShiftedHomotopyGroup C (𝟙_ C) n × ShiftedHomotopyGroup C (𝟙_ C) n) →*
      ShiftedHomotopyGroup C (𝟙_ C) n :=
  (pathTransportMulEquiv (classifyingSpacePath (λ_ (𝟙_ C)).hom) n).toMonoidHom.comp
    ((shiftedHomotopyGroupMap (tensor C) (𝟙_ C, 𝟙_ C) n).comp
      (classifyingSpaceProductPiEquiv C C (𝟙_ C) (𝟙_ C) n).symm.toMonoidHom)

lemma classifyingSpaceProductPiEquiv_unitPairLeft (n : ℕ)
    (a : ShiftedHomotopyGroup C (𝟙_ C) n) :
    classifyingSpaceProductPiEquiv C C (𝟙_ C) (𝟙_ C) n
      (shiftedHomotopyGroupMap unitPairLeft (𝟙_ C) n a) = (1, a) := by
  change classifyingSpaceProductPiEquiv C C (𝟙_ C) (𝟙_ C) n
    (shiftedHomotopyGroupMap (((Functor.const C).obj (𝟙_ C)).prod' (𝟭 C)) (𝟙_ C) n a) = _
  have h := classifyingSpaceProductPiEquiv_pairing C C
    ((Functor.const C).obj (𝟙_ C)) (𝟭 C) (𝟙_ C) n a
  rw [shiftedHomotopyGroupMap_const, shiftedHomotopyGroupMap_id] at h
  exact h

lemma classifyingSpaceProductPiEquiv_unitPairRight (n : ℕ)
    (a : ShiftedHomotopyGroup C (𝟙_ C) n) :
    classifyingSpaceProductPiEquiv C C (𝟙_ C) (𝟙_ C) n
      (shiftedHomotopyGroupMap unitPairRight (𝟙_ C) n a) = (a, 1) := by
  change classifyingSpaceProductPiEquiv C C (𝟙_ C) (𝟙_ C) n
    (shiftedHomotopyGroupMap ((𝟭 C).prod' ((Functor.const C).obj (𝟙_ C))) (𝟙_ C) n a) = _
  have h := classifyingSpaceProductPiEquiv_pairing C C
    (𝟭 C) ((Functor.const C).obj (𝟙_ C)) (𝟙_ C) n a
  rw [shiftedHomotopyGroupMap_const, shiftedHomotopyGroupMap_id] at h
  exact h

@[simp]
lemma classifyingUnitPiMultiplication_one_left (n : ℕ)
    (a : ShiftedHomotopyGroup C (𝟙_ C) n) :
    classifyingUnitPiMultiplication n (1, a) = a := by
  have hi := (classifyingSpaceProductPiEquiv C C (𝟙_ C) (𝟙_ C) n).symm_apply_apply
    (shiftedHomotopyGroupMap unitPairLeft (𝟙_ C) n a)
  rw [classifyingSpaceProductPiEquiv_unitPairLeft] at hi
  change pathTransportMulEquiv (classifyingSpacePath (λ_ (𝟙_ C)).hom) n
    (shiftedHomotopyGroupMap (tensor C) (𝟙_ C, 𝟙_ C) n
      ((classifyingSpaceProductPiEquiv C C (𝟙_ C) (𝟙_ C) n).symm (1, a))) = a
  rw [hi, pathTransportMulEquiv_apply]
  have h := pathTransport_classifyingSpaceMap_naturalTransformation
    (unitPairLeftNatTrans (C := C)) (𝟙_ C) (n + 1) a
  change pathTransport (classifyingSpacePath (λ_ (𝟙_ C)).hom) (n + 1)
    (shiftedHomotopyGroupMap (unitPairLeft ⋙ tensor C) (𝟙_ C) n a) =
      shiftedHomotopyGroupMap (𝟭 C) (𝟙_ C) n a at h
  rw [shiftedHomotopyGroupMap_comp, shiftedHomotopyGroupMap_id] at h
  exact h

@[simp]
lemma classifyingUnitPiMultiplication_one_right (n : ℕ)
    (a : ShiftedHomotopyGroup C (𝟙_ C) n) :
    classifyingUnitPiMultiplication n (a, 1) = a := by
  have hi := (classifyingSpaceProductPiEquiv C C (𝟙_ C) (𝟙_ C) n).symm_apply_apply
    (shiftedHomotopyGroupMap unitPairRight (𝟙_ C) n a)
  rw [classifyingSpaceProductPiEquiv_unitPairRight] at hi
  change pathTransportMulEquiv (classifyingSpacePath (λ_ (𝟙_ C)).hom) n
    (shiftedHomotopyGroupMap (tensor C) (𝟙_ C, 𝟙_ C) n
      ((classifyingSpaceProductPiEquiv C C (𝟙_ C) (𝟙_ C) n).symm (a, 1))) = a
  rw [hi, pathTransportMulEquiv_apply, unitors_equal]
  have h := pathTransport_classifyingSpaceMap_naturalTransformation
    (unitPairRightNatTrans (C := C)) (𝟙_ C) (n + 1) a
  change pathTransport (classifyingSpacePath (ρ_ (𝟙_ C)).hom) (n + 1)
    (shiftedHomotopyGroupMap (unitPairRight ⋙ tensor C) (𝟙_ C) n a) =
      shiftedHomotopyGroupMap (𝟭 C) (𝟙_ C) n a at h
  rw [shiftedHomotopyGroupMap_comp, shiftedHomotopyGroupMap_id] at h
  exact h

/-- Eckmann–Hilton on the original homotopy-group multiplication at the unit. -/
theorem classifyingUnitPi_mul_comm (n : ℕ)
    (a b : ShiftedHomotopyGroup C (𝟙_ C) n) : a * b = b * a := by
  let m := classifyingUnitPiMultiplication (C := C) n
  calc
    a * b = m (a, 1) * m (1, b) := by simp [m]
    _ = m ((a, 1) * (1, b)) := (m.map_mul _ _).symm
    _ = m ((1, b) * (a, 1)) := by simp
    _ = m (1, b) * m (a, 1) := m.map_mul _ _
    _ = b * a := by simp [m]

/-- The actual path-quotient fundamental group at the monoidal unit is abelian. -/
theorem classifyingUnitFundamentalGroup_mul_comm
    (a b : FundamentalGroup (ClassifyingSpace C) (classifyingSpacePoint (𝟙_ C))) :
    a * b = b * a := by
  let e := HomotopyGroup.pi1MulEquivFundamentalGroup
    (X := ClassifyingSpace C) (x := classifyingSpacePoint (𝟙_ C))
  apply e.symm.injective
  simp only [map_mul]
  exact classifyingUnitPi_mul_comm 0 (e.symm a) (e.symm b)

end CategoryTheory
