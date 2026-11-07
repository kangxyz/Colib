/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Quillen.LowDegreeScalarAction.IdentityAutomorphism
public import Colib.KTheory.Quillen.LowDegreeScalarAction.ExactNaturality
public import Colib.KTheory.Quillen.SmallModel.Exact
public import Colib.CategoryTheory.Linear.ScalarAutomorphism

/-!
# Actual scalar units in the original low-degree K-operations

The canonical map to the center of a linear category, followed by the existing
units-to-automorphisms equivalence, supplies the actual scalar natural
automorphism of the identity. Its normalized Q self-homotopy defines the
existing K1-to-K2 operation. Its source and unit laws are bundled as
homomorphisms, and the representative equations retain the original cubes.

The ordinary linear-functor square preserves the same scalar coefficient.
For a chosen SmallModel, full faithfulness of its original realization functor
lifts this same natural automorphism; no additional linear structure on that
model is assumed. Finite-module and finite-projective specializations belong to
`Colib.RingTheory.KTheory.Quillen.LowDegreeScalarAction.ScalarUnit`.

The identity-automorphism naturality theorem gives the original
exact-functor K-map squares, including the actual mapped-model small K-maps,
from ordinary linearity. Ordered-symbol or product normalization and boundary
compatibility remain separate obligations.
-/
/-! Implementation source: `Quillen/KTheory/LowDegreeScalarAction/ScalarUnit.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original normalized-Q maps,
whole identity tracks, upper SmallK and tensor-extension formulas are retained.
Unused degree-zero and optional matrix-cube calibrations are not imported. -/
@[expose] public section

noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe w u v u₁ v₁ u₂ v₂ s
open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open CategoryTheory.Linear
open scoped ZeroObject Topology

namespace CategoryTheory.ExactCategory.ScalarUnit

section MappedModelAutomorphism
variable (R : Type w) [Ring R]
  {C : Type u₁} [Category.{v₁} C] [Preadditive C] [HasFiniteBiproducts C] [Linear R C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasFiniteBiproducts D] [Linear R D]
  [EssentiallySmall.{s} C] [EssentiallySmall.{s} D]
  {EC : ExactStructure C} {ED : ExactStructure D}

/-- The original mapped-model functor preserves the lifted scalar components. -/
theorem smallModelScalarNatAut_map (F : ExactFunctor EC ED) [F.toFunctor.Linear R]
    (r : Rˣ) (X : SmallModel.{s} C) :
    F.smallModel.{s}.toFunctor.map (((smallModelScalarNatAut R C r).asIso).hom.app X) =
      ((smallModelScalarNatAut R D r).asIso).hom.app (F.smallModel.{s}.toFunctor.obj X) := by
  change (equivSmallModel.{s} D).functor.map
    (F.toFunctor.map ((equivSmallModel.{s} C).inverse.map
      (((smallModelScalarNatAut R C r).asIso).hom.app X))) =
    ((smallModelScalarNatAut R D r).asIso).hom.app
      ((equivSmallModel.{s} D).functor.obj
        (F.toFunctor.obj ((equivSmallModel.{s} C).inverse.obj X)))
  rw [smallModelScalarNatAut_map_hom]
  have h := scalarNatAut_map R F.toFunctor r ((equivSmallModel.{s} C).inverse.obj X)
  simp only [scalarNatAut_hom_app] at h
  rw [h]
  simpa only [scalarNatAut_hom_app] using
    smallModelScalarNatAut_functor_map_hom R D r
      (F.toFunctor.obj ((equivSmallModel.{s} C).inverse.obj X))

end MappedModelAutomorphism

section Operations
variable {C : Type (max u v)} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (R : Type w) [Ring R] (E : ExactStructure C)

/-- The original K-one operation for an actual multiplicative family of unit automorphisms. -/
def kOneActionOf (a : Rˣ →* Aut (𝟭 C)) : Rˣ →* (E.K 1 →* E.K 2) where
  toFun r := IdentityAutomorphism.kOneAction E (a r).asIso
  map_one' := by
    ext x
    change IdentityAutomorphism.kOneNatAut E x (a 1) = 1
    simp only [map_one]
  map_mul' r t := by
    ext x
    change IdentityAutomorphism.kOneNatAut E x (a (r * t)) =
      IdentityAutomorphism.kOneNatAut E x (a r) * IdentityAutomorphism.kOneNatAut E x (a t)
    simp only [map_mul]

variable [Linear R C]

/-- The original degree-(1,1) operation, a homomorphism in the unit and the K-one class. -/
def kOneAction : Rˣ →* (E.K 1 →* E.K 2) := kOneActionOf R E (scalarNatAut R C)

/-- The scalar operation retains the existing identity-automorphism K-one operation. -/
@[simp] theorem kOneAction_apply (r : Rˣ) (a : E.K 1) :
    kOneAction R E r a = IdentityAutomorphism.kOneAction E ((scalarNatAut R C r).asIso) a := rfl

/-- The degree-(1,1) operation preserves the original source product. -/
theorem kOneAction_source_mul (r : Rˣ) (a b : E.K 1) :
    kOneAction R E r (a * b) = kOneAction R E r a * kOneAction R E r b :=
  (kOneAction R E r).map_mul a b

/-- Multiplication of the actual scalar units adds their degree-(1,1) operations. -/
theorem kOneAction_unit_mul (r t : Rˣ) (a : E.K 1) :
    kOneAction R E (r * t) a = kOneAction R E r a * kOneAction R E t a :=
  DFunLike.congr_fun ((kOneAction R E).map_mul r t) a

/-- The identity K-one input has identity output. -/
theorem kOneAction_source_one (r : Rˣ) : kOneAction R E r 1 = 1 :=
  (kOneAction R E r).map_one

/-- The identity scalar unit has zero degree-(1,1) operation. -/
theorem kOneAction_unit_one (a : E.K 1) : kOneAction R E 1 a = 1 :=
  DFunLike.congr_fun (kOneAction R E).map_one a

/-- The degree-(1,1) representative is the original normalized track-first cube. -/
theorem kOneAction_cube (r : Rˣ) (p : GenLoop (Fin 2) E.KSpace E.kBasepoint) :
    kOneAction R E r ⟦p⟧ =
      (⟦genLoopNormalizedSelfTrackCube 1 p
        (IdentityTrack.track (IdentityAutomorphism.homotopy E ((scalarNatAut R C
          r).asIso)).toHomotopy
          (IdentityAutomorphism.homotopy_fixed E ((scalarNatAut R C r).asIso)) 1 p)⟧ : E.K 2) :=
  IdentityAutomorphism.kOneAction_cube E ((scalarNatAut R C r).asIso) p

/-- Every track time is the actual normalized-Q homotopy of the scalar automorphism. -/
theorem track_apply (r : Rˣ) (m : ℕ)
    (p : GenLoop (Fin (m + 1)) E.KSpace E.kBasepoint)
    (t : unitInterval) (z : Fin (m + 1) → unitInterval) :
    IdentityTrack.track (IdentityAutomorphism.homotopy E ((scalarNatAut R C r).asIso)).toHomotopy
      (IdentityAutomorphism.homotopy_fixed E ((scalarNatAut R C r).asIso)) m p t z =
      classifyingSpaceNaturalTransformationHomotopy
        (ExactFunctor.normalizedQIso (F := ExactFunctor.id E) (G := ExactFunctor.id E)
          ((scalarNatAut R C r).asIso)).hom (t, p z) :=
  IdentityAutomorphism.track_apply E ((scalarNatAut R C r).asIso) m p t z

variable {E} {D : Type (max u v)} [Category.{v} D] [Preadditive D]
  [HasFiniteBiproducts D] [Linear R D] {ED : ExactStructure D}

/-- The K-one scalar operation retains the original degree-one and degree-two K-maps. -/
theorem kOneAction_natural (F : ExactFunctor E ED) [F.toFunctor.Linear R]
    (r : Rˣ) (a : E.K 1) :
    F.KMap 2 (kOneAction R E r a) = kOneAction R ED r (F.KMap 1 a) :=
  IdentityAutomorphism.kOneAction_natural F ((scalarNatAut R C r).asIso) ((scalarNatAut R D
    r).asIso)
    (scalarNatAut_map R F.toFunctor r) a

end Operations

section SmallModelOperations
variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [Linear R C] [EssentiallySmall.{s} C] (E : ExactStructure C)

/-- The actual chosen-model K-one operation with its original scalar automorphism lifted. -/
def smallModelKOneAction : Rˣ →* (E.SmallK.{s} 1 →* E.SmallK.{s} 2) :=
  kOneActionOf R E.smallModel.{s} (smallModelScalarNatAut R C)

/-- The chosen-model operation retains the original K-one operation of the lifted automorphism. -/
@[simp] theorem smallModelKOneAction_apply (r : Rˣ) (a : E.SmallK.{s} 1) :
    smallModelKOneAction R E r a =
      IdentityAutomorphism.kOneAction E.smallModel ((smallModelScalarNatAut R C r).asIso) a := rfl

/-- The chosen-model K-one representative retains the original normalized track-first cube. -/
theorem smallModelKOneAction_cube (r : Rˣ)
    (p : GenLoop (Fin 2) E.smallModel.{s}.KSpace E.smallModel.{s}.kBasepoint) :
    smallModelKOneAction R E r ⟦p⟧ =
      (⟦genLoopNormalizedSelfTrackCube 1 p
        (IdentityTrack.track (IdentityAutomorphism.homotopy E.smallModel
          ((smallModelScalarNatAut R C r).asIso)).toHomotopy
          (IdentityAutomorphism.homotopy_fixed E.smallModel ((smallModelScalarNatAut R C r).asIso))
          1 p)⟧ : E.SmallK.{s} 2) :=
  IdentityAutomorphism.kOneAction_cube E.smallModel ((smallModelScalarNatAut R C r).asIso) p

variable {E} {D : Type u₂} [Category.{v₂} D] [Preadditive D] [HasFiniteBiproducts D]
  [Linear R D] [EssentiallySmall.{s} D] {ED : ExactStructure D}

/-- Chosen-model K-one scalar naturality needs no linear structure on either model. -/
theorem smallModelKOneAction_natural (F : ExactFunctor E ED) [F.toFunctor.Linear R]
    (r : Rˣ) (a : E.SmallK.{s} 1) :
    F.smallKMap.{s} 2 (smallModelKOneAction R E r a) =
      smallModelKOneAction R ED r (F.smallKMap.{s} 1 a) :=
  IdentityAutomorphism.kOneAction_natural.{s, s} F.smallModel.{s}
    ((smallModelScalarNatAut R C r).asIso) ((smallModelScalarNatAut R D r).asIso)
    (smallModelScalarNatAut_map R F r) a

end SmallModelOperations

end CategoryTheory.ExactCategory.ScalarUnit
