/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.UniverseHomotopy
public import Colib.Topology.ClassifyingSpace.Naturality

/-! # Naturality of classifying-space homotopies across universes

Constant functors and the actual realized homotopies agree with their native
common-universe constructions at every point and interval parameter.

Implementation source: the preliminary lemmas in
`Quillen/CategoryTheory/TheoremB/StructuredUniverseComparison.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology unitInterval
universe u₁ v₁ u₂ v₂
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A constant functor realizes to the constant map, in independent universes. -/
@[simp] theorem classifyingSpaceMapUniversal_const (d : D) :
    classifyingSpaceMapUniversal ((Functor.const C).obj d) =
      ContinuousMap.const (ClassifyingSpace C) (classifyingSpacePoint d) := by
  let U : C ⥤ AsSmall.{max u₁ v₁ u₂ v₂} C := AsSmall.up
  let V : AsSmall.{max u₁ v₁ u₂ v₂} D ⥤ D := AsSmall.down
  let K : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D :=
    (Functor.const _).obj (AsSmall.up.obj d)
  have h : (U ⋙ K) ⋙ V = (Functor.const C).obj d := rfl
  rw [← h, classifyingSpaceMapUniversal_comp, classifyingSpaceMapUniversal_comp,
    classifyingSpaceMapUniversal_eq K]
  ext x
  change classifyingSpaceMapUniversal V (classifyingSpaceMap K
    (classifyingSpaceMapUniversal U x)) = classifyingSpacePoint d
  rw [show classifyingSpaceMap K = TopCat.const (classifyingSpacePoint (AsSmall.up.obj d))
    from classifyingSpaceMap_const_direct _]
  exact classifyingSpaceMapUniversal_point V _

/-- In common small universes, the universal homotopy is the original homotopy
at every point and every interval parameter. -/
theorem classifyingSpaceUniversalHomotopy_eq {A B : Type u₁}
    [SmallCategory A] [SmallCategory B] {F G : A ⥤ B} (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace A) :
    classifyingSpaceUniversalHomotopy α (t, x) =
      classifyingSpaceNaturalTransformationHomotopy α (t, x) := by
  let U : A ⥤ AsSmall.{u₁} A := AsSmall.up
  let V : AsSmall.{u₁} B ⥤ B := AsSmall.down
  change classifyingSpaceMapUniversal V
    (classifyingSpaceNaturalTransformationHomotopy
      (Functor.whiskerLeft AsSmall.down (Functor.whiskerRight α AsSmall.up))
      (t, classifyingSpaceMapUniversal U x)) = _
  rw [classifyingSpaceNaturalTransformationHomotopy_whiskerLeft,
    classifyingSpaceNaturalTransformationHomotopy_whiskerRight]
  have hx : classifyingSpaceMap (AsSmall.down : AsSmall.{u₁} A ⥤ A)
      (classifyingSpaceMapUniversal U x) = x := by
    change (classifyingSpaceMap (AsSmall.down : AsSmall.{u₁} A ⥤ A)).hom
      (classifyingSpaceMapUniversal U x) = x
    rw [← classifyingSpaceMapUniversal_eq]
    change ((classifyingSpaceMapUniversal AsSmall.down).comp
      (classifyingSpaceMapUniversal U)) x = x
    rw [← classifyingSpaceMapUniversal_comp]
    change classifyingSpaceMapUniversal (𝟭 A) x = x
    rw [classifyingSpaceMapUniversal_id]
    rfl
  rw [hx]
  change ((classifyingSpaceMapUniversal V).comp
    (classifyingSpaceMap (AsSmall.up : B ⥤ AsSmall.{u₁} B)).hom) _ = _
  rw [← classifyingSpaceMapUniversal_eq (AsSmall.up : B ⥤ AsSmall.{u₁} B)]
  rw [← classifyingSpaceMapUniversal_comp]
  change classifyingSpaceMapUniversal (𝟭 B) _ = _
  rw [classifyingSpaceMapUniversal_id]
  rfl

end CategoryTheory
