/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.TheoremB.CompositionHomotopy
public import Colib.Topology.ClassifyingSpace.UniverseNaturality
public import Colib.Topology.Homotopy.ConcatenationFamilies

/-!
# Universal realized composition and cone-family coherence

The original universal natural-transformation maps retain their whole
composition triangles. The whiskering statements keep the displayed common
target universe explicit. Paired cone families cancel a common suffix by an
actual continuous homotopy, for the native Q-cylinder comparison.
-/
/-! Implementation source: `Quillen/Topology/ClassifyingSpace/UniversalComposition.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual cone paths,
composition triangles and categorical universes are preserved under native ownership. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u₁ v₁ u₂ v₂
open CategoryTheory
open scoped Topology unitInterval
namespace CategoryTheory.TheoremB
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F G H : C ⥤ D} (α : F ⟶ G) (β : G ⟶ H)

/-- The actual universal composite-transformation track fills its two-simplex,
relative to both parameter endpoints. -/
def universalCompositionHomotopy :
    (classifyingSpaceUniversalHomotopy (α ≫ β)).toContinuousMap.HomotopyRel
      ((classifyingSpaceUniversalHomotopy α).trans
        (classifyingSpaceUniversalHomotopy β)).toContinuousMap
      {z : unitInterval × ClassifyingSpace C | z.1 = 0 ∨ z.1 = 1} := by
  let U : C ⥤ AsSmall.{max u₁ v₁ u₂ v₂} C := AsSmall.up
  let V : AsSmall.{max u₁ v₁ u₂ v₂} D ⥤ D := AsSmall.down
  let α' := Functor.whiskerLeft (AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C)
    (Functor.whiskerRight α (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D))
  let β' := Functor.whiskerLeft (AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C)
    (Functor.whiskerRight β (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D))
  let J := naturalTransformationCompositionHomotopy α' β'
  refine {
    toFun z := classifyingSpaceMapUniversal V
      (J (z.1, (z.2.1, classifyingSpaceMapUniversal U z.2.2)))
    continuous_toFun := by fun_prop
    map_zero_left := ?_
    map_one_left := ?_
    prop' := ?_ }
  · intro z
    change classifyingSpaceMapUniversal V
      (J (0, (z.1, classifyingSpaceMapUniversal U z.2))) = _
    erw [J.apply_zero]
    rfl
  · intro z
    change classifyingSpaceMapUniversal V
      (J (1, (z.1, classifyingSpaceMapUniversal U z.2))) = _
    erw [J.apply_one]
    change classifyingSpaceMapUniversal V
      (((classifyingSpaceNaturalTransformationHomotopy α').trans
        (classifyingSpaceNaturalTransformationHomotopy β'))
          (z.1, classifyingSpaceMapUniversal U z.2)) =
      ((classifyingSpaceUniversalHomotopy α).trans (classifyingSpaceUniversalHomotopy β)) z
    rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs <;> rfl
  · intro s z hz
    exact congrArg (classifyingSpaceMapUniversal V) (J.prop s
      (z.1, classifyingSpaceMapUniversal U z.2) hz)

end CategoryTheory.TheoremB

namespace CategoryTheory

variable {A : Type u₁} [Category.{v₁} A] {C : Type u₂} [Category.{v₂} C]
  {D : Type (max u₁ v₁ u₂ v₂)} [SmallCategory D]

/-- Precomposition preserves the entire universal track in the displayed common target universe. -/
theorem universalHomotopy_whiskerLeft (K : A ⥤ C) {F G : C ⥤ D} (α : F ⟶ G)
    (t : unitInterval) (x : ClassifyingSpace A) :
    classifyingSpaceUniversalHomotopy (Functor.whiskerLeft K α) (t,x) =
      classifyingSpaceUniversalHomotopy α (t,classifyingSpaceMapUniversal K x) := by
  let UA : A ⥤ AsSmall.{max u₁ v₁ u₂ v₂} A := AsSmall.up
  let UC : C ⥤ AsSmall.{max u₁ v₁ u₂ v₂} C := AsSmall.up
  let VD : AsSmall.{max u₁ v₁ u₂ v₂} D ⥤ D := AsSmall.down
  let K' : AsSmall.{max u₁ v₁ u₂ v₂} A ⥤ AsSmall.{max u₁ v₁ u₂ v₂} C :=
    AsSmall.down ⋙ K ⋙ AsSmall.up
  let α' := Functor.whiskerLeft (AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C)
    (Functor.whiskerRight α (AsSmall.up : D ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D))
  change classifyingSpaceMapUniversal VD
    (classifyingSpaceNaturalTransformationHomotopy (Functor.whiskerLeft K' α')
      (t,classifyingSpaceMapUniversal UA x)) =
    classifyingSpaceMapUniversal VD
      (classifyingSpaceNaturalTransformationHomotopy α'
        (t,classifyingSpaceMapUniversal UC (classifyingSpaceMapUniversal K x)))
  rw [classifyingSpaceNaturalTransformationHomotopy_whiskerLeft]
  have hx : classifyingSpaceMap K' (classifyingSpaceMapUniversal UA x) =
      classifyingSpaceMapUniversal UC (classifyingSpaceMapUniversal K x) := by
    change ((classifyingSpaceMap K').hom.comp (classifyingSpaceMapUniversal UA)) x = _
    rw [← classifyingSpaceMapUniversal_eq, ← classifyingSpaceMapUniversal_comp]
    change classifyingSpaceMapUniversal (K ⋙ UC) x = _
    rw [classifyingSpaceMapUniversal_comp]
    rfl
  rw [hx]

variable {F G : A ⥤ C}

/-- Postcomposition preserves the entire universal track in the displayed common target
universe. -/
theorem universalHomotopy_whiskerRight (α : F ⟶ G) (K : C ⥤ D)
    (t : unitInterval) (x : ClassifyingSpace A) :
    classifyingSpaceUniversalHomotopy (Functor.whiskerRight α K) (t,x) =
      classifyingSpaceMapUniversal K (classifyingSpaceUniversalHomotopy α (t,x)) := by
  let UA : A ⥤ AsSmall.{max u₁ v₁ u₂ v₂} A := AsSmall.up
  let VC : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ C := AsSmall.down
  let VD : AsSmall.{max u₁ v₁ u₂ v₂} D ⥤ D := AsSmall.down
  let K' : AsSmall.{max u₁ v₁ u₂ v₂} C ⥤ AsSmall.{max u₁ v₁ u₂ v₂} D :=
    AsSmall.down ⋙ K ⋙ AsSmall.up
  let α' := Functor.whiskerLeft (AsSmall.down : AsSmall.{max u₁ v₁ u₂ v₂} A ⥤ A)
    (Functor.whiskerRight α (AsSmall.up : C ⥤ AsSmall.{max u₁ v₁ u₂ v₂} C))
  change classifyingSpaceMapUniversal VD
    (classifyingSpaceNaturalTransformationHomotopy (Functor.whiskerRight α' K')
      (t,classifyingSpaceMapUniversal UA x)) =
    classifyingSpaceMapUniversal K
      (classifyingSpaceMapUniversal VC
        (classifyingSpaceNaturalTransformationHomotopy α'
          (t,classifyingSpaceMapUniversal UA x)))
  rw [classifyingSpaceNaturalTransformationHomotopy_whiskerRight]
  change classifyingSpaceMapUniversal VD
    ((classifyingSpaceMap K').hom
      (classifyingSpaceNaturalTransformationHomotopy α' (t,classifyingSpaceMapUniversal UA x))) = _
  rw [← classifyingSpaceMapUniversal_eq K']
  change ((classifyingSpaceMapUniversal VD).comp (classifyingSpaceMapUniversal K')) _ =
    ((classifyingSpaceMapUniversal K).comp (classifyingSpaceMapUniversal VC)) _
  rw [← classifyingSpaceMapUniversal_comp, ← classifyingSpaceMapUniversal_comp]
  rfl

end CategoryTheory

namespace Topology.ConePair
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F G : C ⥤ D} {d : D}

/-- The original universal transformation path with its constant source identified exactly. -/
def realizedCone (α : (Functor.const C).obj d ⟶ F) :
    (ContinuousMap.const (ClassifyingSpace C) (classifyingSpacePoint d)).Homotopy
      (classifyingSpaceMapUniversal F) :=
  (classifyingSpaceUniversalHomotopy α).cast (classifyingSpaceMapUniversal_const _) rfl

/-- The actual loop family of two natural cones with their common target. -/
def naturalPair (α β : (Functor.const C).obj d ⟶ F) :
    C(ClassifyingSpace C, Path (classifyingSpacePoint d) (classifyingSpacePoint d)) :=
  loopMap (realizedCone α) (realizedCone β)

/-- A common terminal natural transformation cancels through its actual composition triangles. -/
def naturalPairSuffixHomotopy (α β : (Functor.const C).obj d ⟶ F) (r : F ⟶ G) :
    (naturalPair (α ≫ r) (β ≫ r)).Homotopy (naturalPair α β) := by
  let A := realizedCone α
  let B := realizedCone β
  let R := classifyingSpaceUniversalHomotopy r
  have J : (naturalPair (α ≫ r) (β ≫ r)).Homotopy
      (loopMap (A.trans R) (B.trans R)) :=
    relativeLoopHomotopy (realizedCone (α ≫ r)) (A.trans R)
      (realizedCone (β ≫ r)) (B.trans R)
      (TheoremB.universalCompositionHomotopy α r) (TheoremB.universalCompositionHomotopy β r)
  exact J.trans (commonTailCancellation A B R)

end Topology.ConePair


namespace CategoryTheory
/-- Equal endpoint functors and equal transported transformations give identical universal
tracks. -/
lemma universalTransformation_congr {A B : Type*} [Category A] [Category B]
    {F G F' G' : A ⥤ B} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G')
    (hα : α ≫ eqToHom hG = eqToHom hF ≫ β)
    (t : unitInterval) (x : ClassifyingSpace A) :
    classifyingSpaceUniversalHomotopy α (t,x) =
      classifyingSpaceUniversalHomotopy β (t,x) := by
  subst F'
  subst G'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hα
  subst β
  rfl


end CategoryTheory
