/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.Resolution

/-! Source: `Quillen/CategoryTheory/TheoremA/StructuredResolution.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd.
This is a categorical/realized resolution prerequisite, not the general Theorem A criterion. -/

/-!
# The structured-arrow orientation of the Theorem A resolution

For the criterion using `(d ↓ F)`, the resolution uses arrows `d ⟶ F c`.
The identity-arrow section is now a right adjoint, and change of `d` in the
comma category is contravariant. These variance choices are explicit rather
than silently identifying structured with costructured arrows.
-/
@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace CategoryTheory.TheoremA.Structured

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The dual resolution, with arrows oriented `d ⟶ F c`. -/
abbrev Resolution := Comma (𝟭 D) F

/-- Projection to the source of `F`. -/
abbrev sourceProjection : Resolution F ⥤ C := Comma.snd (𝟭 D) F

/-- Projection to the target of `F`. -/
abbrev targetProjection : Resolution F ⥤ D := Comma.fst (𝟭 D) F

/-- The identity-arrow section. -/
@[simps]
def sectionFunctor : C ⥤ Resolution F where
  obj c := ⟨F.obj c, c, 𝟙 _⟩
  map f := ⟨F.map f, f, by simp⟩

@[simp]
theorem section_source : sectionFunctor F ⋙ sourceProjection F = 𝟭 C := rfl

@[simp]
theorem section_target : sectionFunctor F ⋙ targetProjection F = F := rfl

/-- The contraction is oriented from each resolution object toward its section. -/
@[simps]
def contraction : 𝟭 (Resolution F) ⟶ sourceProjection F ⋙ sectionFunctor F where
  app X := ⟨X.hom, 𝟙 X.right, by simp [sectionFunctor]⟩
  naturality X Y f := by
    apply Comma.hom_ext
    · exact f.w
    · change f.right ≫ 𝟙 Y.right = 𝟙 X.right ≫ f.right
      simp

/-- The source projection is left adjoint to the identity-arrow section. -/
def sectionAdjunction : sourceProjection F ⊣ sectionFunctor F :=
  Adjunction.mkOfUnitCounit {
    unit := contraction F
    counit := { app := fun c ↦ 𝟙 c }
    left_triangle := by
      ext X
      simp [contraction, sectionFunctor]
    right_triangle := by
      ext c <;> simp [contraction, sectionFunctor] }

/-- The structure arrows compare the target projection with the composite through `F`. -/
@[simps]
def comparison : targetProjection F ⟶ sourceProjection F ⋙ F where
  app X := X.hom
  naturality _ _ f := f.w

/-- The structured resolution has a genuine simplicial deformation retraction. -/
def contractionNerveHomotopy :
    SSet.Homotopy (𝟙 (nerve (Resolution F)))
      (nerveMap (sourceProjection F) ≫ nerveMap (sectionFunctor F)) :=
  naturalTransformationNerveHomotopy (contraction F)

/-- Its canonical comparison with the map induced by `F`. -/
def comparisonNerveHomotopy :
    SSet.Homotopy (nerveMap (targetProjection F))
      (nerveMap (sourceProjection F) ≫ nerveMap F) :=
  naturalTransformationNerveHomotopy (comparison F)

/-- The structured-arrow category included over its fixed source `d`. -/
@[simps]
def fiberInclusion (d : D) : StructuredArrow d F ⥤ Resolution F where
  obj X := ⟨d, X.right, X.hom⟩
  map f := ⟨𝟙 d, f.right, by simp⟩

@[simp]
theorem fiberInclusion_source (d : D) :
    fiberInclusion F d ⋙ sourceProjection F = StructuredArrow.proj d F := rfl

@[simp]
theorem fiberInclusion_target (d : D) :
    fiberInclusion F d ⋙ targetProjection F =
      (Functor.const (StructuredArrow d F)).obj d := rfl

/-- Contravariant change of the source in `(d ↓ F)`, with its comparison
arrow in the total resolution. -/
@[simps]
def fiberTransport {d e : D} (f : d ⟶ e) :
    StructuredArrow.map f ⋙ fiberInclusion F d ⟶ fiberInclusion F e where
  app X := ⟨f, 𝟙 X.right, by
    change f ≫ X.hom = (f ≫ X.hom) ≫ F.map (𝟙 X.right)
    simp⟩
  naturality X Y g := by
    apply Comma.hom_ext
    · change 𝟙 d ≫ f = f ≫ 𝟙 e
      simp
    · change g.right ≫ 𝟙 Y.right = 𝟙 X.right ≫ g.right
      simp

end CategoryTheory.TheoremA.Structured
