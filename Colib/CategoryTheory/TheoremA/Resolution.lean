/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.Adjunction
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Grothendieck

/-! Source: `Quillen/CategoryTheory/TheoremA/Resolution.lean` at
c561118b7795eb9780be9ed391c3251d6a4d0afd.
This is a categorical/realized resolution prerequisite, not the general Theorem A criterion. -/

/-!
# The categorical resolution used in Quillen's Theorem A

For a functor `F : C ⥤ D`, the resolution has objects `(c, d, F c ⟶ d)`.
Its projection to `C` has a fully faithful left adjoint, and consequently is
already a homotopy equivalence after taking nerves and realization. The other
projection has comma categories `(F ↓ d)` as its strict fibers.

This file proves the categorical and simplicial assertions, including the
identification with the Grothendieck construction of `d ↦ (F ↓ d)`. It does
not assert that fiberwise contractibility makes the second projection a
homotopy equivalence: that is the additional homotopy-colimit theorem needed
for the general Theorem A criterion.
-/
@[expose] public section

noncomputable section

open CategoryTheory
open scoped Simplicial

universe u

namespace CategoryTheory.TheoremA

variable {C D : Type u} [SmallCategory C] [SmallCategory D] (F : C ⥤ D)

/-- The comma resolution of a functor, with arrows oriented `F c ⟶ d`. -/
abbrev Resolution := Comma F (𝟭 D)

/-- The projection to the source category. -/
abbrev sourceProjection : Resolution F ⥤ C := Comma.fst F (𝟭 D)

/-- The projection to the target category. Its fibers are `(F ↓ d)`. -/
abbrev targetProjection : Resolution F ⥤ D := Comma.snd F (𝟭 D)

/-- The identity-arrow section of the source projection. -/
@[simps]
def sectionFunctor : C ⥤ Resolution F where
  obj c := ⟨c, F.obj c, 𝟙 _⟩
  map f := ⟨f, F.map f, by simp⟩

@[simp]
theorem section_source : sectionFunctor F ⋙ sourceProjection F = 𝟭 C := rfl

@[simp]
theorem section_target : sectionFunctor F ⋙ targetProjection F = F := rfl

/-- The contraction of the resolution toward its identity-arrow section. -/
@[simps]
def contraction : sourceProjection F ⋙ sectionFunctor F ⟶ 𝟭 (Resolution F) where
  app X := ⟨𝟙 X.left, X.hom, by simp [sectionFunctor]⟩
  naturality X Y f := by
    apply Comma.hom_ext
    · change f.left ≫ 𝟙 Y.left = 𝟙 X.left ≫ f.left
      simp
    · exact f.w

/-- The source projection is right adjoint to its identity-arrow section. -/
def sectionAdjunction : sectionFunctor F ⊣ sourceProjection F :=
  Adjunction.mkOfUnitCounit {
    unit := { app := fun c ↦ 𝟙 c }
    counit := contraction F
    left_triangle := by
      ext c <;> simp [contraction, sectionFunctor]
    right_triangle := by
      ext X
      simp [contraction, sectionFunctor] }

/-- The structure arrow gives the canonical comparison with `F`. -/
@[simps]
def comparison : sourceProjection F ⋙ F ⟶ targetProjection F where
  app X := X.hom
  naturality _ _ f := f.w

/-- An explicit simplicial homotopy contracting the resolution onto `C`. -/
def contractionNerveHomotopy :
    SSet.Homotopy (nerveMap (sourceProjection F) ≫ nerveMap (sectionFunctor F))
      (𝟙 (nerve (Resolution F))) :=
  naturalTransformationNerveHomotopy (contraction F)

/-- The resolved factorization agrees with the canonical nerve map up to the
homotopy supplied by each resolution object's structure arrow. -/
def comparisonNerveHomotopy :
    SSet.Homotopy (nerveMap (sourceProjection F) ≫ nerveMap F)
      (nerveMap (targetProjection F)) :=
  naturalTransformationNerveHomotopy (comparison F)

/-- The inclusion of `(F ↓ d)` into the resolution over `d`. -/
@[simps]
def fiberInclusion (d : D) : CostructuredArrow F d ⥤ Resolution F where
  obj X := ⟨X.left, d, X.hom⟩
  map f := ⟨f.left, 𝟙 d, by simp⟩

@[simp]
theorem fiberInclusion_source (d : D) :
    fiberInclusion F d ⋙ sourceProjection F = CostructuredArrow.proj F d := rfl

@[simp]
theorem fiberInclusion_target (d : D) :
    fiberInclusion F d ⋙ targetProjection F =
      (Functor.const (CostructuredArrow F d)).obj d := rfl

/-- Covariant change of the target in `(F ↓ d)`, with its comparison arrow
in the total resolution. This fixes the variance in the Theorem A criterion. -/
@[simps]
def fiberTransport {d e : D} (f : d ⟶ e) :
    fiberInclusion F d ⟶ CostructuredArrow.map f ⋙ fiberInclusion F e where
  app X := ⟨𝟙 X.left, f, by
    change F.map (𝟙 X.left) ≫ (X.hom ≫ f) = X.hom ≫ f
    simp⟩
  naturality X Y g := by
    apply Comma.hom_ext
    · change g.left ≫ 𝟙 Y.left = 𝟙 X.left ≫ g.left
      simp
    · change 𝟙 d ≫ f = f ≫ 𝟙 e
      simp

end CategoryTheory.TheoremA
