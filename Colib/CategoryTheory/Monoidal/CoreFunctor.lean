/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Monoidal.Core
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
Implementation provenance:
`Quillen/Aglib/CategoryTheory/Monoidal/CoreFunctor.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Strong monoidal functors on the original categorical cores

An original strong monoidal functor induces a strong monoidal functor on
mathlib's cores. Its unit and tensor comparisons are the same isomorphisms,
regarded as arrows in the cores; original coherence is reflected by inclusion.
-/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u v u' v'
namespace CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]

/-- The original comparison isomorphisms, regarded in the actual categorical cores. -/
def coreMonoidalData (F : C ⥤ D) [F.Monoidal] : F.core.CoreMonoidal where
  εIso := Core.isoMk (Functor.Monoidal.εIso F)
  μIso X Y := Core.isoMk (Functor.Monoidal.μIso F X.of Y.of)
  μIso_hom_natural_left f X := by
    apply Core.hom_ext
    exact Functor.LaxMonoidal.μ_natural_left F f.iso.hom X.of
  μIso_hom_natural_right X f := by
    apply Core.hom_ext
    exact Functor.LaxMonoidal.μ_natural_right F X.of f.iso.hom
  associativity X Y Z := by
    apply Core.hom_ext
    exact Functor.LaxMonoidal.associativity F X.of Y.of Z.of
  left_unitality X := by
    apply Core.hom_ext
    exact Functor.LaxMonoidal.left_unitality F X.of
  right_unitality X := by
    apply Core.hom_ext
    exact Functor.LaxMonoidal.right_unitality F X.of

/-- Passing to the original cores preserves strong monoidal structure. -/
instance coreMonoidal (F : C ⥤ D) [F.Monoidal] : F.core.Monoidal :=
  (coreMonoidalData F).toMonoidal

/-- The core unit comparison has exactly the original underlying morphism. -/
lemma core_ε_hom (F : C ⥤ D) [F.Monoidal] :
    (Functor.LaxMonoidal.ε F.core).iso.hom = Functor.LaxMonoidal.ε F := rfl

/-- The core tensor comparison has exactly the original underlying morphism. -/
lemma core_μ_hom (F : C ⥤ D) [F.Monoidal] (X Y : Core C) :
    (Functor.LaxMonoidal.μ F.core X Y).iso.hom =
      Functor.LaxMonoidal.μ F X.of Y.of := rfl

/-- Original braided coherence is retained by the core lift. -/
instance coreBraided [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.Braided] : F.core.Braided where
  braided X Y := by
    apply Core.hom_ext
    exact Functor.LaxBraided.braided (F := F) X.of Y.of

/-- A genuine monoidal natural isomorphism induces one on the original cores. -/
instance coreNatIso_isMonoidal {F G : C ⥤ D} [F.Monoidal] [G.Monoidal]
    (α : F ≅ G) [α.hom.IsMonoidal] : α.core.hom.IsMonoidal where
  unit := by
    apply Core.hom_ext
    exact NatTrans.IsMonoidal.unit (τ := α.hom)
  tensor X Y := by
    apply Core.hom_ext
    exact NatTrans.IsMonoidal.tensor (τ := α.hom) X.of Y.of

/-- The original identity-core comparison is monoidal for the inherited data. -/
instance coreId_isMonoidal : (Functor.coreId C).hom.IsMonoidal where
  unit := by
    apply Core.hom_ext
    change (𝟙 (𝟙_ C)) ≫ 𝟙 _ = 𝟙 _
    simp
  tensor X Y := by
    apply Core.hom_ext
    change (𝟙 (X.of ⊗ Y.of)) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _
    simp

/-- The original composite-core comparison is monoidal for the inherited data. -/
instance coreComp_isMonoidal {E : Type*} [Category* E] [MonoidalCategory E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Monoidal] [G.Monoidal] :
    (Functor.coreComp F G).hom.IsMonoidal where
  unit := by
    apply Core.hom_ext
    change Functor.LaxMonoidal.ε (F ⋙ G) ≫ 𝟙 _ =
      Functor.LaxMonoidal.ε G ≫ G.map (Functor.LaxMonoidal.ε F)
    simp
  tensor X Y := by
    apply Core.hom_ext
    change Functor.LaxMonoidal.μ (F ⋙ G) X.of Y.of ≫ 𝟙 _ =
      (𝟙 _ ⊗ₘ 𝟙 _) ≫ Functor.LaxMonoidal.μ G (F.obj X.of) (F.obj Y.of) ≫
        G.map (Functor.LaxMonoidal.μ F X.of Y.of)
    simp

end CategoryTheory.Functor
