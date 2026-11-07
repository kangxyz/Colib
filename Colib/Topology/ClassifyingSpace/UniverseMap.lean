/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.DescAcross
public import Colib.Topology.ClassifyingSpace.Map

/-!
# Original classifying-space maps across independent universes

Postcomposition on each native nerve simplex descends directly to the original
geometric realization. The map retains every simplex coordinate and vertex,
agrees with the existing map in common universes, and preserves composition.
No additional simplicial-map structure or common-universe realization is used.

Implementation correspondence: `Quillen/Topology/ClassifyingSpace/UniverseMap.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, directly using native colimit descent.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite SSet
open scoped Simplicial Topology
universe u₁ v₁ u₂ v₂ u₃ v₃
namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- The continuous map of the original realizations induced by an arbitrary-universe functor. -/
def classifyingSpaceMapUniversal (F : C ⥤ D) :
    C(ClassifyingSpace C, ClassifyingSpace D) :=
  realizationDesc (X := nerve C)
    (fun n x ↦ realizationSimplex (X := nerve D) (n := n) (x ⋙ F)) (by
      intro n m a x t
      exact realizationSimplex_naturality (X := nerve D) a (x ⋙ F) t)

@[simp] theorem classifyingSpaceMapUniversal_simplex (F : C ⥤ D)
    (n : SimplexCategory) (x : (nerve C).obj (op n))
    (t : _root_.stdSimplex ℝ (Fin (n.len + 1))) :
    classifyingSpaceMapUniversal F (realizationSimplex x t) =
      realizationSimplex (x ⋙ F) t :=
  realizationDesc_simplex _
    (fun a x t ↦ realizationSimplex_naturality (X := nerve D) a (x ⋙ F) t) n x t

/-- Postcomposition retains the original object vertex exactly. -/
@[simp] theorem classifyingSpaceMapUniversal_point (F : C ⥤ D) (c : C) :
    classifyingSpaceMapUniversal F (classifyingSpacePoint c) =
      classifyingSpacePoint (F.obj c) := by
  change classifyingSpaceMapUniversal F (realizationPoint (nerveVertex c)) = _
  rw [← realizationSimplex_zero (nerveVertex c) default,
    classifyingSpaceMapUniversal_simplex, realizationSimplex_zero]
  exact congrArg realizationPoint (ComposableArrows.ext₀ rfl)

theorem classifyingSpaceMapUniversal_id :
    classifyingSpaceMapUniversal (𝟭 C) = ContinuousMap.id (ClassifyingSpace C) := by
  apply DFunLike.coe_injective
  apply realization_ext
  intro n x t
  simp only [classifyingSpaceMapUniversal_simplex, ContinuousMap.id_apply]
  rfl

@[simp] theorem classifyingSpaceMapUniversal_comp (F : C ⥤ D) (G : D ⥤ E) :
    classifyingSpaceMapUniversal (F ⋙ G) =
      (classifyingSpaceMapUniversal G).comp (classifyingSpaceMapUniversal F) := by
  apply DFunLike.coe_injective
  apply realization_ext
  intro n x t
  simp only [classifyingSpaceMapUniversal_simplex, ContinuousMap.comp_apply]
  rfl

/-- In common universes this is exactly the existing classifying-space map. -/
@[simp] theorem classifyingSpaceMapUniversal_eq {C D : Type u₁}
    [Category.{v₁} C] [Category.{v₁} D] (F : C ⥤ D) :
    classifyingSpaceMapUniversal F = (classifyingSpaceMap F).hom := by
  apply DFunLike.coe_injective
  apply realization_ext
  intro n x t
  rw [classifyingSpaceMapUniversal_simplex]
  change SSet.toTop.map (SSet.yonedaEquiv.symm (x ⋙ F))
    ((SimplexCategory.toTopHomeo n).symm t) =
      (SSet.toTop.map (SSet.yonedaEquiv.symm x) ≫ SSet.toTop.map (nerveMap F))
        ((SimplexCategory.toTopHomeo n).symm t)
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_comp]
  rfl

end CategoryTheory
