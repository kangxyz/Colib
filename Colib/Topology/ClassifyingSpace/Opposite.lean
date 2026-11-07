/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.ClassifyingSpace.NerveOpposite
public import Colib.Topology.Realization.Opposite

/-! The classifying spaces of a category and its opposite agree naturally,
by actual reversal of nerve chains and topological simplex coordinates. -/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Reversing nerve chains is natural in the original functor. -/
theorem nerveOppositeIso_naturality (F : C ⥤ D) :
    SSet.opFunctor.map (nerveMap F) ≫ (nerveOppositeIso (C := D)).hom =
      (nerveOppositeIso (C := C)).hom ≫ nerveMap F.op := by
  ext p c : 4
  refine CategoryTheory.Functor.hext (fun i ↦ rfl) ?_
  intro i j f
  rfl

/-- Natural topological identification of opposite classifying spaces. -/
def classifyingOppositeIso (C : Type u) [Category.{v} C] :
    ClassifyingSpace Cᵒᵖ ≅ ClassifyingSpace C :=
  (SSet.toTop.mapIso (nerveOppositeIso (C := C))).symm ≪≫
    SSet.realizationOppositeNatIso.app (nerve C)

/-- Opposite realization retains the exact map of classifying spaces. -/
theorem classifyingOppositeIso_naturality (F : C ⥤ D) :
    classifyingSpaceMap F.op ≫ (classifyingOppositeIso D).hom =
      (classifyingOppositeIso C).hom ≫ classifyingSpaceMap F := by
  have h := congrArg SSet.toTop.map (nerveOppositeIso_naturality F)
  simp only [Functor.map_comp] at h
  have h₁ : classifyingSpaceMap F.op ≫
      SSet.toTop.map (nerveOppositeIso (C := D)).inv =
      SSet.toTop.map (nerveOppositeIso (C := C)).inv ≫
        SSet.toTop.map (SSet.opFunctor.map (nerveMap F)) := by
    exact (CommSq.vert_inv
      (g := SSet.toTop.mapIso (nerveOppositeIso (C := C)))
      (h := SSet.toTop.mapIso (nerveOppositeIso (C := D))) (CommSq.mk h)).w
  have h₂ := SSet.realizationOppositeNatIso.hom.naturality (nerveMap F)
  exact ((CommSq.mk h₁).vert_comp (CommSq.mk h₂)).w

end CategoryTheory
