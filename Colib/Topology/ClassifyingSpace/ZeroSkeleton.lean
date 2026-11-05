/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.Topology.ClassifyingSpace.Basic
public import Colib.Topology.Realization.ConstantIso
public import Colib.Topology.Realization.EdgePath
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
# The actual vertex skeleton of a nerve

The geometric realization of the actual zero-dimensional nerve skeleton is
canonically homeomorphic to the discrete original objects. Object and morphism
universes are independent, and the homeomorphism preserves actual vertices.

## Implementation provenance

The first thirteen declarations of
`Quillen/Topology/ClassifyingSpace/ZeroSkeleton.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual skeleton, vertex maps,
universe lifts, homeomorphism and all thirteen source proofs are retained.
Only namespace and dependency ownership change. The subsequent statement about
zero-dimensional homotopy classes is not included or assumed here.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite SSet
open scoped Simplicial Topology
universe u v
namespace CategoryTheory
variable {C : Type u} [Category.{v} C]

/-- Every simplex in the actual vertex skeleton is a constant chain. -/
theorem nerve_zeroSkeleton_constant {p : SimplexCategoryᵒᵖ}
    (s : (nerve C).obj p) (hs : s ∈ ((nerve C).skeleton 1).obj p) :
    s = (Functor.const (Fin (p.unop.len + 1))).obj (s.obj 0) := by
  simp only [SSet.skeleton, OrderHom.coe_mk, Subfunctor.iSup_obj,
    Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at hs
  obtain ⟨⟨n, hn⟩, x, hx, ⟨f⟩, rfl⟩ := hs
  have hn0 : n = 0 := by omega
  subst n
  obtain ⟨d, rfl⟩ := ComposableArrows.mk₀_surjective x
  rfl

/-- Every constant chain is a simplex of the actual vertex skeleton. -/
theorem nerve_constant_mem_zeroSkeleton (c : C) (p : SimplexCategoryᵒᵖ) :
    (Functor.const (Fin (p.unop.len + 1))).obj c ∈ ((nerve C).skeleton 1).obj p := by
  let α : op ⦋0⦌ ⟶ p := (SimplexCategory.const p.unop ⦋0⦌ 0).op
  exact ((nerve C).skeleton 1).map α
    ((nerve C).mem_skeleton (nerveVertex c) (by omega))

/-- Evaluation at the original object identifies the skeleton with a constant
simplicial set, using only the universe lift required by the nerve. -/
def nerveZeroSkeletonToConstant :
    ((nerve C).skeleton 1 : SSet.{max u v}) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{v} C) where
  app p := ↾fun x ↦ ULift.up (x.1.obj 0)
  naturality p q α := by
    ext x
    change ULift.up (((nerve C).map α x.1).obj 0) = ULift.up (x.1.obj 0)
    rw [nerve_zeroSkeleton_constant x.1 x.2]
    rfl

instance nerveZeroSkeletonToConstant_isIso : IsIso (nerveZeroSkeletonToConstant (C := C)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro p
  apply (isIso_iff_bijective _).2
  constructor
  · intro x y h
    apply Subtype.ext
    have he : x.1.obj 0 = y.1.obj 0 := congrArg ULift.down h
    exact (nerve_zeroSkeleton_constant x.1 x.2).trans
      ((congrArg (Functor.const (Fin (p.unop.len + 1))).obj he).trans
        (nerve_zeroSkeleton_constant y.1 y.2).symm)
  · intro c
    exact ⟨⟨(Functor.const (Fin (p.unop.len + 1))).obj c.down,
      nerve_constant_mem_zeroSkeleton c.down p⟩, rfl⟩

/-- The actual vertex skeleton is the constant simplicial set of original objects. -/
def nerveZeroSkeletonIso :
    ((nerve C).skeleton 1 : SSet.{max u v}) ≅
      (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{v} C) :=
  asIso (nerveZeroSkeletonToConstant (C := C))

/-- The actual realization vertex in the zero-dimensional skeleton. -/
def nerveZeroSkeletonPoint (c : C) : |((nerve C).skeleton 1 : SSet.{max u v})| :=
  realizationPoint ⟨nerveVertex c, (nerve C).mem_skeleton (nerveVertex c) (by omega)⟩

/-- The vertex skeleton realization, including its original topology, is discrete. -/
def nerveZeroSkeletonRealizationIso :
    SSet.toTop.obj ((nerve C).skeleton 1 : SSet.{max u v}) ≅
      TopCat.discrete.obj (ULift.{v} C) :=
  SSet.toTop.mapIso nerveZeroSkeletonIso ≪≫ SSet.constantRealizationIso (ULift.{v} C)

/-- The canonical realization isomorphism sends each actual vertex to its original object. -/
lemma nerveZeroSkeletonRealizationIso_point (c : C) :
    (nerveZeroSkeletonRealizationIso (C := C)).hom (nerveZeroSkeletonPoint c) =
      ULift.up c := by
  change (SSet.constantRealizationIso (ULift.{v} C)).hom
    (SSet.toTop.map nerveZeroSkeletonIso.hom
      (realizationPoint ⟨nerveVertex c, _⟩)) = _
  rw [realizationPoint_naturality]
  exact constantRealizationIso_point (ULift.{v} C) (ULift.up c)

/-- Removing the harmless universe lift gives a homeomorphism to the original objects. -/
def nerveZeroSkeletonHomeomorph :
    |((nerve C).skeleton 1 : SSet.{max u v})| ≃ₜ TopCat.discrete.obj C :=
  (TopCat.homeoOfIso (nerveZeroSkeletonRealizationIso (C := C))).trans
    { toEquiv := Equiv.ulift
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }

lemma nerveZeroSkeletonHomeomorph_point (c : C) :
    nerveZeroSkeletonHomeomorph (nerveZeroSkeletonPoint c) = c := by
  change ((nerveZeroSkeletonRealizationIso (C := C)).hom (nerveZeroSkeletonPoint c)).down = c
  rw [nerveZeroSkeletonRealizationIso_point]

/-- The inverse realizes the actual original vertex, with no choice of representative. -/
lemma nerveZeroSkeletonRealizationIso_inv_object (c : C) :
    (nerveZeroSkeletonRealizationIso (C := C)).inv (ULift.up c) =
      nerveZeroSkeletonPoint c := by
  rw [← nerveZeroSkeletonRealizationIso_point c]
  exact (TopCat.homeoOfIso (nerveZeroSkeletonRealizationIso (C := C))).symm_apply_apply _

lemma nerveZeroSkeletonHomeomorph_symm_object (c : C) :
    (nerveZeroSkeletonHomeomorph (C := C)).symm c = nerveZeroSkeletonPoint c := by
  apply (nerveZeroSkeletonHomeomorph (C := C)).injective
  rw [Homeomorph.apply_symm_apply, nerveZeroSkeletonHomeomorph_point]

/-- The skeleton inclusion preserves the actual original classifying-space vertex. -/
lemma nerveZeroSkeletonPoint_inclusion (c : C) :
    SSet.toTop.map ((nerve C).skeleton 1).ι (nerveZeroSkeletonPoint c) =
      classifyingSpacePoint c :=
  realizationPoint_naturality ((nerve C).skeleton 1).ι _

end CategoryTheory

attribute [colib_tag "COL-0161",
  colib_ref "WeibelKBook" "IV, Recipe 3.1.1 and Definition 3.1.4, pages 24-25"
    "background"
    "Actual vertex skeleton and discrete-object realization, not a path-component comparison"]
  CategoryTheory.nerveZeroSkeletonIso
  CategoryTheory.nerveZeroSkeletonRealizationIso
  CategoryTheory.nerveZeroSkeletonRealizationIso_point
  CategoryTheory.nerveZeroSkeletonHomeomorph
  CategoryTheory.nerveZeroSkeletonHomeomorph_point
  CategoryTheory.nerveZeroSkeletonRealizationIso_inv_object
  CategoryTheory.nerveZeroSkeletonHomeomorph_symm_object
  CategoryTheory.nerveZeroSkeletonPoint_inclusion
