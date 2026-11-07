/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Realization.ConstantIso
public import Colib.Topology.Realization.EdgePath
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-! # The actual vertex skeleton of an arbitrary simplicial set

Evaluation at vertex zero identifies the actual zero-dimensional skeleton
with the constant simplicial set on the original vertices. Realization gives
a homeomorphism to their discrete space, preserving every original vertex.
-/
/-!
## Implementation provenance

Adapted from `Quillen/Topology/Realization/ZeroSkeleton.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, vertex and edge
identifications, path classes, proofs and universe parameters are retained.
Native namespace ownership and the pinned standard simplex replace source ownership.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u
namespace SSet
variable (X : SSet.{u})

/-- The original zero-th vertex of an arbitrary simplex. -/
def simplexVertexZero {p : SimplexCategoryᵒᵖ} (x : X.obj p) : X _⦋0⦌ :=
  X.map (SimplexCategory.const ⦋0⦌ p.unop 0).op x

/-- The original constant simplex at a specified vertex. -/
def constantVertexSimplex (x : X _⦋0⦌) (p : SimplexCategoryᵒᵖ) : X.obj p :=
  X.map (SimplexCategory.const p.unop ⦋0⦌ 0).op x

/-- Every simplex in the actual zero-skeleton is constant at its original vertex. -/
theorem zeroSkeleton_constant {p : SimplexCategoryᵒᵖ}
    (x : X.obj p) (hx : x ∈ (X.skeleton 1).obj p) :
    x = constantVertexSimplex X (simplexVertexZero X x) p := by
  simp only [SSet.skeleton, OrderHom.coe_mk, Subfunctor.iSup_obj,
    Set.iUnion_coe_set, Set.mem_iUnion, exists_prop] at hx
  obtain ⟨⟨n, hn⟩, y, hy, ⟨f⟩, rfl⟩ := hx
  have hn0 : n = 0 := by omega
  subst n
  dsimp only [constantVertexSimplex, simplexVertexZero]
  rw [← ConcreteCategory.comp_apply, ← X.map_comp,
    ← ConcreteCategory.comp_apply, ← X.map_comp]
  congr 3
  apply Quiver.Hom.unop_inj
  exact Subsingleton.elim _ _

/-- Original constant vertex simplices belong to the actual vertex skeleton. -/
theorem constantVertexSimplex_mem_zeroSkeleton (x : X _⦋0⦌) (p : SimplexCategoryᵒᵖ) :
    constantVertexSimplex X x p ∈ (X.skeleton 1).obj p :=
  (X.skeleton 1).map _ (X.mem_skeleton x (by omega))

/-- Evaluating an original constant simplex recovers its original vertex. -/
@[simp] theorem simplexVertexZero_constantVertexSimplex (x : X _⦋0⦌)
    (p : SimplexCategoryᵒᵖ) :
    simplexVertexZero X (constantVertexSimplex X x p) = x := by
  dsimp only [constantVertexSimplex, simplexVertexZero]
  rw [← ConcreteCategory.comp_apply, ← X.map_comp]
  have h : (SimplexCategory.const p.unop ⦋0⦌ 0).op ≫
      (SimplexCategory.const ⦋0⦌ p.unop 0).op = 𝟙 (op ⦋0⦌) := by
    apply Quiver.Hom.unop_inj
    exact Subsingleton.elim _ _
  rw [h, X.map_id]
  rfl

/-- Evaluation identifies the actual vertex skeleton with the original constant vertex set. -/
def zeroSkeletonToConstant : (X.skeleton 1 : SSet.{u}) ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (X _⦋0⦌) where
  app _ := ↾fun x ↦ simplexVertexZero X x.1
  naturality p q α := by
    ext x
    change simplexVertexZero X (X.map α x.1) = simplexVertexZero X x.1
    rw [zeroSkeleton_constant X x.1 x.2]
    dsimp only [constantVertexSimplex, simplexVertexZero]
    simp only [← ConcreteCategory.comp_apply, ← X.map_comp]
    congr 2

instance zeroSkeletonToConstant_isIso : IsIso (zeroSkeletonToConstant X) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro p
  apply (isIso_iff_bijective _).2
  constructor
  · intro x y h
    apply Subtype.ext
    exact (zeroSkeleton_constant X x.1 x.2).trans
      ((congrArg (fun z ↦ constantVertexSimplex X z p) h).trans
        (zeroSkeleton_constant X y.1 y.2).symm)
  · intro x
    exact ⟨⟨constantVertexSimplex X x p, constantVertexSimplex_mem_zeroSkeleton X x p⟩,
      simplexVertexZero_constantVertexSimplex X x p⟩

/-- The original zero-skeleton as the constant simplicial set of original vertices. -/
def zeroSkeletonIso : (X.skeleton 1 : SSet.{u}) ≅
    (Functor.const SimplexCategoryᵒᵖ).obj (X _⦋0⦌) := asIso (zeroSkeletonToConstant X)

/-- The original vertex viewed as a point of the actual vertex skeleton. -/
def zeroSkeletonPoint (x : X _⦋0⦌) : |(X.skeleton 1 : SSet.{u})| :=
  realizationPoint ⟨x, X.mem_skeleton x (by omega)⟩

/-- The actual vertex skeleton has exactly the discrete topology of original vertices. -/
def zeroSkeletonRealizationIso : SSet.toTop.obj (X.skeleton 1 : SSet.{u}) ≅
    TopCat.discrete.obj (X _⦋0⦌) :=
  SSet.toTop.mapIso (zeroSkeletonIso X) ≪≫ constantRealizationIso (X _⦋0⦌)

/-- The actual realized vertex is sent to its unchanged original vertex. -/
@[simp] theorem zeroSkeletonRealizationIso_point (x : X _⦋0⦌) :
    (zeroSkeletonRealizationIso X).hom (zeroSkeletonPoint X x) = x := by
  change (constantRealizationIso (X _⦋0⦌)).hom
    (SSet.toTop.map (zeroSkeletonIso X).hom (realizationPoint ⟨x, _⟩)) = _
  rw [realizationPoint_naturality]
  have h : simplexVertexZero X x = x := by
    change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op x = x
    rw [SimplexCategory.const_eq_id, op_id, X.map_id]
    rfl
  exact (constantRealizationIso_point (X _⦋0⦌) _).trans h

/-- The corresponding actual homeomorphism, with its unchanged forward vertex map. -/
def zeroSkeletonHomeomorph : |(X.skeleton 1 : SSet.{u})| ≃ₜ
    TopCat.discrete.obj (X _⦋0⦌) := TopCat.homeoOfIso (zeroSkeletonRealizationIso X)

/-- Original vertices are precisely the inverse images under the actual homeomorphism. -/
@[simp] theorem zeroSkeletonHomeomorph_symm_vertex (x : X _⦋0⦌) :
    (zeroSkeletonHomeomorph X).symm x = zeroSkeletonPoint X x := by
  apply (zeroSkeletonHomeomorph X).injective
  exact ((zeroSkeletonHomeomorph X).apply_symm_apply x).trans
    (zeroSkeletonRealizationIso_point X x).symm

/-- The original skeleton inclusion preserves the actual original vertex point. -/
theorem zeroSkeletonPoint_inclusion (x : X _⦋0⦌) :
    SSet.toTop.map (X.skeleton 1).ι (zeroSkeletonPoint X x) = realizationPoint x :=
  realizationPoint_naturality (X.skeleton 1).ι _

end SSet
