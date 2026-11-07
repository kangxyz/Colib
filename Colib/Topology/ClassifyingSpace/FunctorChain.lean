/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.ProductSimplex
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import Colib.Topology.ClassifyingSpace.Naturality

/-!
# Realized functor chains and triangle coherence

Implementation source: `Quillen/CategoryTheory/TheoremB/StructuredIsoHomotopy.lean` and
`Quillen/Topology/ClassifyingSpace/FunctorChain.lean`
at c561118b7795eb9780be9ed391c3251d6a4d0afd. Actual simplex families,
path coordinates, and endpoint data are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Convexity Topology CategoryTheory SSet Opposite MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory
variable {C D : Type u} [SmallCategory C] [SmallCategory D]

/-- A chain of functors and natural transformations gives its actual simplex family. -/
def functorChainNerveCylinder {n : ℕ} (A : ComposableArrows (C ⥤ D) n) :
    nerve C ⊗ Δ[n] ⟶ nerve D where
  app k := ↾fun z ↦
    (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙ Functor.uncurry.obj A
  naturality _ _ _ := by ext z; rfl

@[simp] theorem functorChainNerveCylinder_one {F G : C ⥤ D} (α : F ⟶ G) :
    functorChainNerveCylinder (ComposableArrows.mk₁ α) =
      naturalTransformationNerveCylinder α := rfl

/-- Restricting the parameter simplex restricts the chain of transformations. -/
theorem functorChainNerveCylinder_precomp {n m : ℕ}
    (A : ComposableArrows (C ⥤ D) n) (f : ⦋m⦌ ⟶ ⦋n⦌) :
    ((𝟙 (nerve C)) ⊗ₘ SSet.stdSimplex.map f) ≫ functorChainNerveCylinder A =
      functorChainNerveCylinder (f.toOrderHom.monotone.functor ⋙ A) := by
  ext k z : 4
  rfl

/-- The complete continuous simplex family over the source classifying space. -/
def functorChainRealization {n : ℕ} (A : ComposableArrows (C ⥤ D) n) :
    C(ClassifyingSpace C × |(Δ[n] : SSet.{u})|, ClassifyingSpace D) :=
  (SSet.toTop.map (functorChainNerveCylinder A)).hom.comp
    (realizationProductSimplexIso (nerve C) n).inv.hom

/-- Naturality of inverse product-with-simplex realization. -/
@[reassoc] theorem realizationProductSimplexIso_inv_naturality {X Y : SSet.{u}}
    (f : X ⟶ Y) {m n : ℕ} (g : ⦋m⦌ ⟶ ⦋n⦌) :
    (realizationProductSimplexIso X m).inv ≫ SSet.toTop.map (f ⊗ₘ SSet.stdSimplex.map g) =
      (SSet.toTop.map f ⊗ₘ SSet.toTop.map (SSet.stdSimplex.map g)) ≫
        (realizationProductSimplexIso Y n).inv :=
  (CommSq.vert_inv (CommSq.mk (realizationProductSimplexIso_naturality f g))).w.symm

/-- Restriction of a realized simplex family agrees exactly with the realized subchain. -/
theorem functorChainRealization_precomp {n m : ℕ}
    (A : ComposableArrows (C ⥤ D) n) (f : ⦋m⦌ ⟶ ⦋n⦌)
    (x : ClassifyingSpace C) (z : |(Δ[m] : SSet.{u})|) :
    functorChainRealization A (x, SSet.toTop.map (SSet.stdSimplex.map f) z) =
      functorChainRealization (f.toOrderHom.monotone.functor ⋙ A) (x, z) := by
  have h := realizationProductSimplexIso_inv_naturality (𝟙 (nerve C)) f
  have hp := ConcreteCategory.congr_hom h (x, z)
  change SSet.toTop.map (functorChainNerveCylinder A)
    ((realizationProductSimplexIso (nerve C) n).inv
      (x, SSet.toTop.map (SSet.stdSimplex.map f) z)) = _
  have hv : (SSet.toTop.map (𝟙 (nerve C)) ⊗ₘ SSet.toTop.map (SSet.stdSimplex.map f))
      (x, z) = (x, SSet.toTop.map (SSet.stdSimplex.map f) z) := by simp
  rw [TopCat.comp_app, TopCat.comp_app, hv] at hp
  rw [← hp]
  change (SSet.toTop.map ((𝟙 (nerve C)) ⊗ₘ SSet.stdSimplex.map f) ≫
    SSet.toTop.map (functorChainNerveCylinder A)) _ = _
  rw [← SSet.toTop.map_comp, functorChainNerveCylinder_precomp]
  rfl
/-- At dimension one, the product-simplex and interval-cylinder comparisons agree. -/
theorem realizationProductSimplexIso_one (X : SSet.{u}) :
    (realizationProductSimplexIso X 1).hom ≫
      (|X| ◁ SSet.stdSimplex.toTopObjIsoI.hom) = (realizationCylinderIso X).hom := by
  change prodComparison SSet.toTop X Δ[1] ≫
      (|X| ◁ SSet.stdSimplex.toTopObjIsoI.hom) = realizationCylinderComparison X
  apply CartesianMonoidalCategory.hom_ext <;>
    simp [realizationCylinderComparison]

theorem realizationProductSimplexIso_one_inv (X : SSet.{u}) :
    (|X| ◁ SSet.stdSimplex.toTopObjIsoI.inv) ≫
      (realizationProductSimplexIso X 1).inv = (realizationCylinderIso X).inv := by
  have he : realizationProductSimplexIso X 1 ≪≫
      MonoidalCategory.whiskerLeftIso |X| SSet.stdSimplex.toTopObjIsoI = realizationCylinderIso X :=
    Iso.ext (realizationProductSimplexIso_one X)
  exact congrArg Iso.inv he

/-- The one-simplex family is exactly the already defined transformation homotopy. -/
theorem functorChainRealization_one {F G : C ⥤ D} (α : F ⟶ G)
    (x : ClassifyingSpace C) (t : unitInterval) :
    functorChainRealization (ComposableArrows.mk₁ α) (x, realizationInterval t) =
      classifyingSpaceNaturalTransformationHomotopy α (t, x) := by
  have hp := ConcreteCategory.congr_hom (realizationProductSimplexIso_one_inv (nerve C))
    (x, ULift.up t)
  exact congrArg (SSet.toTop.map (naturalTransformationNerveCylinder α)) hp

/-- The three edges of a realized chain of two transformations. -/
theorem functorChainRealization_two_face {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (i : Fin 3) (x : ClassifyingSpace C) (t : unitInterval) :
    functorChainRealization (ComposableArrows.mk₂ α β)
      (x, SSet.toTop.map (SSet.stdSimplex.δ i) (realizationInterval t)) =
    functorChainRealization ((nerve (C ⥤ D)).δ i (ComposableArrows.mk₂ α β))
      (x, realizationInterval t) :=
  functorChainRealization_precomp _ (SimplexCategory.δ i) x _

/-- The realized homotopy of the identity transformation is constant at every source point. -/
theorem classifyingHomotopy_id (F : C ⥤ D) (x : ClassifyingSpace C) (t : unitInterval) :
    classifyingSpaceNaturalTransformationHomotopy (𝟙 F) (t, x) = classifyingSpaceMap F x := by
  have he : naturalTransformationCylinderFunctor (𝟙 F) =
      CategoryTheory.Prod.snd (Fin 2) C ⋙ F := by
    refine CategoryTheory.Functor.hext (fun X ↦ ?_) ?_
    · rcases X with ⟨i, x⟩
      fin_cases i <;> rfl
    · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨f, g⟩
      have hij := leOfHom f
      fin_cases i <;> fin_cases j
      · simp [naturalTransformationCylinderFunctor, Functor.uncurry, ComposableArrows.mk₁]
      · simp [naturalTransformationCylinderFunctor, Functor.uncurry, ComposableArrows.mk₁]
      · exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) hij |>.elim
      · simp [naturalTransformationCylinderFunctor, Functor.uncurry, ComposableArrows.mk₁]
  have hc : naturalTransformationNerveCylinder (𝟙 F) =
      fst (nerve C) Δ[1] ≫ nerveMap F := by
    ext n z : 4
    change _ ⋙ naturalTransformationCylinderFunctor (𝟙 F) = _
    rw [he]
    rfl
  change SSet.toTop.map (naturalTransformationNerveCylinder (𝟙 F))
    ((realizationCylinderIso (nerve C)).inv (x, ULift.up t)) = _
  rw [hc, SSet.toTop.map_comp, TopCat.comp_app]
  have hp := congrArg _root_.Prod.fst (ConcreteCategory.congr_hom
    (realizationCylinderIso (nerve C)).inv_hom_id (x, ULift.up t))
  exact congrArg (classifyingSpaceMap F) hp
/-- The family in ordinary barycentric simplex coordinates. -/
def functorChainBarycentric {n : ℕ} (A : ComposableArrows (C ⥤ D) n) :
    C(ClassifyingSpace C × Convexity.StdSimplex ℝ (Fin (n + 1)), ClassifyingSpace D) where
  toFun z := functorChainRealization A
    (z.1, (SimplexCategory.toTopHomeo ⦋n⦌).symm z.2)
  continuous_toFun := by fun_prop

private theorem simplexRealization_map {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (z : Convexity.StdSimplex ℝ (Fin (m + 1))) :
    SSet.toTop.map (SSet.stdSimplex.map f) ((SimplexCategory.toTopHomeo ⦋m⦌).symm z) =
      (SimplexCategory.toTopHomeo ⦋n⦌).symm (Convexity.StdSimplex.map f.toOrderHom z) :=
  (SimplexCategory.toTopHomeo_symm_naturality_apply f z).symm

/-- The affine edge between two chosen triangle vertices. -/
def triangleEdge (i j : Fin 3) (t : unitInterval) : StdSimplex ℝ (Fin 3) :=
  StdSimplex.duple i j (unitInterval.nonneg (unitInterval.symm t))
    (unitInterval.nonneg t) (by simp)

@[fun_prop] theorem continuous_triangleEdge (i j : Fin 3) : Continuous (triangleEdge i j) :=
  StdSimplex.continuous_duple i j

/-- The edge retains the original ordered endpoint weights. -/
@[simp] theorem triangleEdge_apply (i j k : Fin 3) (t : unitInterval) :
    (triangleEdge i j t).weights k =
      (if k = i then 1 - (t : ℝ) else 0) + (if k = j then (t : ℝ) else 0) := by
  simp only [triangleEdge, StdSimplex.weights_duple, Finsupp.add_apply,
    Finsupp.single_apply, unitInterval.coe_symm_eq, eq_comm]

@[simp] theorem triangleEdge_zero (i j : Fin 3) : triangleEdge i j 0 = StdSimplex.single i := by
  apply StdSimplex.ext
  simp [triangleEdge, StdSimplex.duple]
@[simp] theorem triangleEdge_one (i j : Fin 3) : triangleEdge i j 1 = StdSimplex.single j := by
  apply StdSimplex.ext
  simp [triangleEdge, StdSimplex.duple]

private theorem triangleEdge_face (i : Fin 3) (t : unitInterval) :
    triangleEdge (i.succAbove 0) (i.succAbove 1) t =
      StdSimplex.map (SimplexCategory.δ i).toOrderHom (StdSimplex.homeomorphI.symm t) := by
  have ht : StdSimplex.homeomorphI.symm t =
      StdSimplex.duple 0 1 (unitInterval.nonneg (unitInterval.symm t))
        (unitInterval.nonneg t) (by simp) := by
    apply StdSimplex.homeomorphI.injective
    apply Subtype.ext
    rw [Homeomorph.apply_symm_apply, StdSimplex.homeomorphI_apply_coe,
      StdSimplex.weights_duple, Finsupp.add_apply,
      Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      Finsupp.single_eq_same, zero_add]
  rw [ht, StdSimplex.map_duple]
  rfl

/-- The barycentric family restricts on each edge to its transformation. -/
theorem functorChainBarycentric_two_face {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (i : Fin 3) (x : ClassifyingSpace C) (t : unitInterval) :
    functorChainBarycentric (ComposableArrows.mk₂ α β)
      (x, triangleEdge (i.succAbove 0) (i.succAbove 1) t) =
    functorChainRealization ((nerve (C ⥤ D)).δ i (ComposableArrows.mk₂ α β))
      (x, realizationInterval t) := by
  change functorChainRealization _
    (x, (SimplexCategory.toTopHomeo ⦋2⦌).symm _) = _
  rw [triangleEdge_face, ← simplexRealization_map]
  have hi : (SimplexCategory.toTopHomeo ⦋1⦌).symm
      (Convexity.StdSimplex.homeomorphI.symm t) = realizationInterval t := rfl
  rw [hi]
  exact functorChainRealization_two_face α β i x t

/-- Fill the triangle between the inverse arrow and the reversed original arrow.
The other endpoint moves only along their composite edge. -/
def inverseTriangleParameter (s t : unitInterval) : StdSimplex ℝ (Fin 3) :=
  convexCombPair (R := ℝ) (unitInterval.symm s) s
    (unitInterval.nonneg _) (unitInterval.nonneg _) (by simp)
    (triangleEdge 1 2 t) (triangleEdge 0 1 (unitInterval.symm t))

/-- The inverse cap retains its three actual barycentric coordinates. -/
@[simp] theorem inverseTriangleParameter_apply (s t : unitInterval) (i : Fin 3) :
    (inverseTriangleParameter s t).weights i =
      ![(s : ℝ) * t, 1 - (t : ℝ), (1 - (s : ℝ)) * t] i := by
  fin_cases i <;>
    simp [inverseTriangleParameter, StdSimplex.weights_convexCombPair, triangleEdge,
      StdSimplex.duple, unitInterval.coe_symm_eq]; ring

@[fun_prop] theorem continuous_inverseTriangleParameter :
    Continuous (fun z : unitInterval × unitInterval ↦ inverseTriangleParameter z.1 z.2) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 3)).continuous_iff]
  unfold Function.comp
  refine continuous_pi (fun i ↦ ?_)
  simp only [inverseTriangleParameter, StdSimplex.weights_convexCombPair,
    Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    unitInterval.coe_symm_eq]
  simp only [triangleEdge, StdSimplex.duple, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> fun_prop

@[simp] theorem inverseTriangleParameter_zero (t : unitInterval) :
    inverseTriangleParameter 0 t = triangleEdge 1 2 t := by simp [inverseTriangleParameter]
@[simp] theorem inverseTriangleParameter_one (t : unitInterval) :
    inverseTriangleParameter 1 t = triangleEdge 0 1 (unitInterval.symm t) := by
  simp [inverseTriangleParameter]
@[simp] theorem inverseTriangleParameter_source (s : unitInterval) :
    inverseTriangleParameter s 0 = StdSimplex.single 1 := by simp [inverseTriangleParameter]
@[simp] theorem inverseTriangleParameter_target (s : unitInterval) :
    inverseTriangleParameter s 1 = triangleEdge 0 2 (unitInterval.symm s) := by
  apply StdSimplex.ext
  simp [inverseTriangleParameter, triangleEdge, StdSimplex.weights_convexCombPair,
    StdSimplex.duple, add_comm]
theorem functorChainBarycentric_two_first {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (x : ClassifyingSpace C) (t : unitInterval) :
    functorChainBarycentric (ComposableArrows.mk₂ α β) (x, triangleEdge 0 1 t) =
      classifyingSpaceNaturalTransformationHomotopy α (t, x) := by
  have h := functorChainBarycentric_two_face α β 2 x t
  rw [nerve.δ₂_mk₂_eq, functorChainRealization_one] at h
  exact h

theorem functorChainBarycentric_two_second {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (x : ClassifyingSpace C) (t : unitInterval) :
    functorChainBarycentric (ComposableArrows.mk₂ α β) (x, triangleEdge 1 2 t) =
      classifyingSpaceNaturalTransformationHomotopy β (t, x) := by
  have h := functorChainBarycentric_two_face α β 0 x t
  rw [nerve.δ₀_mk₂_eq, functorChainRealization_one] at h
  exact h

theorem functorChainBarycentric_two_composite {F G H : C ⥤ D}
    (α : F ⟶ G) (β : G ⟶ H) (x : ClassifyingSpace C) (t : unitInterval) :
    functorChainBarycentric (ComposableArrows.mk₂ α β) (x, triangleEdge 0 2 t) =
      classifyingSpaceNaturalTransformationHomotopy (α ≫ β) (t, x) := by
  have h := functorChainBarycentric_two_face α β 1 x t
  rw [nerve.δ₁_mk₂_eq, functorChainRealization_one] at h
  exact h

variable {B C D : Type u} [SmallCategory B] [SmallCategory C] [SmallCategory D]

/-- Restricting the source of a functor chain commutes with its nerve cylinder. -/
theorem functorChainNerveCylinder_whiskerLeft {n : ℕ}
    (A : ComposableArrows (C ⥤ D) n) (G : B ⥤ C) :
    (nerveMap G ⊗ₘ 𝟙 Δ[n]) ≫ functorChainNerveCylinder A =
      functorChainNerveCylinder (A ⋙ (Functor.whiskeringLeft B C D).obj G) := by
  ext k z
  rfl

/-- Joint simplex realization is natural in the source functor. -/
theorem functorChainRealization_whiskerLeft {n : ℕ}
    (A : ComposableArrows (C ⥤ D) n) (G : B ⥤ C)
    (x : ClassifyingSpace B) (z : |(Δ[n] : SSet.{u})|) :
    functorChainRealization A (classifyingSpaceMap G x, z) =
      functorChainRealization (A ⋙ (Functor.whiskeringLeft B C D).obj G) (x, z) := by
  have hn := realizationProductSimplexIso_inv_naturality (nerveMap G) (𝟙 ⦋n⦌)
  rw [show SSet.stdSimplex.map (𝟙 ⦋n⦌) = 𝟙 (Δ[n] : SSet.{u}) from
    CategoryTheory.Functor.map_id _ _, SSet.toTop.map_id] at hn
  have hv := ConcreteCategory.congr_hom hn (x, z)
  change SSet.toTop.map (functorChainNerveCylinder A)
    ((realizationProductSimplexIso (nerve C) n).inv (classifyingSpaceMap G x, z)) = _
  have hp : (SSet.toTop.map (nerveMap G) ⊗ₘ 𝟙 |(Δ[n] : SSet.{u})|) (x, z) =
      (classifyingSpaceMap G x, z) := rfl
  rw [TopCat.comp_app, TopCat.comp_app, hp] at hv
  rw [← hv]
  change (SSet.toTop.map (nerveMap G ⊗ₘ 𝟙 Δ[n]) ≫
    SSet.toTop.map (functorChainNerveCylinder A)) _ = _
  rw [← SSet.toTop.map_comp, functorChainNerveCylinder_whiskerLeft]
  rfl

theorem functorChainNerveCylinder_const (F : C ⥤ D) (n : ℕ) :
    functorChainNerveCylinder ((Functor.const (Fin (n + 1))).obj F) =
      fst (nerve C) Δ[n] ≫ nerveMap F := by
  ext k z : 4
  change (z.2.down.toOrderHom.monotone.functor.prod' z.1) ⋙
    Functor.uncurry.obj ((Functor.const (Fin (n + 1))).obj F) = z.1 ⋙ F
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro i; rfl
  · intro i j f
    simp [Functor.uncurry]

theorem functorChainRealization_const (F : C ⥤ D) (n : ℕ)
    (x : ClassifyingSpace C) (z : |(Δ[n] : SSet.{u})|) :
    functorChainRealization ((Functor.const (Fin (n + 1))).obj F) (x, z) =
      classifyingSpaceMap F x := by
  change SSet.toTop.map (functorChainNerveCylinder _)
    ((realizationProductSimplexIso (nerve C) n).inv (x, z)) = _
  rw [functorChainNerveCylinder_const, SSet.toTop.map_comp, TopCat.comp_app]
  have hp := congrArg _root_.Prod.fst (ConcreteCategory.congr_hom
    (realizationProductSimplexIso (nerve C) n).inv_hom_id (x, z))
  exact congrArg (classifyingSpaceMap F) hp

/-- A chain fixes a vertex whenever all its values there are the same object
and every arrow into that object is unique. This applies to the zero Q-object. -/
theorem functorChainRealization_vertex_of_subsingleton {n : ℕ}
    (A : ComposableArrows (C ⥤ D) n) (c : C) (d : D)
    (hobj : ∀ i, (A.obj i).obj c = d) (hthin : ∀ Y : D, Subsingleton (Y ⟶ d))
    (z : |(Δ[n] : SSet.{u})|) :
    functorChainRealization A (classifyingSpacePoint c, z) = classifyingSpacePoint d := by
  let K := (Functor.const C).obj c
  have he (i : Fin (n + 1)) : K ⋙ A.obj i = (Functor.const C).obj d := by
    refine CategoryTheory.Functor.ext (fun _ ↦ hobj i) ?_
    intro X Y f
    have ht : Subsingleton ((A.obj i).obj c ⟶ (A.obj i).obj c) := by
      rw [hobj i]; exact hthin _
    exact ht.elim _ _
  have hA : A ⋙ (Functor.whiskeringLeft C C D).obj K =
      (Functor.const (Fin (n + 1))).obj ((Functor.const C).obj d) := by
    refine CategoryTheory.Functor.ext he ?_
    intro i j f
    apply NatTrans.ext
    funext X
    have ht : Subsingleton ((A.obj i).obj c ⟶ (A.obj j).obj c) := by
      rw [hobj j]; exact hthin _
    exact ht.elim _ _
  have h := functorChainRealization_whiskerLeft A K (classifyingSpacePoint c) z
  rw [classifyingSpaceMap_point, hA, functorChainRealization_const,
    classifyingSpaceMap_point] at h
  exact h

end CategoryTheory
