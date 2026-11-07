/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Category.TopCat.ColimitAcross
public import Colib.Topology.Realization.Basic

/-!
# Geometric-realization descent across universes

Compatible maps on the native topological simplices descend to the unchanged
geometric realization, preserving each simplex and its ordinary barycentric
coordinates. There is no additional simplicial-set or realization model.

Implementation provenance: the simplex-colimit and descent construction of
`Quillen/Topology/Realization/UniverseLift.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Native `Convexity.StdSimplex` coordinates
replace the source's convex-space simplex spelling.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u v w
namespace SSet

/-- The original simplex cocone defining geometric realization. -/
def realizationSimplexCocone (X : SSet.{u}) :
    Cocone (CostructuredArrow.proj SSet.stdSimplex X ⋙ SimplexCategory.toTop) :=
  (Functor.LeftExtension.mk SSet.toTop SSet.toTopSimplex.inv).coconeAt X

/-- Geometric realization is the colimit of its original topological simplices. -/
def realizationSimplexCoconeIsColimit (X : SSet.{u}) :
    IsColimit (realizationSimplexCocone X) :=
  Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    SSet.toTop SSet.toTopSimplex.inv X

/-- The characteristic map of an original simplex in ordinary barycentric coordinates. -/
def realizationSimplex {X : SSet.{u}} {n : SimplexCategory} (x : X.obj (op n)) :
    C(Convexity.StdSimplex ℝ (Fin (n.len + 1)), |X|) :=
  (SSet.toTop.map (SSet.yonedaEquiv.symm x)).hom.comp
    ⟨(SimplexCategory.toTopHomeo n).symm, (SimplexCategory.toTopHomeo n).symm.continuous⟩

/-- Characteristic maps respect every simplicial operator. -/
theorem realizationSimplex_naturality {X : SSet.{u}} {n m : SimplexCategory}
    (a : n ⟶ m) (x : X.obj (op m)) (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    realizationSimplex x (Convexity.StdSimplex.map a t) =
      realizationSimplex (X.map a.op x) t := by
  change SSet.toTop.map (SSet.yonedaEquiv.symm x)
    ((SimplexCategory.toTopHomeo m).symm (Convexity.StdSimplex.map a t)) = _
  rw [SimplexCategory.toTopHomeo_symm_naturality_apply]
  change (SSet.toTop.map (SSet.stdSimplex.map a) ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm x)) _ = _
  rw [← Functor.map_comp, SSet.yonedaEquiv_symm_naturality_left]
  rfl

theorem realizationSimplexCocone_ι_apply {X : SSet.{u}}
    (j : CostructuredArrow SSet.stdSimplex X)
    (t : Convexity.StdSimplex ℝ (Fin (j.left.len + 1))) :
    (realizationSimplexCocone X).ι.app j (ULift.up t) =
      realizationSimplex (SSet.yonedaEquiv j.hom) t := by
  simp only [realizationSimplex, Equiv.symm_apply_apply]
  rfl

/-- Descend a compatible family on the original simplices to a target in any universe. -/
def realizationDesc {X : SSet.{u}} {Z : Type v} [TopologicalSpace Z]
    (f : ∀ (n : SimplexCategory), X.obj (op n) →
      C(Convexity.StdSimplex ℝ (Fin (n.len + 1)), Z))
    (hf : ∀ {n m} (a : n ⟶ m) (x : X.obj (op m))
      (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))),
      f m x (Convexity.StdSimplex.map a t) = f n (X.map a.op x) t) : C(|X|, Z) :=
  TopCat.colimitDescAcross (realizationSimplexCocone X)
    (realizationSimplexCoconeIsColimit X)
    (fun j ↦ ⟨fun t ↦ f j.left (SSet.yonedaEquiv j.hom) t.down, by fun_prop⟩)
    (by
      intro j k a t
      change f k.left (SSet.yonedaEquiv k.hom) (Convexity.StdSimplex.map a.left t.down) = _
      rw [hf]
      congr 2
      rw [SSet.yonedaEquiv_naturality, CostructuredArrow.w a])

@[simp] theorem realizationDesc_simplex {X : SSet.{u}} {Z : Type v} [TopologicalSpace Z]
    (f : ∀ (n : SimplexCategory), X.obj (op n) →
      C(Convexity.StdSimplex ℝ (Fin (n.len + 1)), Z))
    (hf : ∀ {n m} (a : n ⟶ m) (x : X.obj (op m))
      (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))),
      f m x (Convexity.StdSimplex.map a t) = f n (X.map a.op x) t)
    (n : SimplexCategory) (x : X.obj (op n)) (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    realizationDesc f hf (realizationSimplex x t) = f n x t := by
  have hx : realizationSimplex x t = (realizationSimplexCocone X).ι.app
      (CostructuredArrow.mk (SSet.yonedaEquiv.symm x)) (ULift.up t) := by
    rw [realizationSimplexCocone_ι_apply]
    simp
  unfold realizationDesc
  rw [hx]
  erw [TopCat.colimitDescAcross_ι]
  · simp
  · intro j k a s
    change f k.left (SSet.yonedaEquiv k.hom) (Convexity.StdSimplex.map a.left s.down) = _
    rw [hf]
    congr 2
    rw [SSet.yonedaEquiv_naturality, CostructuredArrow.w a]

/-- Functions out of realization are determined on its original simplices. -/
theorem realization_ext {X : SSet.{u}} {Z : Type v} (f g : |X| → Z)
    (h : ∀ (n : SimplexCategory) (x : X.obj (op n))
      (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))),
      f (realizationSimplex x t) = g (realizationSimplex x t)) : f = g := by
  funext z
  obtain ⟨j, t, rfl⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget TopCat) (realizationSimplexCoconeIsColimit X)) z
  change f ((realizationSimplexCocone X).ι.app j t) =
    g ((realizationSimplexCocone X).ι.app j t)
  change SimplexCategory.toTop.obj j.left at t
  obtain ⟨t⟩ := t
  rw [realizationSimplexCocone_ι_apply]
  exact h _ _ _

@[simp] theorem realizationSimplex_zero {X : SSet.{u}} (x : X _⦋0⦌)
    (t : Convexity.StdSimplex ℝ (Fin 1)) :
    realizationSimplex x t = realizationPoint x := by
  exact congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm x))
    (Subsingleton.elim ((SimplexCategory.toTopHomeo ⦋0⦌).symm t) default)

end SSet
