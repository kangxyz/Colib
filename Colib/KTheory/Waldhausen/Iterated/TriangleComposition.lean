/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.TriangleRealization
public import Colib.CategoryTheory.TheoremB.CompositionHomotopy

/-!
# Actual composition comparisons for iterated transformation homotopies

The genuine realized triangle supplies a continuous endpoint-relative and based comparison
between the original composite-transformation homotopy and the concatenation of its original
factors. The original structure coordinate remains independent throughout.
-/
/-! Implementation provenance: `Quillen/Waldhausen/SConstruction/Iterated/TriangleComposition.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, simplex faces,
whole fixed-zero family, and independent structure parameters are retained under native ownership.
  -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory Convexity
open scoped Simplicial Topology unitInterval
universe u

namespace CategoryTheory.Waldhausen.IteratedS

open SmallWaldhausenCategory SSet Topology

private theorem simplexFamily_precomp {X Y : SSet.{u}} {m k : ℕ}
    (H : X ⊗ Δ[k] ⟶ Y) (f : ⦋m⦌ ⟶ ⦋k⦌) (x : |X|) (z : |(Δ[m] : SSet.{u})|) :
    realizationSimplexFamily H (x, SSet.toTop.map (SSet.stdSimplex.map f) z) =
      realizationSimplexFamily (((𝟙 X) ⊗ₘ SSet.stdSimplex.map f) ≫ H) (x, z) := by
  have hp := ConcreteCategory.congr_hom
    (realizationProductSimplexIso_inv_naturality (𝟙 X) f) (x, z)
  have hv : (SSet.toTop.map (𝟙 X) ⊗ₘ SSet.toTop.map (SSet.stdSimplex.map f))
      (x, z) = (x, SSet.toTop.map (SSet.stdSimplex.map f) z) := by simp
  rw [TopCat.comp_app, TopCat.comp_app, hv] at hp
  change SSet.toTop.map H ((realizationProductSimplexIso X k).inv
    (x, SSet.toTop.map (SSet.stdSimplex.map f) z)) = _
  rw [← hp]
  change (SSet.toTop.map ((𝟙 X) ⊗ₘ SSet.stdSimplex.map f) ≫ SSet.toTop.map H)
    ((realizationProductSimplexIso X m).inv (x, z)) = _
  rw [← Functor.map_comp]
  rfl

private theorem simplexFamily_interval {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : SSet.Homotopy f g) (x : |X|) (t : unitInterval) :
    realizationSimplexFamily H.h (x, realizationInterval t) =
      realizationSimplicialHomotopy H (t, x) := by
  have hp := ConcreteCategory.congr_hom (realizationProductSimplexIso_one_inv X)
    (x, ULift.up t)
  exact congrArg (SSet.toTop.map H.h) hp

private theorem triangleEdge_realization (i : Fin 3) (t : unitInterval) :
    (SimplexCategory.toTopHomeo ⦋2⦌).symm
      (triangleEdge (i.succAbove 0) (i.succAbove 1) t) =
      SSet.toTop.map (SSet.stdSimplex.δ i) (realizationInterval t) := by
  apply (SimplexCategory.toTopHomeo ⦋2⦌).injective
  rw [Homeomorph.apply_symm_apply]
  change triangleEdge _ _ t = (SimplexCategory.toTopHomeo ⦋2⦌)
    (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.δ i)) (realizationInterval t))
  rw [SimplexCategory.toTopHomeo_naturality_apply]
  have ht : StdSimplex.homeomorphI.symm t =
      StdSimplex.duple 0 1 (unitInterval.nonneg (unitInterval.symm t))
        (unitInterval.nonneg t) (by simp) := by
    apply StdSimplex.homeomorphI.injective
    apply Subtype.ext
    rw [Homeomorph.apply_symm_apply, StdSimplex.homeomorphI_apply_coe,
      StdSimplex.weights_duple, Finsupp.add_apply,
      Finsupp.single_eq_of_ne (by decide : (1 : Fin 2) ≠ 0),
      Finsupp.single_eq_same, zero_add]
  have hi : (SimplexCategory.toTopHomeo ⦋1⦌) (realizationInterval t) =
      StdSimplex.homeomorphI.symm t := by
    change (SimplexCategory.toTopHomeo ⦋1⦌)
      ((SimplexCategory.toTopHomeo ⦋1⦌).symm (StdSimplex.homeomorphI.symm t)) = _
    exact Homeomorph.apply_symm_apply _ _
  rw [hi]
  change triangleEdge _ _ t =
    StdSimplex.map (SimplexCategory.δ i).toOrderHom (StdSimplex.homeomorphI.symm t)
  rw [ht, StdSimplex.map_duple]
  rfl

variable {V W : WideSubcategory preservesZero.{u}} {F G H : V ⟶ W}
  (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
  (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))

/-- The actual stage triangle in barycentric coordinates. -/
def stageTriangleBarycentric (r : ℕ) :
    C(stageSpace r V × StdSimplex ℝ (Fin 3), stageSpace r W) where
  toFun z := stageTriangleRealization η θ hη hθ r
    (z.1, (SimplexCategory.toTopHomeo ⦋2⦌).symm z.2)
  continuous_toFun := by fun_prop

/-- The first geometric face is exactly the original first transformation track. -/
theorem stageTriangleBarycentric_first (r : ℕ) (x : stageSpace r V) (t : unitInterval) :
    stageTriangleBarycentric η θ hη hθ r (x, triangleEdge 0 1 t) =
      stageTransformationTopHomotopy r η hη (t, x) := by
  change realizationSimplexFamily _
    (x, (SimplexCategory.toTopHomeo ⦋2⦌).symm (triangleEdge 0 1 t)) = _
  have he := triangleEdge_realization (2 : Fin 3) t
  change (SimplexCategory.toTopHomeo ⦋2⦌).symm (triangleEdge 0 1 t) = _ at he
  rw [he]
  refine (simplexFamily_precomp (stageTransformationTriangle r η θ hη hθ)
    (SimplexCategory.δ (2 : Fin 3)) x (realizationInterval t)).trans ?_
  exact (congrArg (fun K : (stages r).obj V ⊗ Δ[1] ⟶ (stages r).obj W ↦
    realizationSimplexFamily K (x, realizationInterval t))
      (stageTransformationTriangle_first η θ hη hθ r)).trans
        (simplexFamily_interval (stageTransformationHomotopy r η hη) x t)

/-- The second geometric face is exactly the original second transformation track. -/
theorem stageTriangleBarycentric_second (r : ℕ) (x : stageSpace r V) (t : unitInterval) :
    stageTriangleBarycentric η θ hη hθ r (x, triangleEdge 1 2 t) =
      stageTransformationTopHomotopy r θ hθ (t, x) := by
  change realizationSimplexFamily _
    (x, (SimplexCategory.toTopHomeo ⦋2⦌).symm (triangleEdge 1 2 t)) = _
  have he := triangleEdge_realization (0 : Fin 3) t
  change (SimplexCategory.toTopHomeo ⦋2⦌).symm (triangleEdge 1 2 t) = _ at he
  rw [he]
  refine (simplexFamily_precomp (stageTransformationTriangle r η θ hη hθ)
    (SimplexCategory.δ (0 : Fin 3)) x (realizationInterval t)).trans ?_
  exact (congrArg (fun K : (stages r).obj V ⊗ Δ[1] ⟶ (stages r).obj W ↦
    realizationSimplexFamily K (x, realizationInterval t))
      (stageTransformationTriangle_second η θ hη hθ r)).trans
        (simplexFamily_interval (stageTransformationHomotopy r θ hθ) x t)

/-- The long geometric face is exactly the original composite-transformation track. -/
theorem stageTriangleBarycentric_composite (r : ℕ) (x : stageSpace r V) (t : unitInterval) :
    stageTriangleBarycentric η θ hη hθ r (x, triangleEdge 0 2 t) =
      stageTransformationTopHomotopy r (η ≫ θ)
        (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) (t, x) := by
  change realizationSimplexFamily _
    (x, (SimplexCategory.toTopHomeo ⦋2⦌).symm (triangleEdge 0 2 t)) = _
  have he := triangleEdge_realization (1 : Fin 3) t
  change (SimplexCategory.toTopHomeo ⦋2⦌).symm (triangleEdge 0 2 t) = _ at he
  rw [he]
  refine (simplexFamily_precomp (stageTransformationTriangle r η θ hη hθ)
    (SimplexCategory.δ (1 : Fin 3)) x (realizationInterval t)).trans ?_
  exact (congrArg (fun K : (stages r).obj V ⊗ Δ[1] ⟶ (stages r).obj W ↦
    realizationSimplexFamily K (x, realizationInterval t))
      (stageTransformationTriangle_composite η θ hη hθ r)).trans
        (simplexFamily_interval (stageTransformationHomotopy r (η ≫ θ)
          (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A))) x t)

/-- The entire realized triangle fixes the original stage point. -/
theorem stageTriangleRealization_fixed_point (r : ℕ) (z : |(Δ[2] : SSet.{u})|) :
    stageTriangleRealization η θ hη hθ r (stagePoint r V, z) = stagePoint r W := by
  let p := (realizationProductSimplexIso (Δ[0] : SSet.{u}) 2).inv (default, z)
  have hn := ConcreteCategory.congr_hom
    (realizationProductSimplexIso_inv_whisker (SSet.yonedaEquiv.symm (stageVertex r V)) 2)
    (default, z)
  change SSet.toTop.map (SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[2]) p =
    (realizationProductSimplexIso ((stages r).obj V) 2).inv (stagePoint r V, z) at hn
  change SSet.toTop.map (stageTransformationTriangle r η θ hη hθ)
    ((realizationProductSimplexIso ((stages r).obj V) 2).inv (stagePoint r V, z)) = _
  rw [← hn]
  change (SSet.toTop.map (SSet.yonedaEquiv.symm (stageVertex r V) ▷ Δ[2]) ≫
    SSet.toTop.map (stageTransformationTriangle r η θ hη hθ)) p = _
  rw [← Functor.map_comp, stageTransformationTriangle_fixed_vertex,
    Functor.map_comp, TopCat.comp_app]
  rw [Subsingleton.elim (SSet.toTop.map (fst Δ[0] Δ[2]) p) default]
  rfl

/-- The original composite stage homotopy is compared to concatenation through the genuine
triangle, relative to both endpoints and the original basepoint line. -/
def stageTransformationCompositionHomotopy (r : ℕ) :
    (stageTransformationTopHomotopy r (η ≫ θ)
      (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A))).toContinuousMap.HomotopyRel
      ((stageTransformationTopHomotopy r η hη).trans
        (stageTransformationTopHomotopy r θ hθ)).toContinuousMap
      (fun z : unitInterval × stageSpace r V ↦ z.1 = 0 ∨ z.1 = 1 ∨ z.2 = stagePoint r V) where
  toFun z := stageTriangleBarycentric η θ hη hθ r
    (z.2.2, TheoremB.compositionTriangleHomotopy (z.1, z.2.1))
  continuous_toFun := by fun_prop
  map_zero_left z := by
    change stageTriangleBarycentric _ _ _ _ _
      (z.2, TheoremB.compositionTriangleHomotopy (0, z.1)) = _
    rw [TheoremB.compositionTriangleHomotopy.apply_zero]
    exact stageTriangleBarycentric_composite η θ hη hθ r z.2 z.1
  map_one_left z := by
    change stageTriangleBarycentric _ _ _ _ _
      (z.2, TheoremB.compositionTriangleHomotopy (1, z.1)) = _
    rw [TheoremB.compositionTriangleHomotopy.apply_one]
    change stageTriangleBarycentric _ _ _ _ _
      (z.2, ((TheoremB.triangleEdgePath 0 1).trans (TheoremB.triangleEdgePath 1 2)) z.1) =
        ((stageTransformationTopHomotopy r η hη).trans
          (stageTransformationTopHomotopy r θ hθ)) z
    rw [Path.trans_apply, ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact stageTriangleBarycentric_first η θ hη hθ r z.2 _
    · exact stageTriangleBarycentric_second η θ hη hθ r z.2 _
  prop' s z hz := by
    rcases z with ⟨t, x⟩
    rcases hz with ht | ht | hx
    · change t = 0 at ht
      subst t
      change stageTriangleBarycentric _ _ _ _ _
        (x, TheoremB.compositionTriangleHomotopy (s, 0)) = _
      rw [TheoremB.compositionTriangleHomotopy.eq_fst s (by simp)]
      exact stageTriangleBarycentric_composite η θ hη hθ r x 0
    · change t = 1 at ht
      subst t
      change stageTriangleBarycentric _ _ _ _ _
        (x, TheoremB.compositionTriangleHomotopy (s, 1)) = _
      rw [TheoremB.compositionTriangleHomotopy.eq_fst s (by simp)]
      exact stageTriangleBarycentric_composite η θ hη hθ r x 1
    · change x = stagePoint r V at hx
      subst x
      exact (stageTriangleRealization_fixed_point η θ hη hθ r _).trans
        (stageTransformationTopHomotopy_fixed_point r (η ≫ θ)
          (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) t).symm

/-- The entire two-parameter comparison fixes the actual original stage point. -/
theorem stageTransformationCompositionHomotopy_fixed_point (r : ℕ) (s t : unitInterval) :
    stageTransformationCompositionHomotopy η θ hη hθ r (s, (t, stagePoint r V)) =
      stagePoint r W :=
  ((stageTransformationCompositionHomotopy η θ hη hθ r).eq_fst s
    (Or.inr (Or.inr rfl))).trans
      (stageTransformationTopHomotopy_fixed_point r (η ≫ θ)
        (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hθ A)) t)

/-- Both homotopy times remain independent of the original structure coordinate. -/
theorem stageTransformationCompositionHomotopy_structure (r : ℕ)
    (s t q : unitInterval) (x : stageSpace r V) :
    stageTransformationCompositionHomotopy η θ hη hθ (r + 1)
        (s, (t, stageLoopMap r V x q)) =
      stageLoopMap r W (stageTransformationCompositionHomotopy η θ hη hθ r (s, (t, x))) q :=
  stageTriangleRealization_structure η θ hη hθ r
    ((SimplexCategory.toTopHomeo ⦋2⦌).symm (TheoremB.compositionTriangleHomotopy (s, t))) q x

end CategoryTheory.Waldhausen.IteratedS
