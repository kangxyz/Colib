/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.EdgePath
public import Colib.Analysis.Convex.StdSimplex.PathHomotopy

/-!
# Triangle relations for actual realized edge paths

Extracted from `Quillen/Topology/ClassifyingSpace/ArrowPaths.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, endpoints,
relative homotopies, universe parameters and multiplication order are retained.
Only native namespace and import ownership change unless noted below.

The finite-simplex filling uses native coordinate interpolation and
`SimplexCategory.toTopHomeo` directly. The pinned realization functor, path
parameters and fixed endpoints are unchanged.

-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Opposite
open scoped Simplicial Topology unitInterval

namespace SSet

/-- All paths with the same endpoints in a realized finite simplex are homotopic. -/
theorem realizationStdSimplex_paths_homotopic {n : ℕ}
    {x y : |(Δ[n] : SSet.{u})|} (p q : Path x y) : p.Homotopic q := by
  let e := SimplexCategory.toTopHomeo (SimplexCategory.mk n)
  have h : (p.map e.continuous).Homotopic (q.map e.continuous) :=
    ⟨Convexity.StdSimplex.pathHomotopy _ _⟩
  have H := h.map ⟨e.symm, e.symm.continuous⟩
  have H' := H.pathCast (e.symm_apply_apply x).symm (e.symm_apply_apply y).symm
  convert H' using 1 <;> ext t <;> exact (e.symm_apply_apply _).symm

/-- The edge from one ordered vertex of the standard simplex to another. -/
def simplexEdge (n : ℕ) (i j : Fin (n + 1)) (h : i ≤ j) :
    (Δ[n] : SSet.{u}).Edge (SSet.stdSimplex.obj₀Equiv.symm i)
      (SSet.stdSimplex.obj₀Equiv.symm j) :=
  .mk (SSet.stdSimplex.edge n i j h)
    (by ext k : 1; fin_cases k; rfl) (by ext k : 1; fin_cases k; rfl)

/-- The first standard triangle edge has exactly the opposite-vertex characteristic map. -/
lemma simplexEdge_01_yoneda :
    SSet.yonedaEquiv.symm (simplexEdge.{u} 2 0 1 (by decide)).edge =
      SSet.stdSimplex.δ 2 := by
  apply SSet.yonedaEquiv.injective
  simp only [Equiv.apply_symm_apply]
  ext k : 1
  fin_cases k <;> rfl

/-- The second standard triangle edge has exactly the opposite-vertex characteristic map. -/
lemma simplexEdge_12_yoneda :
    SSet.yonedaEquiv.symm (simplexEdge.{u} 2 1 2 (by decide)).edge =
      SSet.stdSimplex.δ 0 := by
  apply SSet.yonedaEquiv.injective
  simp only [Equiv.apply_symm_apply]
  ext k : 1
  fin_cases k <;> rfl

/-- The long standard triangle edge has exactly the middle-vertex characteristic map. -/
lemma simplexEdge_02_yoneda :
    SSet.yonedaEquiv.symm (simplexEdge.{u} 2 0 2 (by decide)).edge =
      SSet.stdSimplex.δ 1 := by
  apply SSet.yonedaEquiv.injective
  simp only [Equiv.apply_symm_apply]
  ext k : 1
  fin_cases k <;> rfl

/-- Realizing the characteristic map of a two-simplex takes its three
standard edges to the three prescribed edges. -/
theorem realizationEdgePath_triangle_face
    {X : SSet.{u}} {x y : X _⦋0⦌} (e : X.Edge x y)
    (s : X _⦋2⦌) (i : Fin 3) (h : X.δ i s = e.edge)
    (t : unitInterval) :
    SSet.toTop.map (SSet.yonedaEquiv.symm s)
      (SSet.toTop.map (SSet.stdSimplex.δ i) (realizationInterval t)) =
        realizationEdgePath e t := by
  change (SSet.toTop.map (SSet.stdSimplex.δ i) ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm s)) _ = _
  rw [← Functor.map_comp, SSet.stdSimplex.δ_comp_yonedaEquiv_symm, h]
  rfl

/-- A simplicial triangle gives the actual relative path homotopy expressing
composition of its two short edges as its long edge. -/
theorem realizationEdgePath_comp
    {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}
    (s : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    ((realizationEdgePath e₀₁).trans (realizationEdgePath e₁₂)).Homotopic
      (realizationEdgePath e₀₂) := by
  let p := realizationEdgePath (simplexEdge.{u} 2 0 1 (by decide))
  let q := realizationEdgePath (simplexEdge.{u} 2 1 2 (by decide))
  let r := realizationEdgePath (simplexEdge.{u} 2 0 2 (by decide))
  let f := (SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)).hom
  have hp (t) : f (p t) = realizationEdgePath e₀₁ t := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
    rw [simplexEdge_01_yoneda]
    exact realizationEdgePath_triangle_face e₀₁ s.simplex 2 s.d₂ t
  have hq (t) : f (q t) = realizationEdgePath e₁₂ t := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
    rw [simplexEdge_12_yoneda]
    exact realizationEdgePath_triangle_face e₁₂ s.simplex 0 s.d₀ t
  have hr (t) : f (r t) = realizationEdgePath e₀₂ t := by
    change SSet.toTop.map (SSet.yonedaEquiv.symm s.simplex)
      (SSet.toTop.map (SSet.yonedaEquiv.symm _) (realizationInterval t)) = _
    rw [simplexEdge_02_yoneda]
    exact realizationEdgePath_triangle_face e₀₂ s.simplex 1 s.d₁ t
  have h₀ : realizationPoint x₀ = f (realizationPoint (SSet.stdSimplex.obj₀Equiv.symm 0)) := by
    simpa using (hp 0).symm
  have h₂ : realizationPoint x₂ = f (realizationPoint (SSet.stdSimplex.obj₀Equiv.symm 2)) := by
    simpa using (hq 1).symm
  have H := ((realizationStdSimplex_paths_homotopic (p.trans q) r).map f).pathCast h₀ h₂
  convert H using 1
  · ext t
    change ((realizationEdgePath e₀₁).trans (realizationEdgePath e₁₂)) t =
      ((p.trans q).map f.continuous) t
    rw [Path.map_trans]
    simp only [Path.trans_apply]
    split_ifs
    · exact (hp _).symm
    · exact (hq _).symm
  · ext t
    exact (hr t).symm

end SSet

attribute [colib_tag "COL-0083",
  colib_ref "HatcherAT" "Section 1.1, Example 1.1, page 25"
    "ingredient"
    "Convex simplex path homotopy used for the actual simplicial triangle relation"]
  SSet.realizationStdSimplex_paths_homotopic
  SSet.realizationEdgePath_comp
