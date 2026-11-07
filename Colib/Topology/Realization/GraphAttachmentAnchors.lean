/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.SimplexAttachmentPathGeneration
public import Colib.Topology.Realization.SimplexBoundaryEndpoints

/-!
# Canonical-edge anchors in an actual graph attachment

Each point of the actual one-simplex attachment admits compatible anchor data.
An edge spoke uses a chosen source-to-point path class preceded by the given
vertex isomorphism `ε`; it is not an explicitly specified straight segment.
Endpoint compatibility assumes the supplied edge morphisms and their `hedge`
equation. No compatibility with arbitrary attachment paths is concluded.

## Implementation provenance

Adapted from all six declarations of
`Quillen/Topology/Realization/EdgePathPresentation/GraphAnchors.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual vertex identifications,
source-to-point paths and edge compatibility equation are retained. No discreteness
assumption is added to the parameter or vertex spaces.
-/
@[expose] public section

noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits Convexity.StdSimplex Topology Set
open scoped Topology unitInterval
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace TopCat
namespace GraphAttachment

variable (X : TopCat.{u}) {V D Y : TopCat.{u}}
    {f : TopCat.of (X × Convexity.StdSimplex.boundary 1) ⟶ V}
    {g : TopCat.of (X × Convexity.StdSimplex ℝ (Fin 2)) ⟶ D} {j : V ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion X 1) f g j)
    (h : C(D, Y)) {A : Type v} [Groupoid.{w} A]
    (F : A ⥤ FundamentalGroupoid Y) (vertex : V → A)
    (ε : ∀ c : V, F.obj (vertex c) ≅ FundamentalGroupoid.mk (h (j c)))

/-- Identify a specified original vertex with its equal cell-boundary point. -/
def vertexIso (a : X) (b : Convexity.StdSimplex.boundary 1) :
    F.obj (vertex (f (a, b))) ≅ FundamentalGroupoid.mk (h (g (a, b.1))) :=
  ε (f (a, b)) ≪≫ eqToIso (congrArg FundamentalGroupoid.mk
    (congrArg h (ConcreteCategory.congr_hom sq.w (a, b)).symm))

/-- The actual source-to-point path in an attached one-simplex, preceded by
the specified original vertex identification. -/
def spoke (a : X) (x : Convexity.StdSimplex ℝ (Fin 2)) :
    F.obj (vertex (f (a, boundaryZero))) ⟶ FundamentalGroupoid.mk (h (g (a, x))) :=
  (vertexIso X sq h F vertex ε a boundaryZero).hom ≫
    ⟦(PathConnectedSpace.somePath (Convexity.StdSimplex.single 0) x).map
      (h.comp (simplexAttachmentCellMap X 1 (g := g) a)).continuous⟧

/-- All genuine paths in one geometric edge satisfy the source-spoke relation. -/
lemma spoke_comp (a : X) {x y : Convexity.StdSimplex ℝ (Fin 2)} (p : Path x y) :
    spoke X sq h F vertex ε a x ≫
        (⟦p.map (h.comp (simplexAttachmentCellMap X 1 (g := g) a)).continuous⟧ :
          FundamentalGroupoid.mk (h (g (a, x))) ⟶
            FundamentalGroupoid.mk (h (g (a, y)))) =
      spoke X sq h F vertex ε a y := by
  let k := h.comp (simplexAttachmentCellMap X 1 (g := g) a)
  have H := (Convexity.StdSimplex.paths_homotopic
    ((PathConnectedSpace.somePath (Convexity.StdSimplex.single 0) x).trans p)
      (PathConnectedSpace.somePath (Convexity.StdSimplex.single 0) y)).map k
  have he : Path.Homotopic.Quotient.mk
      (((PathConnectedSpace.somePath (Convexity.StdSimplex.single 0) x).trans p).map k.continuous) =
      Path.Homotopic.Quotient.mk
        ((PathConnectedSpace.somePath (Convexity.StdSimplex.single 0) y).map k.continuous) :=
    Quotient.sound H
  dsimp only [spoke]
  rw [Category.assoc]
  apply congrArg ((vertexIso X sq h F vertex ε a boundaryZero).hom ≫ ·)
  change (Path.Homotopic.Quotient.mk
    ((PathConnectedSpace.somePath (Convexity.StdSimplex.single 0) x).map k.continuous)).trans
      (Path.Homotopic.Quotient.mk (p.map k.continuous)) =
    Path.Homotopic.Quotient.mk
      ((PathConnectedSpace.somePath (Convexity.StdSimplex.single 0) y).map k.continuous)
  simpa only [Path.map_trans, Path.Homotopic.Quotient.mk_trans] using he

@[simp] lemma spoke_source (a : X) :
    spoke X sq h F vertex ε a (Convexity.StdSimplex.single 0) =
      (vertexIso X sq h F vertex ε a boundaryZero).hom := by
  let k := h.comp (simplexAttachmentCellMap X 1 (g := g) a)
  have H := (Convexity.StdSimplex.paths_homotopic
    (PathConnectedSpace.somePath (Convexity.StdSimplex.single (0 : Fin 2))
      (Convexity.StdSimplex.single 0))
      (Path.refl (Convexity.StdSimplex.single 0))).map k
  have he : Path.Homotopic.Quotient.mk
      ((PathConnectedSpace.somePath (Convexity.StdSimplex.single (0 : Fin 2))
        (Convexity.StdSimplex.single 0)).map k.continuous) =
      Path.Homotopic.Quotient.mk ((Path.refl (Convexity.StdSimplex.single 0)).map k.continuous) :=
    Quotient.sound H
  dsimp only [spoke]
  have he' : (⟦(PathConnectedSpace.somePath (Convexity.StdSimplex.single (0 : Fin 2))
      (Convexity.StdSimplex.single 0)).map k.continuous⟧ :
      FundamentalGroupoid.mk (k (Convexity.StdSimplex.single 0)) ⟶
        FundamentalGroupoid.mk (k (Convexity.StdSimplex.single 0))) =
      𝟙 (FundamentalGroupoid.mk (k (Convexity.StdSimplex.single 0))) := by
    change Path.Homotopic.Quotient.mk _ =
      Path.Homotopic.Quotient.mk (Path.refl (k (Convexity.StdSimplex.single 0)))
    exact he.trans (congrArg Path.Homotopic.Quotient.mk (by ext t; rfl))
  erw [he']
  exact Category.comp_id _

/-- Anchor data require only agreement on original vertices and individual
geometric edge charts. They make no assertion about arbitrary continuous paths. -/
structure Anchor (z : D) where
  /-- The original source object selected for this point. -/
  obj : A
  /-- Its actual path class to the point. -/
  hom : F.obj obj ⟶ FundamentalGroupoid.mk (h z)
  /-- On an original vertex, the anchor differs by an original groupoid arrow. -/
  old : ∀ (c : V) (hc : j c = z), ∃ q : obj ⟶ vertex c,
    hom = F.map q ≫ (ε c).hom ≫
      eqToHom (congrArg FundamentalGroupoid.mk (congrArg h hc))
  /-- On an edge chart, the anchor differs from its source spoke by an original arrow. -/
  cell : ∀ (a : X) (x : Convexity.StdSimplex ℝ (Fin 2)) (hx : g (a, x) = z),
    ∃ q : obj ⟶ vertex (f (a, boundaryZero)),
      hom = F.map q ≫ spoke X sq h F vertex ε a x ≫
        eqToHom (congrArg FundamentalGroupoid.mk (congrArg h hx))

variable (edge : ∀ a : X, vertex (f (a, boundaryZero)) ⟶ vertex (f (a, boundaryOne)))
    (hedge : ∀ a : X, spoke X sq h F vertex ε a (Convexity.StdSimplex.single 1) =
      F.map (edge a) ≫ (vertexIso X sq h F vertex ε a boundaryOne).hom)

include hedge in
/-- The actual pushout identifications supply compatible anchors. Only original
edge morphisms are used when a chart meets its target vertex. -/
theorem anchor_nonempty (z : D) : Nonempty (Anchor X sq h F vertex ε z) := by
  classical
  by_cases hz : z ∈ Set.range j
  · obtain ⟨c, hc⟩ := hz
    refine ⟨{
      obj := vertex c
      hom := (ε c).hom ≫ eqToHom (congrArg FundamentalGroupoid.mk (congrArg h hc))
      old := ?_
      cell := ?_ }⟩
    · intro d hd
      have hcd : c = d := (simplexAttachment_old_isClosedEmbedding X 1 sq).injective
        (hc.trans hd.symm)
      subst d
      exact ⟨𝟙 _, by simp⟩
    · intro a x hx
      obtain ⟨⟨a', b⟩, hab, hbc⟩ :=
        (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit
          (sq.map (forget TopCat)).isColimit
          (isClosedEmbedding_parameterizedSimplexBoundary X 1).injective (a, x) c).mp
            (hx.trans hc.symm)
      have ha : a' = a := congrArg Prod.fst hab
      subst a'
      have hb : b.1 = x := congrArg Prod.snd hab
      subst x
      change f (a, b) = c at hbc
      subst c
      rcases boundary_eq_zero_or_one b with rfl | rfl
      · refine ⟨𝟙 _, ?_⟩
        change _ = F.map (𝟙 _) ≫ spoke X sq h F vertex ε a (Convexity.StdSimplex.single 0) ≫ _
        rw [spoke_source]
        simp [vertexIso, Category.assoc]
      · refine ⟨inv (edge a), ?_⟩
        change _ = F.map (inv (edge a)) ≫
          spoke X sq h F vertex ε a (Convexity.StdSimplex.single 1) ≫ _
        rw [hedge]
        simp [vertexIso, Category.assoc]
  · obtain ⟨b, hb⟩ := Set.mem_range.mp
      ((Set.ext_iff.mp (range_pushout_cell_compl sq
        (isClosedEmbedding_parameterizedSimplexBoundary X 1).injective) z).mpr hz)
    refine ⟨{
      obj := vertex (f (b.1.1, boundaryZero))
      hom := spoke X sq h F vertex ε b.1.1 b.1.2 ≫
        eqToHom (congrArg FundamentalGroupoid.mk (congrArg h hb))
      old := ?_
      cell := ?_ }⟩
    · intro c hc
      exact (hz ⟨c, hc⟩).elim
    · intro a x hx
      have he : b.1 = (a, x) := pushout_cell_eq_of_not_mem_range sq b.2 (hb.trans hx.symm)
      rcases b with ⟨⟨a', x'⟩, hb'⟩
      have ha : a' = a := congrArg Prod.fst he
      have hx' : x' = x := congrArg Prod.snd he
      subst a' x'
      exact ⟨𝟙 _, by simp⟩

end GraphAttachment
end TopCat

attribute [colib_tag "COL-0108",
  colib_ref "HatcherAT" "Section 1.1, Example 1.1, page 25"
    "ingredient"
    "Chosen path classes inside one geometric edge, with endpoint-fixed homotopies"]
  TopCat.GraphAttachment.spoke
  TopCat.GraphAttachment.spoke_comp
  TopCat.GraphAttachment.spoke_source

attribute [colib_tag "COL-0108",
  colib_ref "HatcherAT" "Section 1.1, Proposition 1.5, page 28"
    "background"
    "Transport using given endpoint isomorphisms; edge compatibility remains a hypothesis"]
  TopCat.GraphAttachment.vertexIso
  TopCat.GraphAttachment.Anchor
  TopCat.GraphAttachment.anchor_nonempty
