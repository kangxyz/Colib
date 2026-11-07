/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.GraphVertices

/-!
# Vertex Transport

Equality transport for a family of original vertex isomorphisms with a
specified final object; all endpoint equalities are retained.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory FundamentalGroupoid.OpenCover
universe u v w z
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment stdSimplex.Boundary
attribute [local instance] Localization.groupoid

/-- Equality transport for a family of original vertex isomorphisms with a
specified final object; all endpoint equalities are retained. -/
theorem isoFamily_to_target {B : Type u} {D : Type v} [Category.{w} D]
    (src dst : B → D) (γ : ∀ x, src x ≅ dst x) {x y : B} (h : x = y)
    (c : D) (hx : dst x = c) (hy : dst y = c) :
    eqToIso (congrArg src h) ≪≫ γ y ≪≫ eqToIso hy = γ x ≪≫ eqToIso hx := by
  subst y
  simp

/-- An old-stage point representing c is exactly the inverse original vertex homeomorphism. -/
theorem oldPoint_eq_original (C : Type u) [Category.{v} C] (x : NerveGraphData.Old C)
    (c : C) (h : NerveGraphData.oldObject C x = c) :
    x = (NerveGraphData.oldHomeomorph C).symm c := by
  apply (NerveGraphData.oldHomeomorph C).injective
  rw [Homeomorph.apply_symm_apply]
  exact h

/-- Exact graph-point equality induced by the original old-stage object formula. -/
theorem oldGraphPoint_eq_original (C : Type u) [Category.{v} C]
    (x : NerveGraphData.Old C) (c : C) (h : NerveGraphData.oldObject C x = c) :
    NerveGraphData.transition C x = graphVertex C c :=
  congrArg (NerveGraphData.transition C) (oldPoint_eq_original C x c h)

/-- The existing graph vertex isomorphism agrees with the original categorical
vertex identification after exactly its actual point and object transports. -/
theorem oldVertexIso_transport (C : Type u) [Category.{v} C]
    (x : NerveGraphData.Old C) (c : C) (h : NerveGraphData.oldObject C x = c) :
    eqToIso (congrArg (fun z => (nerveGraphDecoder C).obj (FundamentalGroupoid.mk z))
        (oldGraphPoint_eq_original C x c h)) ≪≫ graphVertexIso C c =
      nerveGraphDecoderVertexIso C x ≪≫ eqToIso (congrArg (⊤ : MorphismProperty C).Q.obj h) := by
  exact isoFamily_to_target
    (fun z => (nerveGraphDecoder C).obj (FundamentalGroupoid.mk (NerveGraphData.transition C z)))
    (NerveGraphData.vertex C) (nerveGraphDecoderVertexIso C)
    (oldPoint_eq_original C x c h) _ (congrArg (⊤ : MorphismProperty C).Q.obj h)
    (NerveGraphData.vertex_oldHomeomorph_symm C c)

@[reassoc]
theorem oldVertexIso_source (C : Type u) [Category.{v} C]
    (x : NerveGraphData.Old C) (c : C) (h : NerveGraphData.oldObject C x = c) :
    (nerveGraphDecoderVertexIso C x).hom ≫ eqToHom (congrArg (⊤ : MorphismProperty C).Q.obj h) =
      eqToHom (congrArg (fun z => (nerveGraphDecoder C).obj (FundamentalGroupoid.mk z))
        (oldGraphPoint_eq_original C x c h)) ≫ (graphVertexIso C c).hom := by
  exact (congrArg Iso.hom (oldVertexIso_transport C x c h)).symm

@[reassoc]
theorem oldVertexIso_target (C : Type u) [Category.{v} C]
    (x : NerveGraphData.Old C) (c : C) (h : NerveGraphData.oldObject C x = c) :
    eqToHom (congrArg (⊤ : MorphismProperty C).Q.obj h.symm) ≫
        (nerveGraphDecoderVertexIso C x).inv =
      (graphVertexIso C c).inv ≫
        eqToHom (congrArg (fun z => (nerveGraphDecoder C).obj (FundamentalGroupoid.mk z))
          (oldGraphPoint_eq_original C x c h).symm) := by
  exact (congrArg Iso.inv (oldVertexIso_transport C x c h)).symm

end CategoryTheory.NerveCompletion
