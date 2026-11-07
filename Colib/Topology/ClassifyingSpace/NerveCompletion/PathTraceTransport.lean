/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.ClassifyingSpace.NerveCompletion.AllEdgesTrace

/-!
# Path Trace Transport

Transport a path trace using its exact original endpoint equalities. The
endpoint isomorphisms acquire those precise equality transports.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
universe u v w
namespace CategoryTheory.NerveCompletion
open FundamentalGroupoid.OpenCover TopCat.SimplexAttachment stdSimplex.Boundary

/-- Transport a path trace using its exact original endpoint equalities. The
endpoint isomorphisms acquire those precise equality transports. -/
theorem functor_path_cast_trace {X : Type u} [TopologicalSpace X]
    {D : Type v} [Category.{w} D] (F : FundamentalGroupoid X ⥤ D)
    {x y x' y' : X} (p : Path x y) (hx : x' = x) (hy : y' = y)
    {a b : D} (α : F.obj (FundamentalGroupoid.mk x) ≅ a)
    (β : F.obj (FundamentalGroupoid.mk y) ≅ b) (f : a ⟶ b)
    (h : F.map (Path.Homotopic.Quotient.mk p) = α.hom ≫ f ≫ β.inv) :
    F.map (Path.Homotopic.Quotient.mk (p.cast hx hy)) =
      (eqToIso (congrArg (fun z => F.obj (FundamentalGroupoid.mk z)) hx) ≪≫ α).hom ≫ f ≫
        (eqToIso (congrArg (fun z => F.obj (FundamentalGroupoid.mk z)) hy) ≪≫ β).inv := by
  rw [Path.Homotopic.Quotient.mk_cast, ← FundamentalGroupoid.conj_eqToHom]
  simp only [Functor.map_comp, eqToHom_map, h, Iso.trans_hom, Iso.trans_inv,
    eqToIso.hom, eqToIso.inv, Category.assoc]

end CategoryTheory.NerveCompletion
