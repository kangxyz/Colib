/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.Descent

/-!
# Local Generation

Actual arrows on which a specified family of isomorphisms intertwines two
functors form a subgroupoid. No global naturality is assumed.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover

/-- Actual arrows on which a specified family of isomorphisms intertwines two
functors form a subgroupoid. No global naturality is assumed. -/
def intertwiningSubgroupoid {D : Type u} [Groupoid.{v} D]
    {C : Type w} [Groupoid.{z} C] (F G : D ⥤ C) (β : ∀ x, F.obj x ≅ G.obj x) :
    Subgroupoid D where
  arrows x y := {p | F.map p = (β x).hom ≫ G.map p ≫ (β y).inv}
  inv := by
    intro x y p hp
    change F.map (Groupoid.inv p) = _
    simpa [Functor.map_inv, Category.assoc, Groupoid.inv_eq_inv] using congrArg Groupoid.inv hp
  mul := by
    intro x y z p hp q hq
    change F.map (p ≫ q) = _
    rw [F.map_comp, G.map_comp, hp, hq]
    simp [Category.assoc]

/-- Naturality on every actual path inside each open chart implies naturality
on all actual ambient paths, by the existing genuine path-generation theorem. -/
theorem intertwining_of_openCover {X : Type u} [TopologicalSpace X]
    {ι : Type v} (U : ι → Set X) (c : CoverData U)
    {C : Type w} [Groupoid.{z} C]
    (F G : FundamentalGroupoid X ⥤ C) (β : ∀ x, F.obj x ≅ G.obj x)
    (hloc : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      F.map (Path.Homotopic.Quotient.mk p) =
        (β (FundamentalGroupoid.mk x)).hom ≫ G.map (Path.Homotopic.Quotient.mk p) ≫
          (β (FundamentalGroupoid.mk y)).inv)
    {x y : X} (p : Path x y) :
    F.map (Path.Homotopic.Quotient.mk p) =
      (β (FundamentalGroupoid.mk x)).hom ≫ G.map (Path.Homotopic.Quotient.mk p) ≫
        (β (FundamentalGroupoid.mk y)).inv :=
  FundamentalGroupoid.path_mem_of_openCover (intertwiningSubgroupoid F G β) U c.isOpen
    (fun x _ => c.covers x) hloc p

/-- A natural isomorphism built from locally verified actual path equalities. -/
def isoOfLocalIntertwining {X : Type u} [TopologicalSpace X]
    {ι : Type v} (U : ι → Set X) (c : CoverData U)
    {C : Type w} [Groupoid.{z} C]
    (F G : FundamentalGroupoid X ⥤ C) (β : ∀ x, F.obj x ≅ G.obj x)
    (hloc : ∀ i {x y : X} (p : Path x y), Set.range p ⊆ U i →
      F.map (Path.Homotopic.Quotient.mk p) =
        (β (FundamentalGroupoid.mk x)).hom ≫ G.map (Path.Homotopic.Quotient.mk p) ≫
          (β (FundamentalGroupoid.mk y)).inv) : F ≅ G :=
  NatIso.ofComponents β (by
    intro x y f
    induction f using _root_.Quotient.ind with | _ p =>
      have h := intertwining_of_openCover U c F G β hloc p
      erw [h]
      simp)

end FundamentalGroupoid.OpenCover
