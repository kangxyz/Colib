/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Homotopy.OpenCover.LocalGeneration
public import Colib.Topology.Homotopy.OpenCover.TransitionData

/-!
# Local Trivializations

Natural isomorphisms on an actual path-connected space are determined by
one component. Naturality on every actual path is essential to this statement.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory
universe u v w z
namespace FundamentalGroupoid.OpenCover

/-- Natural isomorphisms on an actual path-connected space are determined by
one component. Naturality on every actual path is essential to this statement. -/
theorem natIso_eq_of_component {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
    {C : Type v} [Category.{w} C] {F G : FundamentalGroupoid X ⥤ C}
    (e e' : F ≅ G) (b : X)
    (hb : e.app (FundamentalGroupoid.mk b) = e'.app (FundamentalGroupoid.mk b)) : e = e' := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  let f := Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath b x.as)
  apply (cancel_epi (F.map f)).mp
  rw [e.hom.naturality, e'.hom.naturality]
  exact congrArg (fun k => k ≫ G.map f) (congrArg Iso.hom hb)

/-- Actual chart trivializations agreeing at every actual overlap point glue to
a constant natural isomorphism. This constructs global naturality from all local
path naturality; it does not assume a global decoder or global loop vanishing. -/
def constantIsoOfChartTrivializations {X : Type u} [TopologicalSpace X]
    {ι : Type v} (U : ι → Set X) (c : CoverData U)
    {C : Type w} [Groupoid.{z} C] (F : FundamentalGroupoid X ⥤ C) (b : C)
    (η : ∀ i, FundamentalGroupoid.map ((ContinuousMap.subtypeVal (U i))) ⋙ F ≅
      (Functor.const (FundamentalGroupoid (U i))).obj b)
    (hη : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j),
      (η i).app (FundamentalGroupoid.mk ⟨x, hi⟩) =
        (η j).app (FundamentalGroupoid.mk ⟨x, hj⟩)) :
    F ≅ (Functor.const (FundamentalGroupoid X)).obj b := by
  let β (x : FundamentalGroupoid X) : F.obj x ≅ b :=
    (η (TransitionData.chosenChart c x.as)).app
      (FundamentalGroupoid.mk ⟨x.as, TransitionData.mem_chosenChart c x.as⟩)
  refine isoOfLocalIntertwining U c F ((Functor.const (FundamentalGroupoid X)).obj b) β ?_
  intro i x y p hp
  change ∀ ⦃z : X⦄, z ∈ Set.range p → z ∈ U i at hp
  have hn := (η i).hom.naturality (Path.Homotopic.Quotient.mk ((Path.inSubset (x := ⟨_, hp
      (p).source_mem_range⟩) (y := ⟨_, hp (p).target_mem_range⟩) p hp)))
  change F.map (Path.Homotopic.Quotient.mk p) ≫
      (η i).hom.app (FundamentalGroupoid.mk ⟨y, hp p.target_mem_range⟩) =
      (η i).hom.app (FundamentalGroupoid.mk ⟨x, hp p.source_mem_range⟩) ≫ 𝟙 b at hn
  have hx : β (FundamentalGroupoid.mk x) =
      (η i).app (FundamentalGroupoid.mk ⟨x, hp p.source_mem_range⟩) :=
    hη _ i x _ _
  have hy : β (FundamentalGroupoid.mk y) =
      (η i).app (FundamentalGroupoid.mk ⟨y, hp p.target_mem_range⟩) :=
    hη _ i y _ _
  change F.map (Path.Homotopic.Quotient.mk p) =
    (β (FundamentalGroupoid.mk x)).hom ≫ 𝟙 b ≫ (β (FundamentalGroupoid.mk y)).inv
  rw [hx, hy]
  calc
    F.map (Path.Homotopic.Quotient.mk p) =
        (((η i).app (FundamentalGroupoid.mk ⟨x, hp p.source_mem_range⟩)).hom ≫ 𝟙 b) ≫
          ((η i).app (FundamentalGroupoid.mk ⟨y, hp p.target_mem_range⟩)).inv :=
      (((η i).app (FundamentalGroupoid.mk ⟨y, hp p.target_mem_range⟩)).eq_comp_inv).mpr hn
    _ = _ := Category.assoc _ _ _

end FundamentalGroupoid.OpenCover
