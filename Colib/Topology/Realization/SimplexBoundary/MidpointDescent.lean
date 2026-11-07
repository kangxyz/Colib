/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.SimplexBoundary.StarTrivializations
public import Colib.Topology.Homotopy.OpenCover.Restriction

/-!
# Midpoint Descent

All actual overlap components agree once the prescribed midpoint components
agree: both restrictions are already natural on every actual overlap path.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory stdSimplex FundamentalGroupoid.OpenCover
universe u v
namespace stdSimplex.Boundary
variable {n : ℕ}

/-- All actual overlap components agree once the prescribed midpoint components
agree: both restrictions are already natural on every actual overlap path. -/
theorem star_isos_agree_of_midpoints {C : Type u} [Category.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (b : C)
    (η : ∀ i, FundamentalGroupoid.map ((ContinuousMap.subtypeVal (vertexStar i))) ⋙ F ≅
      (Functor.const (FundamentalGroupoid (vertexStar i))).obj b)
    (hmid : ∀ i j,
      (η i).app (FundamentalGroupoid.mk ⟨edgeMidpoint i j, (edgeMidpoint_mem i j).1⟩) =
      (η j).app (FundamentalGroupoid.mk ⟨edgeMidpoint i j, (edgeMidpoint_mem i j).2⟩)) :
    ∀ i j x (hi : x ∈ vertexStar i) (hj : x ∈ vertexStar j),
      (η i).app (FundamentalGroupoid.mk ⟨x, hi⟩) =
        (η j).app (FundamentalGroupoid.mk ⟨x, hj⟩) := by
  intro i j x hi hj
  let S := vertexStar i ∩ vertexStar j
  let incli : S ⊆ vertexStar i := fun _ h => h.1
  let inclj : S ⊆ vertexStar j := fun _ h => h.2
  let ei := restrictChartIso F b S (vertexStar i) incli (η i)
  let ej := restrictChartIso F b S (vertexStar j) inclj (η j)
  let : ContractibleSpace S := contractible_overlap i j
  have he : ei = ej := natIso_eq_of_component ei ej
    ⟨edgeMidpoint i j, edgeMidpoint_mem i j⟩ (by
      apply Iso.ext
      change (restrictChartIso F b S (vertexStar i) incli (η i)).hom.app _ =
        (restrictChartIso F b S (vertexStar j) inclj (η j)).hom.app _
      rw [restrictChartIso_hom_app, restrictChartIso_hom_app]
      exact congrArg Iso.hom (hmid i j))
  apply Iso.ext
  have hh := congrArg (fun e => e.hom.app (FundamentalGroupoid.mk (⟨x, hi, hj⟩ : S))) he
  change (restrictChartIso F b S (vertexStar i) incli (η i)).hom.app _ =
    (restrictChartIso F b S (vertexStar j) inclj (η j)).hom.app _ at hh
  rw [restrictChartIso_hom_app, restrictChartIso_hom_app] at hh
  exact hh

/-- A constant boundary natural isomorphism constructed from the finite midpoint
checks, actual open-star contractions and all actual overlap-path naturality. -/
def boundaryConstantIsoOfMidpoints {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (b : C)
    (β : ∀ i, F.obj (FundamentalGroupoid.mk (vertex i)) ≅ b)
    (hmid : ∀ i j,
      (starPotentialIso F b β i).app
          (FundamentalGroupoid.mk ⟨edgeMidpoint i j, (edgeMidpoint_mem i j).1⟩) =
      (starPotentialIso F b β j).app
          (FundamentalGroupoid.mk ⟨edgeMidpoint i j, (edgeMidpoint_mem i j).2⟩)) :
    F ≅ (Functor.const (FundamentalGroupoid (boundary (n + 2)))).obj b :=
  constantIsoOfChartTrivializations vertexStar starCover F b (starPotentialIso F b β)
    (star_isos_agree_of_midpoints F b (starPotentialIso F b β) hmid)

/-- Under the explicit finite midpoint conditions, EVERY actual boundary loop
is killed. The midpoint conditions for the nerve attaching functor remain a
separate original-face computation; they are not hidden in this conclusion. -/
theorem boundary_loop_eq_id_of_midpoints {C : Type u} [Groupoid.{v} C]
    (F : FundamentalGroupoid (boundary (n + 2)) ⥤ C) (b : C)
    (β : ∀ i, F.obj (FundamentalGroupoid.mk (vertex i)) ≅ b)
    (hmid : ∀ i j,
      (starPotentialIso F b β i).app
          (FundamentalGroupoid.mk ⟨edgeMidpoint i j, (edgeMidpoint_mem i j).1⟩) =
      (starPotentialIso F b β j).app
          (FundamentalGroupoid.mk ⟨edgeMidpoint i j, (edgeMidpoint_mem i j).2⟩))
    (x : boundary (n + 2)) (p : Path x x) :
    F.map (Path.Homotopic.Quotient.mk p) = 𝟙 (F.obj (FundamentalGroupoid.mk x)) := by
  let e := boundaryConstantIsoOfMidpoints F b β hmid
  have hn := e.hom.naturality (Path.Homotopic.Quotient.mk p)
  change F.map (Path.Homotopic.Quotient.mk p) ≫ e.hom.app (FundamentalGroupoid.mk x) =
    e.hom.app (FundamentalGroupoid.mk x) ≫ 𝟙 b at hn
  apply (cancel_mono (e.app (FundamentalGroupoid.mk x)).hom).mp
  exact hn.trans ((Category.comp_id (e.app (FundamentalGroupoid.mk x)).hom).trans
    (Category.id_comp (e.app (FundamentalGroupoid.mk x)).hom).symm)

end stdSimplex.Boundary
