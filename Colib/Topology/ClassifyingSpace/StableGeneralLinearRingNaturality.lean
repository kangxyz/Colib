/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.StableGeneralLinearCompletion

/-!
# Change of rings on the original stable matrix telescope

Entrywise ring maps give a natural transformation of the actual finite-rank
matrix categories and hence a functor on their Grothendieck constructions.
The original stable projection commutes strictly with this functor. Naturality
of a chosen inverse is obtained by homotopy cancellation, never by assuming
that independently chosen inverses commute strictly.

## Implementation provenance

Adapted from `Quillen/Topology/ClassifyingSpace/StableGeneralLinearRingNaturality.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, chosen paths, and original
proof hypotheses are retained under native ownership.
-/
@[expose] public section
noncomputable section
open Topology SSet HomotopyGroup
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
namespace StableGeneralLinear.GrothendieckModel
variable {R S : Type u} [Ring R] [Ring S]

/-- Entrywise change of rings in every original finite-rank category. -/
def ringDiagramMap (f : R →+* S) : categoryDiagram R ⟶ categoryDiagram S where
  app j := (smallFunctor (finiteMap f (rank j))).toCatHom
  naturality {j k} a := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun X => by rcases X with ⟨⟨⟩⟩; rfl) ?_
    intro X Y g
    rcases X with ⟨⟨⟩⟩
    rcases Y with ⟨⟨⟩⟩
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    exact congrArg ULift.up (finiteMap_transition f _ g.down)

/-- The genuine Grothendieck functor induced by entrywise change of rings. -/
def ringFunctor (f : R →+* S) : Telescope R ⥤ Telescope S :=
  CategoryTheory.Grothendieck.map (ringDiagramMap f)

/-- Change of rings preserves the original rank index. -/
@[simp] theorem ringFunctor_obj_base (f : R →+* S) (X : Telescope R) :
    ((ringFunctor f).obj X).base = X.base := rfl

private theorem oneObject_eqToHom_down {G : Type u} [_root_.Group G]
    {X Y : AsSmall.{0} (SingleObj G)} (h : X = Y) :
    (eqToHom h).down = (1 : G) := by
  subst h
  rfl

private theorem oneObject_comp_down {G : Type u} [_root_.Group G]
    {X Y Z : AsSmall.{0} (SingleObj G)} (a : X ⟶ Y) (b : Y ⟶ Z) :
    (a ≫ b).down = b.down * a.down := rfl

/-- A matrix arrow is changed entrywise, without an extra stable conjugation. -/
@[simp] theorem ringFunctor_map_fiber (f : R →+* S) {X Y : Telescope R}
    (a : X ⟶ Y) :
    ((ringFunctor f).map a).fiber.down = finiteMap f (rank Y.base) a.fiber.down := by
  dsimp only [ringFunctor, CategoryTheory.Grothendieck.map]
  simp only [Cat.Hom₂.eqToHom_toNatTrans, eqToHom_app]
  rw [oneObject_comp_down, oneObject_eqToHom_down]
  exact mul_one (M := Matrix.GeneralLinearGroup (Fin (rank Y.base)) S) _

/-- The actual projection square commutes before geometric realization. -/
theorem ringFunctor_projection (f : R →+* S) :
    ringFunctor f ⋙ projection S = projection R ⋙ smallFunctor (map f) := by
  refine CategoryTheory.Functor.ext (fun X => rfl) ?_
  intro X Y a
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  apply ULift.ext
  change of S (rank Y.base) ((ringFunctor f).map a).fiber.down =
    map f (of R (rank Y.base) a.fiber.down)
  rw [ringFunctor_map_fiber, map_of]

/-- The strict original projection square after geometric realization. -/
theorem ringFunctor_projection_realization (f : R →+* S) :
    (classifyingSpaceMap (projection S)).hom.comp (classifyingSpaceMap (ringFunctor f)).hom =
      (classifyingSpaceMap (smallFunctor (map f))).hom.comp
        (classifyingSpaceMap (projection R)).hom := by
  have h := congrArg (fun F => classifyingSpaceMap F) (ringFunctor_projection f)
  simpa only [classifyingSpaceMap_comp, TopCat.hom_comp] using congrArg TopCat.Hom.hom h

end StableGeneralLinear.GrothendieckModel

namespace ModuleCat.FiniteProjective.StableCompletion
open StableGeneralLinear StableGeneralLinear.GrothendieckModel
variable {R S : Type u} [Ring R] [Ring S]

/-- The chosen stable-to-telescope inverse is natural up to an actual homotopy.
The homotopy follows from the strict projection square and both inverse laws. -/
theorem originalStableToTelescope_ringMap (f : R →+* S) :
    ((classifyingSpaceMap (ringFunctor f)).hom.comp
      (originalStableToTelescope R)).Homotopic
      ((originalStableToTelescope S).comp
        (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom) := by
  let e := classifyingHomotopyEquiv S
  let a := (classifyingSpaceMap (ringFunctor f)).hom.comp (originalStableToTelescope R)
  let b := (originalStableToTelescope S).comp
    (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom
  let hR : C(ClassifyingSpace (SingleObj (StableGeneralLinear.Group R)),
      ClassifyingSpace (stableCategory R)) :=
    ⟨CategoryTheory.asSmallClassifyingHomeomorph
      (SingleObj (StableGeneralLinear.Group R)),
      (CategoryTheory.asSmallClassifyingHomeomorph
        (SingleObj (StableGeneralLinear.Group R))).continuous⟩
  let hS : C(ClassifyingSpace (SingleObj (StableGeneralLinear.Group S)),
      ClassifyingSpace (stableCategory S)) :=
    ⟨CategoryTheory.asSmallClassifyingHomeomorph
      (SingleObj (StableGeneralLinear.Group S)),
      (CategoryTheory.asSmallClassifyingHomeomorph
        (SingleObj (StableGeneralLinear.Group S))).continuous⟩
  have hn : (classifyingSpaceMap (smallFunctor (StableGeneralLinear.map f))).hom.comp hR =
      hS.comp (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom := by
    ext x
    exact smallFunctor_classifying_naturality (StableGeneralLinear.map f) x
  have ha : (e.toFun.comp a).Homotopic
      ((classifyingSpaceMap (smallFunctor (StableGeneralLinear.map f))).hom.comp hR) := by
    dsimp only [e, a]
    rw [classifyingHomotopyEquiv_toFun, ← ContinuousMap.comp_assoc,
      ringFunctor_projection_realization, ContinuousMap.comp_assoc]
    exact (ContinuousMap.Homotopic.refl _).comp (originalStableToTelescope_projection R)
  have hb : (e.toFun.comp b).Homotopic
      (hS.comp (classifyingSpaceMap (StableGeneralLinear.map f).toFunctor).hom) := by
    dsimp only [e, b]
    rw [classifyingHomotopyEquiv_toFun, ← ContinuousMap.comp_assoc]
    exact (originalStableToTelescope_projection S).comp (ContinuousMap.Homotopic.refl _)
  rw [hn] at ha
  have hab := ha.trans hb.symm
  have hleft : (e.invFun.comp (e.toFun.comp a)).Homotopic a := by
    simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
      e.left_inv.comp (ContinuousMap.Homotopic.refl a)
  have hright : (e.invFun.comp (e.toFun.comp b)).Homotopic b := by
    simpa only [ContinuousMap.comp_assoc, ContinuousMap.id_comp] using
      e.left_inv.comp (ContinuousMap.Homotopic.refl b)
  exact hleft.symm.trans (((ContinuousMap.Homotopic.refl e.invFun).comp hab).trans hright)

end ModuleCat.FiniteProjective.StableCompletion
