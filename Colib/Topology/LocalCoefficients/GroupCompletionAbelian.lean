/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Abelian
public import Colib.Topology.ClassifyingSpace.GroupCompletionTranslation
public import Colib.Topology.ClassifyingSpace.MonoidalFundamentalGroup
public import Colib.CategoryTheory.GroupCompletion.Monoidal
public import Colib.Topology.ClassifyingSpace.Connectivity
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
Adapted from `Quillen/Topology/LocalCoefficients/GroupCompletionAbelian.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving all actual loop maps.

# Abelian monodromy on every component of the actual group completion

Coordinate translations carry the unit component to every object vertex.
Their genuine homotopy inverses transfer commutativity of loops at the unit;
paths from vertices then cover every point of the classifying space. Thus the
conclusion concerns all local systems, not only systems on the unit component.
-/

@[expose] public section

noncomputable section

open CategoryTheory MonoidalCategory

universe u v w

namespace FundamentalGroupoid.LocalCoefficients

/-- A full functor transfers commutativity of the endomorphisms of an object. -/
theorem endomorphisms_commute_of_full {C : Type u} [Category C]
    {D : Type v} [Category D] (F : C ⥤ D) [F.Full] (x : C)
    (hx : ∀ g h : x ⟶ x, g ≫ h = h ≫ g)
    (g h : F.obj x ⟶ F.obj x) : g ≫ h = h ≫ g := by
  obtain ⟨g, rfl⟩ := F.map_surjective g
  obtain ⟨h, rfl⟩ := F.map_surjective h
  rw [← F.map_comp, ← F.map_comp, hx]

/-- Commutativity of endomorphisms is invariant under an actual object isomorphism. -/
theorem endomorphisms_commute_of_iso {C : Type u} [Category C] {x y : C}
    (e : x ≅ y) (hx : ∀ g h : x ⟶ x, g ≫ h = h ≫ g)
    (g h : y ⟶ y) : g ≫ h = h ≫ g := by
  have he := hx (e.hom ≫ g ≫ e.inv) (e.hom ≫ h ≫ e.inv)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id] using
    congrArg (fun k ↦ e.inv ≫ k ≫ e.hom) he

/-- A genuine homotopy equivalence transfers commutativity at its original image point. -/
theorem loops_commute_of_homotopyEquiv {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (x : X)
    (hx : ∀ g h : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x,
      g ≫ h = h ≫ g)
    (g h : FundamentalGroupoid.mk (e x) ⟶ FundamentalGroupoid.mk (e x)) :
    g ≫ h = h ≫ g := by
  let F := FundamentalGroupoidFunctor.equivOfHomotopyEquiv e
  exact endomorphisms_commute_of_full F.functor (FundamentalGroupoid.mk x) hx g h

/-- A specified joining path transfers commutativity of the actual loop classes. -/
theorem loops_commute_of_joined {X : Type u} [TopologicalSpace X] {x y : X}
    (p : Joined x y)
    (hx : ∀ g h : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x,
      g ≫ h = h ≫ g)
    (g h : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk y) :
    g ≫ h = h ≫ g := by
  obtain ⟨p⟩ := p
  exact endomorphisms_commute_of_iso
    (asIso (Path.Homotopic.Quotient.mk p)) hx g h

end FundamentalGroupoid.LocalCoefficients

namespace CategoryTheory.GroupCompletion.Localization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Translating both coordinates carries the actual unit vertex to the given pair,
up to the two original left unitors. -/
def unitToVertexHomotopyEquiv (X : Localization C C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Localization C C))
      (ClassifyingSpace (Localization C C)) :=
  (translationClassifyingHomotopyEquiv X.obj.1).trans
    (translationClassifyingHomotopyEquiv X.obj.2).symm

/-- The specified path is the edge of the original pair of left unitors. -/
lemma unitToVertexHomotopyEquiv_joined (X : Localization C C) :
    Joined (unitToVertexHomotopyEquiv X (classifyingSpacePoint (𝟙_ (Localization C C))))
      (classifyingSpacePoint X) := by
  change Joined (classifyingSpaceMap (secondTranslation X.obj.2)
    (classifyingSpaceMap (firstTranslation X.obj.1)
      (classifyingSpacePoint (𝟙_ (Localization C C))))) _
  rw [classifyingSpaceMap_point, classifyingSpaceMap_point]
  exact ⟨classifyingSpacePath (leftUnitIso X).hom⟩

/-- Every point of the actual group-completion classifying space has commuting loops. -/
theorem classifyingSpace_loops_commute
    (x : FundamentalGroupoid (ClassifyingSpace (Localization C C)))
    (g h : x ⟶ x) : g ≫ h = h ≫ g := by
  have hunit : ∀ g h : FundamentalGroupoid.mk
      (classifyingSpacePoint (𝟙_ (Localization C C))) ⟶
      FundamentalGroupoid.mk (classifyingSpacePoint (𝟙_ (Localization C C))),
      g ≫ h = h ≫ g := by
    intro g h
    exact congrArg End.asHom
      (classifyingUnitFundamentalGroup_mul_comm (C := Localization C C) (End.of h) (End.of g))
  obtain ⟨X, hX⟩ := classifyingSpace_joined_vertex x.as
  apply FundamentalGroupoid.LocalCoefficients.loops_commute_of_joined hX
  apply FundamentalGroupoid.LocalCoefficients.loops_commute_of_joined
    (unitToVertexHomotopyEquiv_joined X)
  exact FundamentalGroupoid.LocalCoefficients.loops_commute_of_homotopyEquiv
    (unitToVertexHomotopyEquiv X) _ hunit

/-- All coefficient systems on the whole actual completion have abelian monodromy. -/
theorem classifyingSpace_abelianMonodromy
    (A : FundamentalGroupoid.LocalCoefficients.System.{max u v, w}
      (ClassifyingSpace (Localization C C))) :
    FundamentalGroupoid.LocalCoefficients.AbelianMonodromy A :=
  FundamentalGroupoid.LocalCoefficients.abelianMonodromy_of_commutative_loops A
    classifyingSpace_loops_commute

end CategoryTheory.GroupCompletion.Localization
