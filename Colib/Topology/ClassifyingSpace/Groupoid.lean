/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.Discrete
public import Colib.Topology.ClassifyingSpace.AsSmall
public import Colib.CategoryTheory.TheoremB.WeakComparison
public import Colib.CategoryTheory.TheoremB.Conditions
public import Colib.Topology.Homotopy.HomotopyGroup.Contractible
public import Colib.Topology.Homotopy.HomotopyGroup.PathTransport
public import Colib.Topology.ClassifyingSpace.Connectivity
public import Mathlib.CategoryTheory.SingleObj

/-!
# Asphericity of the original groupoid classifying space

The actual comma of a point inclusion is the discrete set of original arrows.
The proved Theorem B comparison and genuine homotopy-fiber long exact sequence
therefore kill all homotopy groups of degree at least two. Actual nerve lifts
and vertex paths retain independent category universes and arbitrary basepoints.
No calculation of the fundamental group is assumed or claimed.

Implementation provenance: `Quillen/Topology/ClassifyingSpace/Groupoid.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps and universes are retained.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology
universe u v
namespace CategoryTheory.GroupoidClassifying
variable {C : Type u} [SmallCategory C] (c d : C)

/-- The functor from the one-object discrete category selecting the object `c`. -/
abbrev pointFunctor : Discrete PUnit.{u+1} ⥤ C := Functor.fromPUnit c

/-- The functor sending an object of the comma category of the point inclusion to its arrow `c ⟶
d` in the discrete morphism set. -/
def pointCommaProjection : CostructuredArrow (pointFunctor c) d ⥤ Discrete (c ⟶ d) where
  obj X := .mk X.hom
  map f := eqToHom (congrArg Discrete.mk (by
    simpa [pointFunctor] using (CostructuredArrow.w f).symm))

/-- The functor sending an arrow `c ⟶ d` to the corresponding comma object of the point
inclusion. -/
def pointCommaSection : Discrete (c ⟶ d) ⥤ CostructuredArrow (pointFunctor c) d :=
  Discrete.functor (fun f ↦ CostructuredArrow.mk (Y := Discrete.mk PUnit.unit) f)

/-- The actual comma of a point inclusion is the discrete original morphism set. -/
def pointCommaEquivalence : CostructuredArrow (pointFunctor c) d ≌ Discrete (c ⟶ d) where
  functor := pointCommaProjection c d
  inverse := pointCommaSection c d
  unitIso := NatIso.ofComponents (fun X ↦
    CostructuredArrow.isoMk (eqToIso (Subsingleton.elim _ _)) (by
      change (𝟙 c) ≫ X.hom = X.hom
      simp))
    (by intro X Y f; apply CostructuredArrow.ext; exact Subsingleton.elim _ _)
  counitIso := Discrete.natIso (fun _ ↦ Iso.refl _)

/-- Every positive homotopy group of the original point comma is trivial. -/
theorem pointComma_subsingleton_pi
    (x : ClassifyingSpace (CostructuredArrow (pointFunctor c) d)) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n + 1)
      (ClassifyingSpace (CostructuredArrow (pointFunctor c) d)) x) := by
  let e := equivalenceClassifyingHomotopyEquiv (pointCommaEquivalence c d)
  let : Subsingleton (HomotopyGroup.Pi (n + 1) (ClassifyingSpace (Discrete (c ⟶ d)))
      (e.toFun x)) := discreteClassifying_subsingleton_pi _ _ n
  exact (homotopyGroupMap_bijective_of_homotopyEquiv e rfl (n + 1)).injective.subsingleton

/-- The original classifying space of the point category is contractible. -/
theorem point_contractible : ContractibleSpace (ClassifyingSpace (Discrete PUnit.{u+1})) :=
  classifyingSpace_contractible_of_isInitial
    (IsInitial.ofUniqueHom (X := Discrete.mk PUnit.unit)
      (fun _ ↦ eqToHom (Subsingleton.elim _ _)) (fun _ _ ↦ Subsingleton.elim _ _))

end CategoryTheory.GroupoidClassifying

namespace CategoryTheory.GroupoidClassifying
variable {C : Type u} [SmallCategory C] [IsGroupoid C] (c : C)

/-- The actual point-inclusion fiber has trivial positive homotopy groups,
using the proved original Theorem B comparison and its actual discrete comma. -/
theorem pointFiber_subsingleton_pi (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n + 1)
      (HomotopyFiber (classifyingSpaceMap (pointFunctor c)).hom (classifyingSpacePoint c))
      (HomotopyFiber.basepoint (classifyingSpaceMap (pointFunctor c)).hom
        (classifyingSpacePoint c) (classifyingSpacePoint (Discrete.mk PUnit.unit))
        (classifyingSpaceMap_point (pointFunctor c) (Discrete.mk PUnit.unit)))) := by
  let x : Discrete PUnit.{u+1} := .mk PUnit.unit
  have h := TheoremB.fiberComparison_bijective (pointFunctor c)
    (TheoremB.transitionHomotopyEquivalences_of_groupoid (pointFunctor c)) x (n + 1)
  exact @Function.Surjective.subsingleton _ _ _
    (pointComma_subsingleton_pi c c
      (classifyingSpacePoint (CostructuredArrow.mk (Y := x) (𝟙 c))) n) h.surjective

/-- The actual classifying space of every small groupoid is aspherical at
its original object vertices: every homotopy group of degree at least two is trivial. -/
theorem subsingleton_higher_pi (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n + 2) (ClassifyingSpace C) (classifyingSpacePoint c)) := by
  let F := pointFunctor c
  let x : Discrete PUnit.{u+1} := .mk PUnit.unit
  let f := (classifyingSpaceMap F).hom
  let y := classifyingSpacePoint c
  let z := classifyingSpacePoint x
  have hb : f z = y := classifyingSpaceMap_point F x
  let : ContractibleSpace (ClassifyingSpace (Discrete PUnit.{u+1})) := point_contractible
  let : Subsingleton (HomotopyGroup.Pi (n + 1)
      (HomotopyFiber f y) (HomotopyFiber.basepoint f y z hb)) :=
    pointFiber_subsingleton_pi c n
  have hall (a : HomotopyGroup.Pi (n + 2) (ClassifyingSpace C) y) : a = 1 := by
    have ha : a ∈ (HomotopyFiber.connectingHom f y z hb n).ker := Subsingleton.elim _ _
    rw [← HomotopyFiber.range_piMap_eq_ker_connectingHom f y z hb n] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [pi_eq_one_of_contractible z (n + 1) b, map_one]
  exact ⟨fun a b ↦ (hall a).trans (hall b).symm⟩

end CategoryTheory.GroupoidClassifying

namespace CategoryTheory.GroupoidClassifying
variable {C : Type u} [Category.{v} C] [IsGroupoid C]

/-- Asphericity of the ORIGINAL groupoid realization in independent object/hom
universes, transported by the actual vertex-preserving simplicial isomorphism. -/
theorem subsingleton_higher_pi_general (c : C) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n + 2) (ClassifyingSpace C) (classifyingSpacePoint c)) := by
  let : (AsSmall.down : AsSmall.{0} C ⥤ C).IsEquivalence :=
    (AsSmall.equiv : C ≌ AsSmall.{0} C).isEquivalence_inverse
  let : IsGroupoid (AsSmall.{0} C) := isGroupoid_of_reflects_iso AsSmall.down
  let : Subsingleton (HomotopyGroup.Pi (n + 2) (ClassifyingSpace (AsSmall.{0} C))
      (classifyingSpacePoint (AsSmall.up.obj c))) := subsingleton_higher_pi _ n
  exact (homotopyGroupMap_bijective_of_homotopyEquiv
    (asSmallClassifyingHomeomorph C).toHomotopyEquiv
    (asSmallClassifyingHomeomorph_point C c) (n + 2)).injective.subsingleton

/-- The original group nerve is aspherical in every group universe, without commutativity. -/
theorem singleObj_subsingleton_higher_pi (G : Type u) [Group G] (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n + 2) (ClassifyingSpace (SingleObj G))
      (classifyingSpacePoint (SingleObj.star G))) :=
  subsingleton_higher_pi_general (SingleObj.star G) n

end CategoryTheory.GroupoidClassifying

namespace CategoryTheory.GroupoidClassifying
variable {C : Type u} [Category.{v} C] [IsGroupoid C]

/-- Every actual point is joined to a vertex, so original groupoid realizations
have trivial higher homotopy at every basepoint, with independent universes. -/
theorem subsingleton_higher_pi_at (x : ClassifyingSpace C) (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n + 2) (ClassifyingSpace C) x) := by
  obtain ⟨c, ⟨γ⟩⟩ := classifyingSpace_joined_vertex x
  let : Subsingleton (HomotopyGroup.Pi (n + 2) (ClassifyingSpace C)
      (classifyingSpacePoint c)) := subsingleton_higher_pi_general c n
  exact (pathTransport γ (n + 2)).symm.injective.subsingleton

end CategoryTheory.GroupoidClassifying
