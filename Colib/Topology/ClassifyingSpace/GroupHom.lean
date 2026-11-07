/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.FundamentalGroup
public import Colib.Topology.ClassifyingSpace.Map
public import Colib.Topology.ClassifyingSpace.ArrowPathsNaturality
public import Colib.Topology.Homotopy.HomotopyGroup.Map

/-!
# Group homomorphisms on genuine classifying spaces

Realizing a homomorphism between one-object group categories gives a pointed
map of classifying spaces. The original group-to-fundamental-group equivalence
is natural for this map. Consequently the induced map on the actual first
homotopy group has precisely the original algebraic kernel.

This supplies a reusable interface for inclusions and normal quotient maps;
it makes no plus-construction or higher K-theory comparison assertion.

Implementation provenance: `Quillen/Topology/ClassifyingSpace/GroupHom.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the realized original group elements.
-/
@[expose] public section

noncomputable section

universe u
open CategoryTheory Topology

namespace CategoryTheory.GroupoidClassifying

variable {G H K : Type u} [Group G] [Group H] [Group K]

/-- The genuine classifying-space map associated to a group homomorphism. -/
def classifyingMap (f : G →* H) :
    ClassifyingSpace (SingleObj G) ⟶ ClassifyingSpace (SingleObj H) :=
  classifyingSpaceMap f.toFunctor

@[simp] lemma classifyingMap_point (f : G →* H) :
    classifyingMap f (classifyingSpacePoint (SingleObj.star G)) =
      classifyingSpacePoint (SingleObj.star H) :=
  classifyingSpaceMap_point f.toFunctor _

@[simp] lemma classifyingMap_id :
    classifyingMap (MonoidHom.id G) = 𝟙 (ClassifyingSpace (SingleObj G)) :=
  classifyingSpaceMap_id

@[simp] lemma classifyingMap_comp (f : G →* H) (g : H →* K) :
    classifyingMap (g.comp f) = classifyingMap f ≫ classifyingMap g :=
  classifyingSpaceMap_comp f.toFunctor g.toFunctor

/-- The induced homomorphism on the actual first based homotopy groups. -/
def piOneMap (f : G →* H) :
    HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj G))
        (classifyingSpacePoint (SingleObj.star G)) →*
      HomotopyGroup.Pi 1 (ClassifyingSpace (SingleObj H))
        (classifyingSpacePoint (SingleObj.star H)) :=
  HomotopyGroup.piMap 0 (classifyingMap f).hom (classifyingMap_point f)

/-- Naturality retains the original group element as its realized edge loop. -/
lemma piOneMap_equiv (f : G →* H) (g : G) :
    piOneMap f (singleObjPiOneEquiv G g) = singleObjPiOneEquiv H (f g) := by
  apply congrArg Quotient.mk'
  ext t
  exact classifyingSpacePath_naturality f.toFunctor (SingleObj.toEnd G g).asHom (t 0)

/-- The induced map is conjugate to the original homomorphism by the canonical equivalences. -/
lemma piOneMap_comp_equiv (f : G →* H) :
    (piOneMap f).comp (singleObjPiOneEquiv G).toMonoidHom =
      (singleObjPiOneEquiv H).toMonoidHom.comp f := by
  ext g
  exact piOneMap_equiv f g

/-- The algebraic kernel is exactly the kernel on realized first homotopy groups. -/
lemma piOneMap_equiv_eq_one_iff (f : G →* H) (g : G) :
    piOneMap f (singleObjPiOneEquiv G g) = 1 ↔ f g = 1 := by
  rw [piOneMap_equiv, ← map_one (singleObjPiOneEquiv H)]
  exact (singleObjPiOneEquiv H).injective.eq_iff

/-- Surjective group homomorphisms give surjective maps on first homotopy groups. -/
lemma piOneMap_surjective (f : G →* H) (hf : Function.Surjective f) :
    Function.Surjective (piOneMap f) := by
  intro y
  obtain ⟨h, rfl⟩ := (singleObjPiOneEquiv H).surjective y
  obtain ⟨g, rfl⟩ := hf h
  exact ⟨singleObjPiOneEquiv G g, piOneMap_equiv f g⟩

/-- Injective group homomorphisms give injective maps on first homotopy groups. -/
lemma piOneMap_injective (f : G →* H) (hf : Function.Injective f) :
    Function.Injective (piOneMap f) := by
  intro x y h
  obtain ⟨a, rfl⟩ := (singleObjPiOneEquiv G).surjective x
  obtain ⟨b, rfl⟩ := (singleObjPiOneEquiv G).surjective y
  rw [piOneMap_equiv, piOneMap_equiv] at h
  exact congrArg (singleObjPiOneEquiv G) (hf ((singleObjPiOneEquiv H).injective h))

end CategoryTheory.GroupoidClassifying
