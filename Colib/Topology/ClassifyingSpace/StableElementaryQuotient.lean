/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.GroupTheory.StableGeneralLinear.ElementaryQuotient
public import Colib.Topology.ClassifyingSpace.GroupHom

/-!
# The elementary quotient on genuine classifying spaces

Realizing the original projection `GL(R) → GL(R)/E(R)` gives a pointed map
of classifying spaces. Its map on the actual fundamental groups is surjective
and its kernel is precisely the image of `E(R)` under the original edge-loop
equivalence. Change of rings preserves this map.

This quotient map is not asserted to be a plus construction: no homology
equivalence or higher-homotopy comparison follows from its fundamental group.

Implementation provenance: `Quillen/Topology/ClassifyingSpace/StableElementaryQuotient.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the realized original group elements.
-/
@[expose] public section

noncomputable section

universe u

open CategoryTheory Topology

namespace StableGeneralLinear

variable (R : Type u) [Ring R]

/-- The genuine realization of the original quotient homomorphism. -/
def classifyingQuotientMap :
    ClassifyingSpace (SingleObj (Group R)) ⟶
      ClassifyingSpace (SingleObj (ElementaryQuotient R)) :=
  GroupoidClassifying.classifyingMap (quotientMap R)

@[simp] lemma classifyingQuotientMap_point :
    classifyingQuotientMap R (classifyingSpacePoint (SingleObj.star (Group R))) =
      classifyingSpacePoint (SingleObj.star (ElementaryQuotient R)) :=
  GroupoidClassifying.classifyingMap_point (quotientMap R)

/-- The induced homomorphism on actual based first homotopy groups. -/
abbrev quotientPiOneMap := GroupoidClassifying.piOneMap (quotientMap R)

/-- The map on fundamental groups keeps the original stable matrix representative. -/
lemma quotientPiOneMap_equiv (g : Group R) :
    quotientPiOneMap R (GroupoidClassifying.singleObjPiOneEquiv (Group R) g) =
      GroupoidClassifying.singleObjPiOneEquiv (ElementaryQuotient R) (quotientMap R g) :=
  GroupoidClassifying.piOneMap_equiv (quotientMap R) g

lemma quotientPiOneMap_surjective : Function.Surjective (quotientPiOneMap R) :=
  GroupoidClassifying.piOneMap_surjective (quotientMap R) (quotientMap_surjective R)

/-- A stable matrix loop is killed exactly when the matrix is elementary. -/
lemma quotientPiOneMap_equiv_eq_one_iff (g : Group R) :
    quotientPiOneMap R (GroupoidClassifying.singleObjPiOneEquiv (Group R) g) = 1 ↔
      g ∈ elementary R := by
  rw [GroupoidClassifying.piOneMap_equiv_eq_one_iff, quotientMap_eq_one]

/-- The actual fundamental-group kernel is the transported elementary subgroup. -/
theorem ker_quotientPiOneMap :
    (quotientPiOneMap R).ker = (elementary R).map
      (GroupoidClassifying.singleObjPiOneEquiv (Group R)).toMonoidHom := by
  ext x
  obtain ⟨g, rfl⟩ := (GroupoidClassifying.singleObjPiOneEquiv (Group R)).surjective x
  rw [MonoidHom.mem_ker, quotientPiOneMap_equiv_eq_one_iff]
  constructor
  · exact fun hg => Subgroup.mem_map_of_mem _ hg
  · rintro ⟨h, hh, he⟩
    exact (GroupoidClassifying.singleObjPiOneEquiv (Group R)).injective he ▸ hh

section RingMap

variable {R} {S : Type u} [Ring S]

/-- Realization retains the commuting square of the original quotient projections. -/
lemma classifyingQuotientMap_naturality (f : R →+* S) :
    GroupoidClassifying.classifyingMap (map f) ≫ classifyingQuotientMap S =
      classifyingQuotientMap R ≫ GroupoidClassifying.classifyingMap (quotientRingMap f) := by
  change GroupoidClassifying.classifyingMap (map f) ≫
      GroupoidClassifying.classifyingMap (quotientMap S) =
    GroupoidClassifying.classifyingMap (quotientMap R) ≫
      GroupoidClassifying.classifyingMap (quotientRingMap f)
  rw [← GroupoidClassifying.classifyingMap_comp, ← GroupoidClassifying.classifyingMap_comp,
    quotientMap_naturality]

/-- The naturality square also commutes on the actual fundamental groups. -/
lemma quotientPiOneMap_naturality (f : R →+* S) :
    (quotientPiOneMap S).comp (GroupoidClassifying.piOneMap (map f)) =
      (GroupoidClassifying.piOneMap (quotientRingMap f)).comp (quotientPiOneMap R) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨g, rfl⟩ := (GroupoidClassifying.singleObjPiOneEquiv (Group R)).surjective x
  simp only [MonoidHom.comp_apply, quotientPiOneMap, GroupoidClassifying.piOneMap_equiv,
    quotientRingMap_quotientMap]

end RingMap

end StableGeneralLinear
