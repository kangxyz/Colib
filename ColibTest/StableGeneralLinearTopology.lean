/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.GroupTheory.StableGeneralLinear.ElementaryQuotient
import Colib.Topology.ClassifyingSpace.FundamentalGroup
import Colib.Topology.ClassifyingSpace.Groupoid
import Colib.Topology.ClassifyingSpace.StableElementaryQuotient
import Colib.Topology.ClassifyingSpace.StableGeneralLinearGrothendieck
import Colib.Topology.ClassifyingSpace.UniverseHomotopy

/-! Regression checks retain the original matrices, group elements, functors,
realized arrows, independent category universes and whole homotopy tracks. -/

noncomputable section
open CategoryTheory Topology
universe u v u' v'

example (R : Type u) [Ring R] :
    StableGeneralLinear.elementary R = commutator (StableGeneralLinear.Group R) :=
  StableGeneralLinear.elementary_eq_commutator R

example (R : Type u) [Ring R] (g : StableGeneralLinear.Group R) :
    StableGeneralLinear.quotientMap R g = 1 ↔ g ∈ StableGeneralLinear.elementary R :=
  StableGeneralLinear.quotientMap_eq_one R g

example (C : Type u) [Category.{v} C] [IsGroupoid C] (c : C) :
    Function.Bijective ((classifyingFundamentalGroupoidFunctor C).mapEnd c) :=
  GroupoidClassifying.fundamentalGroupMap_bijective_general c

example (G : Type u) [Group G] (g : G) :
    GroupoidClassifying.singleObjPiOneEquiv G g =
      HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (Path.Homotopic.Quotient.mk (classifyingSpacePath (SingleObj.toEnd G g))) :=
  GroupoidClassifying.singleObjPiOneEquiv_apply G g

example (G : Type u) [Group G] (n : ℕ) :
    Subsingleton (HomotopyGroup.Pi (n + 2) (ClassifyingSpace (SingleObj G))
      (classifyingSpacePoint (SingleObj.star G))) :=
  GroupoidClassifying.singleObj_subsingleton_higher_pi G n

example (R : Type u) [Ring R] (g : StableGeneralLinear.Group R) :
    StableGeneralLinear.quotientPiOneMap R
        (GroupoidClassifying.singleObjPiOneEquiv (StableGeneralLinear.Group R) g) = 1 ↔
      g ∈ StableGeneralLinear.elementary R :=
  StableGeneralLinear.quotientPiOneMap_equiv_eq_one_iff R g

example (R : Type u) [Ring R] :
    (StableGeneralLinear.quotientPiOneMap R).ker =
      (StableGeneralLinear.elementary R).map
        (GroupoidClassifying.singleObjPiOneEquiv
          (StableGeneralLinear.Group R)).toMonoidHom :=
  StableGeneralLinear.ker_quotientPiOneMap R

example {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    (F : C ⥤ D) {c d : C} (f : c ⟶ d) (t : unitInterval) :
    classifyingSpaceMapUniversal F (classifyingSpacePath f t) =
      classifyingSpacePath (F.map f) t :=
  classifyingSpaceMapUniversal_path F f t

example {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F G : C ⥤ D} (α : F ⟶ G) (c : C) (t : unitInterval) :
    classifyingSpaceUniversalHomotopy α (t, classifyingSpacePoint c) =
      classifyingSpacePath (α.app c) t :=
  classifyingSpaceUniversalHomotopy_vertex_track α c t
