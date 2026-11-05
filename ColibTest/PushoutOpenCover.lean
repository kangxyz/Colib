/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Category.TopCat.PushoutInteriors
import Colib.Topology.Homotopy.OpenCoverFull

/-!
# Pushout interiors and open-inclusion fullness regression tests

The transported image requires chosen object isomorphisms, not object injectivity.
The open inclusion is full under all stated cover hypotheses; no faithfulness
or equivalence assertion is made.
-/

open CategoryTheory CategoryTheory.Limits Topology
open scoped Topology unitInterval

universe u v w

noncomputable section

section Pushout

variable {A B C D : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ D} {j : C ⟶ D}
  (sq : IsPushout i f g j)

example (hi : IsClosedEmbedding i) : IsClosedEmbedding j :=
  TopCat.isClosedEmbedding_pushout_right sq hi

example {b b' : B} (hb : b ∉ Set.range i) (h : g b = g b') : b = b' :=
  TopCat.pushout_cell_eq_of_not_mem_range sq hb h

example (hi : Function.Injective i) (W : Set B) (hW : IsOpen W)
    (hdisj : W ⊆ (Set.range i)ᶜ) : IsOpen (g '' W) :=
  TopCat.isOpen_pushout_cell_image sq hi W hW hdisj

example (hi : IsClosedEmbedding i) :
    IsOpenEmbedding (fun b : ↥((Set.range i)ᶜ) ↦ g b.1) :=
  TopCat.isOpenEmbedding_pushout_cell_compl sq hi

example (hi : Function.Injective i) :
    Set.range (fun b : ↥((Set.range i)ᶜ) ↦ g b.1) = (Set.range j)ᶜ :=
  TopCat.range_pushout_cell_compl sq hi

example [T1Space B] [T1Space C] (hi : IsClosedEmbedding i) : T1Space D :=
  TopCat.t1Space_pushout_of_closedEmbedding sq hi

end Pushout

section Groupoids

variable {A : Type u} {G : Type v} [Groupoid A] [Groupoid G]
  (F : A ⥤ G) (a : G → A) (e : ∀ x, F.obj (a x) ≅ x)

example {x y : G} (p : x ⟶ y) :
    p ∈ (transportedImageSubgroupoid F a e).arrows x y ↔
      ∃ q : a x ⟶ a y, F.map q = (e x).hom ≫ p ≫ (e y).inv := Iff.rfl

example {x y : G} (q : a x ⟶ a y) :
    (e x).inv ≫ F.map q ≫ (e y).hom ∈
      (transportedImageSubgroupoid F a e).arrows x y := by
  refine ⟨q, ?_⟩
  simp

end Groupoids

section OpenCover

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

example {U : Set X} {x y : U} (p : Path x.1 y.1) (hp : Set.range p ⊆ U)
    (t : unitInterval) : (Path.inSubset p hp t).1 = p t := rfl

example {U : Set X} {x y : U} (p : Path x.1 y.1) (hp : Set.range p ⊆ U) :
    (Path.inSubset p hp).map continuous_subtype_val = p := Path.inSubset_map p hp

example (U : Set X) (V : ι → Set X)
    (hcover : Set.univ ⊆ U ∪ ⋃ i, V i)
    (hdisj : Pairwise (fun i j ↦ Disjoint (V i) (V j)))
    (hconn : ∀ i, IsPathConnected (V i))
    (hoverlap : ∀ i, IsPathConnected (U ∩ V i)) (x : X) :
    Nonempty (Topology.OpenCoverAnchor U V x) :=
  Topology.exists_openCoverAnchor U V hcover hdisj hconn hoverlap x

example (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hcover : Set.univ ⊆ U ∪ ⋃ i, V i)
    (hdisj : Pairwise (fun i j ↦ Disjoint (V i) (V j)))
    (hsc : ∀ i, IsSimplyConnected (V i))
    (hoverlap : ∀ i, IsPathConnected (U ∩ V i)) :
    (FundamentalGroupoid.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).Full :=
  FundamentalGroupoid.openInclusion_full U V hU hV hcover hdisj hsc hoverlap

end OpenCover
