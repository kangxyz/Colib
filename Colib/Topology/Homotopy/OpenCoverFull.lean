/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.CategoryTheory.Groupoid.TransportedImage
public import Colib.Topology.Homotopy.OpenCover

/-!
# Fundamental-groupoid fullness from an open cover

An open set `U` and pairwise disjoint simply connected open sets `V i` cover a
space. If each overlap `U ∩ V i` is path-connected, the inclusion of `U` induces
a full functor on fundamental groupoids. This concerns arbitrary actual paths,
not an assumed cellular path decomposition. Faithfulness is not asserted.


## Implementation provenance

Extracted from `Quillen/Topology/Realization/EdgePathPresentation/OpenCoverFull.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
universes, maps and hypotheses are retained.
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory Set Topology
open scoped Topology unitInterval

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section OpenCover

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/-- A path whose endpoints and image lie in a subset, regarded as a path in
that subset with its actual subspace topology. -/
def Path.inSubset {U : Set X} {x y : U} (p : Path x.1 y.1)
    (hp : Set.range p ⊆ U) : Path x y where
  toFun t := ⟨p t, hp (Set.mem_range_self t)⟩
  continuous_toFun := p.continuous.subtype_mk _
  source' := Subtype.ext p.source
  target' := Subtype.ext p.target

@[simp] theorem Path.inSubset_map {U : Set X} {x y : U} (p : Path x.1 y.1)
    (hp : Set.range p ⊆ U) :
    (Path.inSubset p hp).map continuous_subtype_val = p := by
  ext t
  rfl

/-- A path connecting a point to the base open set, simultaneously remaining
in every cell chart containing that point. -/
structure Topology.OpenCoverAnchor (U : Set X) (V : ι → Set X) (x : X) where
  /-- An anchor point in the base open set `U`. -/
  point : U
  /-- A path from the anchor point to `x`. -/
  path : Path point.1 x
  /-- When `x` lies in `U`, the anchor path remains in `U`. -/
  in_base : x ∈ U → Set.range path ⊆ U
  /-- For each chart containing `x`, the anchor path remains in that chart. -/
  in_chart : ∀ i, x ∈ V i → Set.range path ⊆ V i

/-- Pairwise disjoint cell charts with connected overlaps supply compatible
anchor paths to the base open set. -/
theorem Topology.exists_openCoverAnchor
    (U : Set X) (V : ι → Set X)
    (hcover : Set.univ ⊆ U ∪ ⋃ i, V i)
    (hdisj : Pairwise (fun i j ↦ Disjoint (V i) (V j)))
    (hconn : ∀ i, IsPathConnected (V i))
    (hoverlap : ∀ i, IsPathConnected (U ∩ V i)) (x : X) :
    Nonempty (Topology.OpenCoverAnchor U V x) := by
  classical
  by_cases hx : x ∈ U
  · refine ⟨⟨⟨x, hx⟩, Path.refl x, ?_, ?_⟩⟩
    · intro _
      rintro _ ⟨t, rfl⟩
      exact hx
    · intro i hxi
      rintro _ ⟨t, rfl⟩
      exact hxi
  · obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp ((hcover (Set.mem_univ x)).resolve_left hx)
    obtain ⟨a, ha⟩ := (hoverlap i).nonempty
    let hpath := (hconn i).joinedIn a ha.2 x hxi
    refine ⟨⟨⟨a, ha.1⟩, hpath.somePath, fun h ↦ (hx h).elim, ?_⟩⟩
    intro k hxk
    have hik : i = k := by
      by_contra hne
      exact (Set.disjoint_left.mp (hdisj hne)) hxi hxk
    subst k
    exact Set.range_subset_iff.mpr hpath.somePath_mem

/-- A path traversing two anchors and a local path stays inside a set whenever
all three constituent paths do. -/
theorem Path.range_anchor_concat_subset {U : Set X} {a x y b : X}
    (α : Path a x) (p : Path x y) (β : Path b y)
    (hα : Set.range α ⊆ U) (hp : Set.range p ⊆ U) (hβ : Set.range β ⊆ U) :
    Set.range ((α.trans p).trans β.symm) ⊆ U := by
  rw [Path.trans_range, Path.trans_range, Path.symm_range]
  exact Set.union_subset (Set.union_subset hα hp) hβ

/-- An open base together with disjoint simply connected open cells has no
new fundamental-groupoid generators when all cell/base overlaps are
path-connected. This is a statement about arbitrary actual continuous paths. -/
theorem FundamentalGroupoid.openInclusion_full
    (U : Set X) (V : ι → Set X) (hU : IsOpen U) (hV : ∀ i, IsOpen (V i))
    (hcover : Set.univ ⊆ U ∪ ⋃ i, V i)
    (hdisj : Pairwise (fun i j ↦ Disjoint (V i) (V j)))
    (hsc : ∀ i, IsSimplyConnected (V i))
    (hoverlap : ∀ i, IsPathConnected (U ∩ V i)) :
    (FundamentalGroupoid.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))).Full := by
  classical
  let anchor (x : X) : Topology.OpenCoverAnchor U V x :=
    Classical.choice (Topology.exists_openCoverAnchor U V hcover hdisj
      (fun i ↦ (hsc i).isPathConnected) hoverlap x)
  let F : FundamentalGroupoid U ⥤ FundamentalGroupoid X :=
    FundamentalGroupoid.map ⟨Subtype.val, continuous_subtype_val⟩
  let a (x : FundamentalGroupoid X) : FundamentalGroupoid U :=
    FundamentalGroupoid.mk (anchor x.as).point
  let e (x : FundamentalGroupoid X) : F.obj (a x) ≅ x :=
    (Groupoid.isoEquivHom _ _).symm ⟦(anchor x.as).path⟧
  let S := transportedImageSubgroupoid F a e
  have hmem {x y : X} (p : Path x y)
      (q : Path (anchor x).point (anchor y).point)
      (H : (q.map continuous_subtype_val).Homotopic
        (((anchor x).path.trans p).trans (anchor y).path.symm)) :
      (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ S.arrows _ _ := by
    refine ⟨(⟦q⟧ : a (FundamentalGroupoid.mk x) ⟶ a (FundamentalGroupoid.mk y)), ?_⟩
    change (Path.Homotopic.Quotient.mk q).map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) =
      (Path.Homotopic.Quotient.mk (anchor x).path).trans
        ((Path.Homotopic.Quotient.mk p).trans
          (Path.Homotopic.Quotient.mk (anchor y).path.symm))
    rw [← Path.Homotopic.Quotient.mk_map]
    have h : Path.Homotopic.Quotient.mk (q.map continuous_subtype_val) =
        Path.Homotopic.Quotient.mk (((anchor x).path.trans p).trans (anchor y).path.symm) :=
      Quotient.sound H
    simpa only [Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.trans_assoc] using h
  let W : Option ι → Set X := fun i ↦ i.elim U V
  have htop : S = ⊤ := by
    apply FundamentalGroupoid.subgroupoid_eq_top_of_openCover S W
    · rintro (_ | i)
      · exact hU
      · exact hV i
    · intro x _
      rcases hcover (Set.mem_univ x) with hx | hx
      · exact Set.mem_iUnion.mpr ⟨none, hx⟩
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
        exact Set.mem_iUnion.mpr ⟨some i, hi⟩
    · rintro (_ | i) x y p hp
      · change Set.range p ⊆ U at hp
        let r := ((anchor x).path.trans p).trans (anchor y).path.symm
        have hr : Set.range r ⊆ U :=
          Path.range_anchor_concat_subset _ _ _
            ((anchor x).in_base (hp p.source_mem_range)) hp
            ((anchor y).in_base (hp p.target_mem_range))
        apply hmem p (Path.inSubset r hr)
        rw [Path.inSubset_map]
      · change Set.range p ⊆ V i at hp
        let r := ((anchor x).path.trans p).trans (anchor y).path.symm
        have hα := (anchor x).in_chart i (hp p.source_mem_range)
        have hβ := (anchor y).in_chart i (hp p.target_mem_range)
        have hr : Set.range r ⊆ V i := Path.range_anchor_concat_subset _ _ _ hα hp hβ
        have hj := (hoverlap i).joinedIn (anchor x).point.1
          ⟨(anchor x).point.2, hα (anchor x).path.source_mem_range⟩
          (anchor y).point.1 ⟨(anchor y).point.2, hβ (anchor y).path.source_mem_range⟩
        let q := hj.somePath
        have hqU : Set.range q ⊆ U := by
          rintro _ ⟨t, rfl⟩
          exact (hj.somePath_mem t).1
        have hqV : Set.range q ⊆ V i := by
          rintro _ ⟨t, rfl⟩
          exact (hj.somePath_mem t).2
        apply hmem p (Path.inSubset q hqU)
        rw [Path.inSubset_map]
        exact Path.homotopic_of_range_subset_isSimplyConnected (hsc i) q r hqV hr
  change F.Full
  constructor
  intro x y p
  have hpS : p ∈ S.arrows (F.obj x) (F.obj y) := by
    rw [htop]
    trivial
  obtain ⟨q, hq⟩ := hpS
  let α : Path (anchor x.as.1).point x.as :=
    Path.inSubset (anchor x.as.1).path ((anchor x.as.1).in_base x.as.2)
  let β : Path (anchor y.as.1).point y.as :=
    Path.inSubset (anchor y.as.1).path ((anchor y.as.1).in_base y.as.2)
  let α' : a (F.obj x) ⟶ x := ⟦α⟧
  let β' : a (F.obj y) ⟶ y := ⟦β⟧
  have hα : F.map α' = (e (F.obj x)).hom := by
    change Path.Homotopic.Quotient.mk (α.map continuous_subtype_val) =
      Path.Homotopic.Quotient.mk (anchor x.as.1).path
    rw [show α.map continuous_subtype_val = (anchor x.as.1).path from Path.inSubset_map _ _]
  have hβ : F.map β' = (e (F.obj y)).hom := by
    change Path.Homotopic.Quotient.mk (β.map continuous_subtype_val) =
      Path.Homotopic.Quotient.mk (anchor y.as.1).path
    rw [show β.map continuous_subtype_val = (anchor y.as.1).path from Path.inSubset_map _ _]
  have hαinv : F.map (inv α') = (e (F.obj x)).inv := by
    rw [F.map_inv]
    simpa [Groupoid.inv_eq_inv] using congrArg Groupoid.inv hα
  refine ⟨inv α' ≫ q ≫ β', ?_⟩
  rw [F.map_comp, F.map_comp, hαinv, hq, hβ]
  simp [Category.assoc]

end OpenCover

attribute [colib_tag "COL-0097",
  colib_ref "HatcherAT" "Section 1.1, Lemma 1.15 and proof, page 35"
    "background"
    "Open-cover path subdivision and anchor transport for fullness, not faithfulness"]
  FundamentalGroupoid.openInclusion_full

attribute [colib_ref "HatcherAT" "Section 1.1, Proposition 1.6, page 28"
  "ingredient" "Fixed-endpoint path homotopy inside each simply connected cover member"]
  FundamentalGroupoid.openInclusion_full
