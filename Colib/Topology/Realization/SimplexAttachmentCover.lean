/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Colib.Topology.Realization.SimplexAnnulus
public import Colib.Topology.Realization.SimplexAttachmentCollar
public import Colib.Topology.Category.TopCat.PushoutInteriors

/-!
# Genuine open charts for a discrete family of simplex attachments

The old-space collar and the individual open cell interiors cover the actual
attachment pushout. The interior charts are pairwise disjoint and simply
connected. In dimension at least two, each overlap with the collar is
nonempty and path-connected.

## Implementation provenance

Adapted from all ten declarations of
`Quillen/Topology/Realization/EdgePathPresentation/Cover.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual chart maps, attaching
pushout, parameter discreteness requirements and dimension bounds are retained.
The coordinates use the native finitely supported simplex. In particular, the old space is
not assumed discrete. The deformation import is reduced to its collar input.
-/
@[expose] public section


noncomputable section
open CategoryTheory CategoryTheory.Limits Topology Set
open Convexity.StdSimplex
open scoped Topology unitInterval

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TopCat

/-- The attaching locus is exactly the parametrized geometric boundary. -/
theorem mem_range_parameterizedSimplexBoundary_iff (X : TopCat.{u}) (n : ℕ)
    (z : X × Convexity.StdSimplex ℝ (Fin (n + 1))) :
    z ∈ Set.range (TopCat.parameterizedSimplexBoundaryInclusion X n) ↔
      z.2 ∈ Convexity.StdSimplex.boundary n := by
  constructor
  · rintro ⟨⟨a, b⟩, rfl⟩
    exact b.2
  · intro hz
    exact ⟨(z.1, ⟨z.2, hz⟩), rfl⟩

section SimplexAttachment

variable (X : TopCat.{u}) [DiscreteTopology X] (n : ℕ) {C D : TopCat.{u}}
    {f : TopCat.of (X × Convexity.StdSimplex.boundary n) ⟶ C}
    {g : TopCat.of (X × Convexity.StdSimplex ℝ (Fin (n + 1))) ⟶ D}
    {j : C ⟶ D}
    (sq : IsPushout (TopCat.parameterizedSimplexBoundaryInclusion X n) f g j)

/-- The interior chart of one simplex in the attaching family. -/
def simplexAttachmentInteriorMap (a : X) : C(simplexInterior n, D) where
  toFun x := g (a, x.1)
  continuous_toFun := g.hom.continuous.comp (continuous_const.prodMk continuous_subtype_val)

/-- The open subset traced out by one interior chart. -/
def simplexAttachmentInterior (a : X) : Set D :=
  Set.range (simplexAttachmentInteriorMap X n (g := g) a)

include sq in
/-- Each individual interior chart has exactly its geometric topology and is
open in the actual attachment pushout. -/
theorem isOpenEmbedding_simplexAttachmentInteriorMap (a : X) :
    IsOpenEmbedding (simplexAttachmentInteriorMap X n (g := g) a) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (simplexAttachmentInteriorMap X n (g := g) a).continuous
  · intro x y h
    have hx : (a, x.1) ∉ Set.range (TopCat.parameterizedSimplexBoundaryInclusion X n) := by
      rw [mem_range_parameterizedSimplexBoundary_iff]
      rintro ⟨i, hi⟩
      exact (ne_of_gt (x.2 i)) hi
    exact Subtype.ext (congrArg Prod.snd (pushout_cell_eq_of_not_mem_range sq hx h))
  · intro W hW
    have hW' : IsOpen (((↑) : simplexInterior n → Convexity.StdSimplex ℝ (Fin (n + 1))) '' W) :=
      (isOpen_simplexInterior n).isOpenEmbedding_subtypeVal.isOpenMap W hW
    let B' : Set (X × Convexity.StdSimplex ℝ (Fin (n + 1))) :=
      {a} ×ˢ (((↑) : simplexInterior n → Convexity.StdSimplex ℝ (Fin (n + 1))) '' W)
    have hB' : IsOpen B' := (isOpen_discrete _).prod hW'
    have hdisj : B' ⊆ (Set.range (TopCat.parameterizedSimplexBoundaryInclusion X n))ᶜ := by
      rintro ⟨a', x⟩ ⟨ha', y, hy, rfl⟩
      rw [Set.mem_compl_iff, mem_range_parameterizedSimplexBoundary_iff]
      rintro ⟨i, hi⟩
      exact (ne_of_gt (y.2 i)) hi
    have hopen := isOpen_pushout_cell_image sq
      (isClosedEmbedding_parameterizedSimplexBoundary X n).injective B' hB' hdisj
    convert hopen using 1
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(a, x.1), ⟨rfl, ⟨x, hx, rfl⟩⟩, rfl⟩
    · rintro ⟨⟨a', x⟩, ⟨ha', y, hy, hxy⟩, hz⟩
      have haa : a' = a := ha'
      subst a'
      change y.1 = x at hxy
      subst x
      exact ⟨y, hy, hz⟩

include sq in
theorem isOpen_simplexAttachmentInterior (a : X) :
    IsOpen (simplexAttachmentInterior X n (g := g) a) :=
  (isOpenEmbedding_simplexAttachmentInteriorMap X n sq a).isOpen_range

include sq in
/-- Each cell interior is simply connected, independently of the old space
or of the attaching map. -/
theorem isSimplyConnected_simplexAttachmentInterior (a : X) :
    IsSimplyConnected (simplexAttachmentInterior X n (g := g) a) := by
  let := (isSimplyConnected_simplexInterior n).simplyConnectedSpace
  exact (isOpenEmbedding_simplexAttachmentInteriorMap X n sq a).isEmbedding.toHomeomorph.symm
    |>.toHomotopyEquiv |>.simplyConnectedSpace

omit [DiscreteTopology X] in
include sq in
/-- Distinct open cell interiors remain disjoint in the attachment. -/
theorem pairwiseDisjoint_simplexAttachmentInteriors :
    Pairwise (fun a b : X ↦ Disjoint (simplexAttachmentInterior X n (g := g) a)
      (simplexAttachmentInterior X n (g := g) b)) := by
  intro a b hab
  rw [Set.disjoint_left]
  rintro z ⟨x, hx⟩ ⟨y, hy⟩
  have hxout : (a, x.1) ∉ Set.range (TopCat.parameterizedSimplexBoundaryInclusion X n) := by
    rw [mem_range_parameterizedSimplexBoundary_iff]
    rintro ⟨i, hi⟩
    exact (ne_of_gt (x.2 i)) hi
  apply hab
  exact congrArg Prod.fst (pushout_cell_eq_of_not_mem_range sq hxout (hx.trans hy.symm))

omit [DiscreteTopology X] in
/-- The overlap with one interior chart is exactly the image of the geometric
open annulus, with no approximation or lifting hypothesis. -/
theorem simplexAttachmentCollar_inter_interior (a : X) :
    simplexAttachmentCollar X n sq ∩ simplexAttachmentInterior X n (g := g) a =
      (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) ↦ g (a, x)) '' simplexAnnulus n := by
  ext z
  constructor
  · rintro ⟨hz, x, rfl⟩
    exact ⟨x.1, ⟨(simplexAttachmentCollar_cell_iff X n sq (a, x.1)).mp hz, x.2⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(simplexAttachmentCollar_cell_iff X n sq (a, x)).mpr hx.1,
      ⟨⟨x, hx.2⟩, rfl⟩⟩

omit [DiscreteTopology X] in
/-- In dimensions at least two, each interior/collar overlap is nonempty and
path-connected. -/
theorem isPathConnected_simplexAttachmentCollar_inter_interior
    (hn : 2 ≤ n) (a : X) :
    IsPathConnected (simplexAttachmentCollar X n sq ∩
      simplexAttachmentInterior X n (g := g) a) := by
  rw [simplexAttachmentCollar_inter_interior]
  exact (isPathConnected_simplexAnnulus hn).image (by fun_prop)

omit [DiscreteTopology X] in
/-- The old-space collar together with the open cell interiors covers every
point of the actual topological attachment. -/
theorem simplexAttachmentCollar_union_interiors :
    simplexAttachmentCollar X n sq ∪ (⋃ a : X, simplexAttachmentInterior X n (g := g) a) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) z with ⟨b, hb⟩ | ⟨c, hc⟩
  · change g b = z at hb
    by_cases hbi : b.2 ∈ simplexInterior n
    · right
      rw [← hb]
      exact Set.mem_iUnion.mpr ⟨b.1, ⟨⟨b.2, hbi⟩, rfl⟩⟩
    · left
      have hbd : b.2 ∈ Convexity.StdSimplex.boundary n := by
        rw [simplexInterior_eq_compl_boundary] at hbi
        simpa only [Set.mem_compl_iff, not_not] using hbi
      rw [← hb]
      apply (simplexAttachmentCollar_cell_iff X n sq b).mpr
      exact simplexBoundary_subset_collar n hbd
  · left
    exact range_old_subset_simplexAttachmentCollar X n sq ⟨c, hc⟩

end SimplexAttachment

end TopCat

attribute [colib_tag "COL-0104",
  colib_ref "BoardmanPushouts" "Proposition 11(b), page 3"
    "ingredient"
    "Open complement charts in the actual attachment pushout"]
  TopCat.isOpenEmbedding_simplexAttachmentInteriorMap
  TopCat.isOpen_simplexAttachmentInterior

attribute [colib_tag "COL-0104",
  colib_ref "HatcherAT" "Section 1.2, proof of Proposition 1.26, pages 50-51"
    "background"
    "Attachment cover geometry, not the exact defect collar or fundamental-group presentation"]
  TopCat.isSimplyConnected_simplexAttachmentInterior
  TopCat.pairwiseDisjoint_simplexAttachmentInteriors
  TopCat.simplexAttachmentCollar_inter_interior
  TopCat.isPathConnected_simplexAttachmentCollar_inter_interior
  TopCat.simplexAttachmentCollar_union_interiors
