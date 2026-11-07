/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Realization.SimplexAttachmentPathGeneration
import Colib.Topology.Realization.SimplexAttachmentFullness

/-!
# Attachment cover, path generation and fullness regression tests

Generation uses old-space and entire-cell paths in every dimension. Fullness
requires dimension at least two and discrete parameters; it is not faithfulness.
-/

open CategoryTheory CategoryTheory.Limits Convexity.StdSimplex Topology
open scoped Topology unitInterval

universe u

noncomputable section

namespace TopCat

variable (X : TopCat.{u}) (n : ℕ) {C D : TopCat.{u}}
  {f : TopCat.of (X × boundary n) ⟶ C}
  {g : TopCat.of (X × Convexity.StdSimplex ℝ (Fin (n + 1))) ⟶ D} {j : C ⟶ D}
  (sq : IsPushout (parameterizedSimplexBoundaryInclusion X n) f g j)

example (a : X) (x : simplexInterior n) :
    simplexAttachmentInteriorMap X n (g := g) a x = g (a, x.1) := rfl

example (a : X) : simplexAttachmentInterior X n (g := g) a =
    Set.range (simplexAttachmentInteriorMap X n (g := g) a) := rfl

example : Pairwise (fun a b : X ↦ Disjoint (simplexAttachmentInterior X n (g := g) a)
    (simplexAttachmentInterior X n (g := g) b)) :=
  pairwiseDisjoint_simplexAttachmentInteriors X n sq

example (a : X) :
    simplexAttachmentCollar X n sq ∩ simplexAttachmentInterior X n (g := g) a =
      (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) ↦ g (a, x)) '' simplexAnnulus n :=
  simplexAttachmentCollar_inter_interior X n sq a

example (hn : 2 ≤ n) (a : X) :
    IsPathConnected (simplexAttachmentCollar X n sq ∩
      simplexAttachmentInterior X n (g := g) a) :=
  isPathConnected_simplexAttachmentCollar_inter_interior X n sq hn a

example : simplexAttachmentCollar X n sq ∪
    (⋃ a : X, simplexAttachmentInterior X n (g := g) a) = Set.univ :=
  simplexAttachmentCollar_union_interiors X n sq

variable [DiscreteTopology X]

example (a : X) : IsOpenEmbedding (simplexAttachmentInteriorMap X n (g := g) a) :=
  isOpenEmbedding_simplexAttachmentInteriorMap X n sq a

example (a : X) : IsOpen (simplexAttachmentInterior X n (g := g) a) :=
  isOpen_simplexAttachmentInterior X n sq a

example (a : X) : IsSimplyConnected (simplexAttachmentInterior X n (g := g) a) :=
  isSimplyConnected_simplexAttachmentInterior X n sq a

example (a : X) (x : Convexity.StdSimplex ℝ (Fin (n + 1))) :
    simplexAttachmentCellMap X n (g := g) a x = g (a, x) := rfl

example (hn : 2 ≤ n) : (FundamentalGroupoid.map j.hom).Full :=
  simplexAttachment_fundamentalGroupoid_full X n sq hn

example (hn : 2 ≤ n) {c d : C} (p : Path (j c) (j d)) :
    ∃ q : Path c d, (q.map j.hom.continuous).Homotopic p :=
  simplexAttachment_path_homotopic_from_old X n sq hn p

variable (S : Subgroupoid (FundamentalGroupoid D))
  (hold : ∀ {x y : C} (p : Path x y),
    (⟦p.map j.hom.continuous⟧ : FundamentalGroupoid.mk (j x) ⟶
      FundamentalGroupoid.mk (j y)) ∈ S.arrows _ _)
  (hcell : ∀ (a : X) {x y : Convexity.StdSimplex ℝ (Fin (n + 1))} (p : Path x y),
    (⟦p.map (simplexAttachmentCellMap X n (g := g) a).continuous⟧ :
      FundamentalGroupoid.mk (g (a, x)) ⟶ FundamentalGroupoid.mk (g (a, y))) ∈ S.arrows _ _)

example : S = ⊤ := simplexAttachment_subgroupoid_eq_top X n sq S hold hcell

example {x y : D} (p : Path x y) :
    (⟦p⟧ : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) ∈ S.arrows _ _ := by
  rw [simplexAttachment_subgroupoid_eq_top X n sq S hold hcell]
  trivial

end TopCat
