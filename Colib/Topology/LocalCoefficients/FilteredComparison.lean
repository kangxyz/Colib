/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.FilteredTriangleHomology

public import Colib.Topology.LocalCoefficients.SquareHomology
public import Mathlib.Algebra.Homology.QuasiIso

/-!
Adapted from `Quillen/Topology/LocalCoefficients/FilteredComparison.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original maps.

# Original local-coefficient comparisons through filtered realization colimits

The stage homology maps retain their canonical coefficient-square conversions.
Their naturality and the actual filtered homology colimit identify the induced
colimit map with the original total spatial map. Stagewise quasi-isomorphisms
therefore imply a quasi-isomorphism of that original map, without an additional
comparison assumption. The sequential version explicitly lifts the natural
number index to the coefficient universe and preserves the original cocone.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits HomologicalComplex
open scoped Simplicial
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {J : Type u} [SmallCategory J]
  (F G : J ⥤ SSet.{u}) (c : Cocone F) (d : Cocone G)
  (η : F ⟶ G) (f : c.pt ⟶ d.pt)
  (w : ∀ j, c.ι.app j ≫ f = η.app j ≫ d.ι.app j)

include w in
/-- Realization retains the prescribed original colimit-leg square. -/
lemma filteredComparison_square (j : J) :
    (SSet.toTop.map f).hom.comp (SSet.toTop.map (c.ι.app j)).hom =
      (SSet.toTop.map (d.ι.app j)).hom.comp (SSet.toTop.map (η.app j)).hom := by
  simpa only [Functor.map_comp, TopCat.hom_comp] using
    congrArg (fun g => (SSet.toTop.map g).hom) (w j)

/-- The original stage comparison is natural after realization. -/
lemma filteredComparison_naturality {j k : J} (a : j ⟶ k) :
    (SSet.toTop.map (G.map a)).hom.comp (SSet.toTop.map (η.app j)).hom =
      (SSet.toTop.map (η.app k)).hom.comp (SSet.toTop.map (F.map a)).hom := by
  simpa only [Functor.map_comp, TopCat.hom_comp] using
    congrArg (fun g => (SSet.toTop.map g).hom) (η.naturality a).symm

/-- The genuine stage homology transformation with canonical coefficient conversions. -/
def filteredComparisonHomology (A : System.{u, u} |d.pt|) (n : ℕ) :
    filteredHomologyDiagram F c (pullback (SSet.toTop.map f).hom A) n ⟶
      filteredHomologyDiagram G d A n where
  app j := squareHomologyMap (SSet.toTop.map (η.app j)).hom
    (SSet.toTop.map (c.ι.app j)).hom (SSet.toTop.map (d.ι.app j)).hom
    (SSet.toTop.map f).hom (filteredComparison_square F G c d η f w j) A n
  naturality j k a := by
    rw [filteredHomologyDiagram_map_triangle, filteredHomologyDiagram_map_triangle]
    exact (squareHomologyMap_naturality
      (SSet.toTop.map (F.map a)).hom (SSet.toTop.map (G.map a)).hom
      (SSet.toTop.map (η.app j)).hom (SSet.toTop.map (η.app k)).hom
      (SSet.toTop.map (c.ι.app j)).hom (SSet.toTop.map (c.ι.app k)).hom
      (SSet.toTop.map (d.ι.app j)).hom (SSet.toTop.map (d.ι.app k)).hom
      (SSet.toTop.map f).hom (stage_triangle F c j k a) (stage_triangle G d j k a)
      (filteredComparison_square F G c d η f w j)
      (filteredComparison_square F G c d η f w k)
      (filteredComparison_naturality F G η a) A n).symm

/-- The induced homology square commutes along each original colimit leg. -/
lemma filteredComparisonHomology_leg (A : System.{u, u} |d.pt|) (n : ℕ) (j : J) :
    (filteredComparisonHomology F G c d η f w A n).app j ≫
      pushforwardHomologyMap (SSet.toTop.map (d.ι.app j)).hom A n =
    pushforwardHomologyMap (SSet.toTop.map (c.ι.app j)).hom
        (pullback (SSet.toTop.map f).hom A) n ≫
      pushforwardHomologyMap (SSet.toTop.map f).hom A n :=
  squareHomologyMap_to_target _ _ _ _ _ _ _

variable [IsFiltered J] (hc : IsColimit c) (hd : IsColimit d)

/-- The original total homology map is exactly the induced map on actual filtered colimits. -/
lemma filteredComparisonHomology_colimit (A : System.{u, u} |d.pt|) (n : ℕ) :
    pushforwardHomologyMap (SSet.toTop.map f).hom A n =
      (filteredHomologyColimitIso F c hc (pullback (SSet.toTop.map f).hom A) n).inv ≫
        colim.map (filteredComparisonHomology F G c d η f w A n) ≫
          (filteredHomologyColimitIso G d hd A n).hom := by
  apply (cancel_epi
    (filteredHomologyColimitIso F c hc (pullback (SSet.toTop.map f).hom A) n).hom).mp
  rw [Iso.hom_inv_id_assoc]
  apply colimit.hom_ext
  intro j
  rw [filteredHomologyColimitIso_ι_hom_assoc, colimit.ι_map_assoc,
    filteredHomologyColimitIso_ι_hom]
  exact (filteredComparisonHomology_leg F G c d η f w A n j).symm

include w hc hd in
/-- Stagewise isomorphisms imply an isomorphism of the original total homology map. -/
lemma filteredComparison_pushforwardHomologyMap_isIso (A : System.{u, u} |d.pt|) (n : ℕ)
    (hη : ∀ j, IsIso (pushforwardHomologyMap (SSet.toTop.map (η.app j)).hom
      (pullback (SSet.toTop.map (d.ι.app j)).hom A) n)) :
    IsIso (pushforwardHomologyMap (SSet.toTop.map f).hom A n) := by
  let α := filteredComparisonHomology F G c d η f w A n
  let : ∀ j, IsIso (α.app j) := fun j => by
    let := hη j
    let := triangleHomologyMap_isIso (SSet.toTop.map (η.app j)).hom
      ((SSet.toTop.map f).hom.comp (SSet.toTop.map (c.ι.app j)).hom)
      (SSet.toTop.map (d.ι.app j)).hom (filteredComparison_square F G c d η f w j) A n
    change IsIso ((coefficientHomologyIso
      (pullbackCompositionIso (SSet.toTop.map (c.ι.app j)).hom
        (SSet.toTop.map f).hom A).symm n).hom ≫ _)
    infer_instance
  let : IsIso α := NatIso.isIso_of_isIso_app α
  rw [filteredComparisonHomology_colimit F G c d η f w hc hd A n]
  change IsIso ((filteredHomologyColimitIso F c hc
    (pullback (SSet.toTop.map f).hom A) n).inv ≫ colim.map α ≫ _)
  infer_instance

include w hc hd in
/-- Stagewise quasi-isomorphisms imply a quasi-isomorphism of the original total chain map. -/
lemma filteredComparison_pushforwardChainMap_quasiIso (A : System.{u, u} |d.pt|)
    (hη : ∀ j, QuasiIso (pushforwardChainMap (SSet.toTop.map (η.app j)).hom
      (pullback (SSet.toTop.map (d.ι.app j)).hom A))) :
    QuasiIso (pushforwardChainMap (SSet.toTop.map f).hom A) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  apply filteredComparison_pushforwardHomologyMap_isIso F G c d η f w hc hd A n
  intro j
  let := hη j
  change IsIso (HomologicalComplex.homologyMap _ n)
  infer_instance

end FundamentalGroupoid.LocalCoefficients

namespace FundamentalGroupoid.LocalCoefficients
variable (F G : ℕ ⥤ SSet.{u}) (c : Cocone F) (d : Cocone G)
  (η : F ⟶ G) (f : c.pt ⟶ d.pt)
  (w : ∀ n, c.ι.app n ≫ f = η.app n ≫ d.ι.app n)
  (hc : IsColimit c) (hd : IsColimit d)

include w hc hd in
/-- The same original-map criterion for a natural-number sequence in any simplicial universe. -/
lemma sequentialComparison_pushforwardChainMap_quasiIso (A : System.{u, u} |d.pt|)
    (hη : ∀ n, QuasiIso (pushforwardChainMap (SSet.toTop.map (η.app n)).hom
      (pullback (SSet.toTop.map (d.ι.app n)).hom A))) :
    QuasiIso (pushforwardChainMap (SSet.toTop.map f).hom A) := by
  let e : AsSmall.{u} ℕ ≌ ℕ := (AsSmall.equiv (C := ℕ)).symm
  exact filteredComparison_pushforwardChainMap_quasiIso
    (e.functor ⋙ F) (e.functor ⋙ G) (c.whisker e.functor) (d.whisker e.functor)
    (Functor.whiskerLeft e.functor η) f (fun j => w (e.functor.obj j))
    ((Functor.Final.isColimitWhiskerEquiv e.functor c).symm hc)
    ((Functor.Final.isColimitWhiskerEquiv e.functor d).symm hd)
    A (fun j => hη (e.functor.obj j))

end FundamentalGroupoid.LocalCoefficients
