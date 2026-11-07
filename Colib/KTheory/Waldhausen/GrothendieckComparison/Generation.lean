/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.EdgeNormalization
public import Colib.KTheory.Waldhausen.GrothendieckComparison.ClassicalMap
public import Colib.KTheory.Waldhausen.Connected
public import Colib.Topology.Realization.SimplicialFullness

/-! # The original object classes generate actual Waldhausen K₀

Every actual original diagonal edge reduces to its original object loop after
coherent original zero-object anchoring. The proved generic graph generation
then applies to all actual continuous path classes in the unchanged realization.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/Generation.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original
objects, maps and hypotheses are retained.
-/
@[expose] public section

noncomputable section
open Topology SSet
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial Topology
universe u
namespace CategoryTheory.Waldhausen.AlgebraicGrothendieck
variable {C : Type u} [SmallCategory C] (W : Structure C)

/-- The original classical comparison, viewed in the actual fundamental groupoid. -/
def comparisonFundamentalGroupoidFunctor :
    SingleObj (Multiplicative (Group W)) ⥤ FundamentalGroupoid W.Delooping :=
  SingleObj.functor (W.kZeroFundamentalGroupEquiv.toMonoidHom.comp (grothendieckToKZero W))

/-- The actual zero object occurring in an original S-construction vertex. -/
def vertexZero (x : (sSet W.cof W.weq) _⦋0⦌) : Structure.ZeroObjects (C := C) :=
  ⟨x.val.obj (grid 0 0 0 le_rfl), x.property.zero 0 0⟩

/-- The original zero-object point is the actual original simplicial vertex. -/
theorem vertexZero_point (x : (sSet W.cof W.weq) _⦋0⦌) :
    basepoint W.cof W.weq (vertexZero W x).obj (vertexZero W x).property =
      realizationPoint x :=
  congrArg realizationPoint (zeroDimensionalSimplex_eq_zero W x).symm

/-- The original coherent chosen-zero anchor at every actual original vertex. -/
def vertexAnchor (x : (sSet W.cof W.weq) _⦋0⦌) :
    (comparisonFundamentalGroupoidFunctor W).obj
      (SingleObj.star (Multiplicative (Group W))) ≅ FundamentalGroupoid.mk (realizationPoint x) :=
  asIso (W.zeroAnchorHom (vertexZero W x)) ≪≫
    eqToIso (congrArg FundamentalGroupoid.mk (vertexZero_point W x))

/-- The classical generator attached to the original source-row middle object. -/
def edgeGenerator {x y : (sSet W.cof W.weq) _⦋0⦌}
    (e : (sSet W.cof W.weq).Edge x y) :
    SingleObj.star (Multiplicative (Group W)) ⟶ SingleObj.star (Multiplicative (Group W)) :=
  Multiplicative.ofAdd (objectClass W (e.edge.val.obj (grid 0 0 1 (by decide))))

/-- The canonical original edge generator has exactly the required actual anchored path class. -/
theorem edgeGenerator_image {x y : (sSet W.cof W.weq) _⦋0⦌}
    (e : (sSet W.cof W.weq).Edge x y) :
    (comparisonFundamentalGroupoidFunctor W).map (edgeGenerator W e) =
      (vertexAnchor W x).hom ≫ ⟦realizationEdgePath e⟧ ≫ (vertexAnchor W y).inv := by
  rcases e with ⟨s, rfl, rfl⟩
  let e : (sSet W.cof W.weq).Edge
      ((sSet W.cof W.weq).δ 1 s) ((sSet W.cof W.weq).δ 0 s) := ⟨s, rfl, rfl⟩
  change (W.kZeroFundamentalGroupEquiv
    (grothendieckToKZero W (Multiplicative.ofAdd
      (objectClass W (s.val.obj (grid 0 0 1 (by decide))))))).toPath = _
  rw [grothendieckToKZero_objectClass, W.kZeroFundamentalGroupEquiv_objectClass]
  have hp : eqToHom (congrArg FundamentalGroupoid.mk
      (vertexZero_point W ((sSet W.cof W.weq).δ 1 s))) ≫
      (⟦realizationEdgePath e⟧ : FundamentalGroupoid.mk _ ⟶ FundamentalGroupoid.mk _) ≫
      eqToHom (congrArg FundamentalGroupoid.mk
        (vertexZero_point W ((sSet W.cof W.weq).δ 0 s)).symm) = W.gridPathHom s := by
    rw [FundamentalGroupoid.conj_eqToHom
      (vertexZero_point W ((sSet W.cof W.weq).δ 1 s))
      (vertexZero_point W ((sSet W.cof W.weq).δ 0 s))]
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    rfl
  dsimp only [vertexAnchor, Iso.trans_hom, Iso.trans_inv, asIso_hom, asIso_inv,
    eqToIso.hom, eqToIso.inv]
  simp only [Category.assoc]
  have hh := congrArg (fun q ↦ W.zeroAnchorHom (W.gridZero s 0 0) ≫ q ≫
    inv (W.zeroAnchorHom (W.gridZero s 1 1))) hp
  simp only [Category.assoc] at hh
  exact (W.gridPathHom_normalization_closed s).symm.trans hh.symm

/-- Every actual based path class is represented by an original classical class. -/
theorem grothendieckToKZero_surjective : Function.Surjective (grothendieckToKZero W) := by
  have hf := SimplicialGraph.map_surjective_of_edges (sSet W.cof W.weq)
    (comparisonFundamentalGroupoidFunctor W)
    (fun _ ↦ SingleObj.star (Multiplicative (Group W))) (vertexAnchor W)
    (edgeGenerator W) (edgeGenerator_image W)
    (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌))
    (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌))
  intro x
  obtain ⟨a, ha⟩ := hf (W.kZeroFundamentalGroupEquiv x).toPath
  exact ⟨a, W.kZeroFundamentalGroupEquiv.injective (End.ext ha)⟩

end CategoryTheory.Waldhausen.AlgebraicGrothendieck
