/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.GrothendieckComparison.ObjectLoops
public import Colib.Topology.ClassifyingSpace.ArrowPaths

/-! # Coherent original zero-object tracks in the actual S-realization

The nerve of the full category of actual zero objects maps into the unchanged
diagonal S-construction by constant interval rows. Its original arrow paths
supply coherent vertex anchors, retaining the genuine chosen zero object.

Implementation provenance: `Quillen/Waldhausen/GrothendieckComparison/ZeroTracks.lean`
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
universe u v
namespace CategoryTheory.Waldhausen.Structure
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The actual full category of zero objects in the original category. -/
abbrev ZeroObjects := ObjectProperty.FullSubcategory (IsZero : ObjectProperty C)

/-- Forget the interval coordinates of an original diagonal grid. -/
def nerveProjection (n : SimplexCategory) : Grid n ⥤ Fin (n.len + 1) :=
  (show Monotone (fun p : Grid n ↦ p.1) from fun _ _ h ↦ h.1).functor

/-- The original chain of actual zero objects is constant in the interval direction. -/
def zeroChainSimplex {n : SimplexCategory} (F : ComposableArrows (ZeroObjects (C := C)) n.len) :
    (sSet W.cof W.weq).obj (op n) :=
  ⟨nerveProjection n ⋙ F ⋙ ObjectProperty.ι (IsZero : ObjectProperty C), {
    zero t _ := (F.obj t).property
    cofibration t _ _ _ _ _ := by
      change W.cof ((F.map (𝟙 t)).hom)
      simpa only [F.map_id, ObjectProperty.FullSubcategory.id_hom] using W.cof.id_mem (F.obj t).obj
    quotient t _ _ _ _ _ := by
      change IsPushout ((F.map (𝟙 t)).hom) ((F.map (𝟙 t)).hom)
        ((F.map (𝟙 t)).hom) ((F.map (𝟙 t)).hom)
      simpa only [F.map_id, ObjectProperty.FullSubcategory.id_hom] using
        IsPushout.id_horiz (𝟙 (F.obj t).obj)
    weak s t _ _ hst _ :=
      W.weq_iso _ ((F.obj s).property.isIso (F.obj t).property _) }⟩

/-- The full original nerve of actual zero objects maps to the actual S-construction. -/
def zeroNerveMap : nerve (ZeroObjects (C := C)) ⟶ sSet W.cof W.weq where
  app _ := ↾fun F ↦ W.zeroChainSimplex F
  naturality _ _ _ := by ext F; rfl

/-- Its vertex is literally the original all-zero grid at the specified zero object. -/
@[simp] theorem zeroNerveMap_vertex (Z : ZeroObjects (C := C)) :
    (W.zeroNerveMap).app (op ⦋0⦌) (nerveVertex Z) =
      zeroSimplex W.cof W.weq Z.obj Z.property (op ⦋0⦌) := by
  apply Subtype.ext
  rfl

/-- The actual original zero-to-zero edge, with its original endpoint vertices. -/
def zeroTrackEdge (Z Z' : ZeroObjects (C := C)) :
    (sSet W.cof W.weq).Edge
      (zeroSimplex W.cof W.weq Z.obj Z.property (op ⦋0⦌))
      (zeroSimplex W.cof W.weq Z'.obj Z'.property (op ⦋0⦌)) :=
  (CategoryTheory.nerve.edgeMk
    (ObjectProperty.homMk (P := (IsZero : ObjectProperty C))
      (Z.property.to_ Z'.obj))).map W.zeroNerveMap

/-- The actual zero-object vertex track, before passing to path homotopy classes. -/
def zeroTrackPath (Z Z' : ZeroObjects (C := C)) :
    Path (basepoint W.cof W.weq Z.obj Z.property)
      (basepoint W.cof W.weq Z'.obj Z'.property) :=
  realizationEdgePath (W.zeroTrackEdge Z Z')

/-- Original zero-object tracks compose by a genuine original nerve triangle. -/
theorem zeroTrackPath_comp (Z Z' Z'' : ZeroObjects (C := C)) :
    ((W.zeroTrackPath Z Z').trans (W.zeroTrackPath Z' Z'')).Homotopic
      (W.zeroTrackPath Z Z'') := by
  let f : Z ⟶ Z' := ObjectProperty.homMk (P := (IsZero : ObjectProperty C)) (Z.property.to_ Z'.obj)
  let g : Z' ⟶ Z'' :=
    ObjectProperty.homMk (P := (IsZero : ObjectProperty C)) (Z'.property.to_ Z''.obj)
  let h : Z ⟶ Z'' :=
    ObjectProperty.homMk (P := (IsZero : ObjectProperty C)) (Z.property.to_ Z''.obj)
  have he : f ≫ g = h := by
    apply ObjectProperty.hom_ext
    exact Z.property.eq_of_src _ _
  exact realizationEdgePath_comp
    (((CategoryTheory.nerve.nonempty_compStruct_iff f g h).2 he).some.map W.zeroNerveMap)

/-- Every original zero-object self-track is homotopic to the constant path. -/
theorem zeroTrackPath_self (Z : ZeroObjects (C := C)) :
    W.zeroTrackPath Z Z = Path.refl (basepoint W.cof W.weq Z.obj Z.property) := by
  have he : W.zeroTrackEdge Z Z =
      SSet.Edge.id (zeroSimplex W.cof W.weq Z.obj Z.property (op ⦋0⦌)) := by
    apply SSet.Truncated.Edge.ext
    apply Subtype.ext
    have hobj : ∀ p, (W.zeroTrackEdge Z Z).edge.val.obj p = Z.obj := by
      rintro ⟨t, p⟩
      fin_cases t <;> rfl
    refine CategoryTheory.Functor.ext hobj ?_
    intro p q f
    have hz : IsZero ((W.zeroTrackEdge Z Z).edge.val.obj p) := by
      rw [hobj p]
      exact Z.property
    exact hz.eq_of_src _ _
  exact (congrArg realizationEdgePath he).trans (realizationEdgePath_id _)

/-- The original chosen zero as an object of the actual full zero-object category. -/
def chosenZeroObject : ZeroObjects (C := C) := ⟨W.zero, W.isZero⟩

/-- The original zero-object path class in the actual fundamental groupoid. -/
def zeroTrackHom (Z Z' : ZeroObjects (C := C)) :
    FundamentalGroupoid.mk (basepoint W.cof W.weq Z.obj Z.property) ⟶
      FundamentalGroupoid.mk (basepoint W.cof W.weq Z'.obj Z'.property) :=
  ⟦W.zeroTrackPath Z Z'⟧

/-- Actual zero-object tracks have the original categorical composition law. -/
@[simp] theorem zeroTrackHom_comp (Z Z' Z'' : ZeroObjects (C := C)) :
    W.zeroTrackHom Z Z' ≫ W.zeroTrackHom Z' Z'' = W.zeroTrackHom Z Z'' :=
  Quotient.sound (W.zeroTrackPath_comp Z Z' Z'')

/-- The actual zero-object self-track is the identity. -/
@[simp] theorem zeroTrackHom_self (Z : ZeroObjects (C := C)) :
    W.zeroTrackHom Z Z = 𝟙 _ := by
  unfold zeroTrackHom
  rw [W.zeroTrackPath_self]
  rfl

/-- The coherent original vertex anchor starts at the originally chosen zero. -/
def zeroAnchorHom (Z : ZeroObjects (C := C)) :
    FundamentalGroupoid.mk W.kBasepoint ⟶
      FundamentalGroupoid.mk (basepoint W.cof W.weq Z.obj Z.property) :=
  W.zeroTrackHom W.chosenZeroObject Z

/-- Original zero tracks extend their original chosen-zero anchors. -/
@[simp] theorem zeroAnchorHom_comp (Z Z' : ZeroObjects (C := C)) :
    W.zeroAnchorHom Z ≫ W.zeroTrackHom Z Z' = W.zeroAnchorHom Z' :=
  W.zeroTrackHom_comp W.chosenZeroObject Z Z'

end CategoryTheory.Waldhausen.Structure
