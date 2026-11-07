/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakNaturalTransformation
public import Colib.KTheory.Waldhausen.Functoriality
public import Colib.KTheory.Waldhausen.ZeroFunctor
public import Colib.Topology.Realization.Connectivity

/-! # Genuine path-connectedness of every Waldhausen S-realization

Every degree-zero S-grid is a constant diagram at an actual zero object.
Its unique zero-object isomorphism to the chosen zero supplies a real
nerve-direction homotopy. Joining arbitrary realization points to vertices
then proves path-connectedness of the unchanged actual delooping.


Implementation provenance:
`Quillen/Waldhausen/SConstruction/Connected.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section


noncomputable section
open Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u v

namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- The degree-zero grid is genuinely a one-object thin category. -/
instance grid_zero_subsingleton : Subsingleton (Grid ⦋0⦌) := by
  change Subsingleton (Fin 1 × {p : Fin 1 × Fin 1 // p.1 ≤ p.2})
  infer_instance

private theorem functor_eq_const_of_subsingleton
    {J : Type*} [Category* J] [Subsingleton J] [Quiver.IsThin J]
    (F : J ⥤ C) (j : J) : F = (Functor.const J).obj (F.obj j) := by
  refine CategoryTheory.Functor.ext (fun i ↦ congrArg F.obj (Subsingleton.elim i j)) ?_
  intro a b f
  have ha : a = j := Subsingleton.elim _ _
  have hb : b = j := Subsingleton.elim _ _
  subst a
  subst b
  have hf : f = 𝟙 j := Subsingleton.elim _ _
  subst f
  simp

/-- Every actual zero-dimensional S-grid is the corresponding constant zero simplex. -/
theorem zeroDimensionalSimplex_eq_zero (x : (sSet W.cof W.weq) _⦋0⦌) :
    x = zeroSimplex W.cof W.weq (x.val.obj (grid 0 0 0 le_rfl))
      (x.property.zero 0 0) (op ⦋0⦌) := by
  apply Subtype.ext
  exact functor_eq_const_of_subsingleton x.val _

/-- Constant functors at arbitrary actual zero objects are genuinely exact. -/
theorem constZero_isExact (Z : C) (hZ : IsZero Z) :
    IsExact W.cof W.weq W.cof W.weq ((Functor.const C).obj Z) where
  zero _ := hZ
  cofibration _ _ := W.cof.id_mem Z
  weak _ _ := W.weq.id_mem Z
  pushout _ _ := IsPushout.id_horiz (𝟙 Z)

/-- An actual zero object's vertex is joined to the originally chosen zero vertex. -/
theorem zero_vertex_joined_basepoint (Z : C) (hZ : IsZero Z) :
    Joined (basepoint W.cof W.weq Z hZ) W.kBasepoint := by
  let η : (Functor.const C).obj Z ⟶ zeroFunctor W := {
    app _ := hZ.to_ W.zero
    naturality _ _ _ := by simp [zeroFunctor] }
  have hη (X : C) : W.weq (η.app X) := W.weq_iso _ (hZ.isIso W.isZero _)
  let H := weakNaturalTransformationRealizationHomotopy W W
    (constZero_isExact W Z hZ) (zeroFunctor_isExact W W) η hη
  have hj : Joined (deloopingMap (constZero_isExact W Z hZ) W.kBasepoint)
      (deloopingMap (zeroFunctor_isExact W W) W.kBasepoint) := ⟨H.evalAt W.kBasepoint⟩
  simpa [zeroFunctor] using hj

/-- Every actual S-vertex is joined to the chosen zero point. -/
theorem sSet_vertex_joined_basepoint (x : (sSet W.cof W.weq) _⦋0⦌) :
    Joined (SSet.realizationPoint x) W.kBasepoint := by
  rw [zeroDimensionalSimplex_eq_zero W x]
  exact zero_vertex_joined_basepoint W _ _

/-- Every genuine Waldhausen S-realization is path-connected. -/
instance delooping_pathConnected : PathConnectedSpace W.Delooping where
  nonempty := ⟨W.kBasepoint⟩
  joined x y := by
    obtain ⟨a, ha⟩ := SSet.realization_joined_vertex x
    obtain ⟨b, hb⟩ := SSet.realization_joined_vertex y
    exact ha.symm.trans ((sSet_vertex_joined_basepoint W a).trans
      ((sSet_vertex_joined_basepoint W b).symm.trans hb))

/-- A genuine path from the chosen zero to any point of the original S-realization. -/
def kBasepointPath (x : W.Delooping) : Path W.kBasepoint x :=
  (PathConnectedSpace.joined W.kBasepoint x).somePath

end CategoryTheory.Waldhausen
