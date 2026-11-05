/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Waldhausen.Basic
public import Colib.CategoryTheory.Waldhausen.SMap
public import Colib.Topology.Homotopy.HomotopyGroup.Map

/-!
# Actual realization maps and image-zero homotopy-group maps

Exact functors act by the existing S-map followed by Mathlib realization. The
basepoint theorem identifies the image-zero vertex, not an arbitrary independently
chosen target zero. A strict equality permits the explicit final basepoint change.
No canonical rebasing, KMap functoriality, or strict S-model comparison is asserted.

## Implementation provenance

Extracted from `Quillen/Waldhausen/Functor.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Source maps and the same-universe
restriction are retained; `Quillen.piMap` is the existing `HomotopyGroup.piMap`.
The model is the unnormalized diagonal IsZero construction.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {cof weq : MorphismProperty C} {cof' weq' : MorphismProperty D}
  {F : C ⥤ D} (hF : IsExact cof weq cof' weq' F)

/-- The map of actual geometric realizations. -/
def deloopingMap : delooping cof weq ⟶ delooping cof' weq' :=
  SSet.toTop.map (sSetMap hF)

variable [cof.ContainsIdentities] [weq.ContainsIdentities]
  [cof'.ContainsIdentities] [weq'.ContainsIdentities]

/-- A zero simplex is sent to the zero simplex of its image object. -/
@[simp]
theorem sSetMap_zeroSimplex (Z : C) (hZ : IsZero Z) (n : SimplexCategoryᵒᵖ) :
    (sSetMap hF).app n (zeroSimplex cof weq Z hZ n) =
      zeroSimplex cof' weq' (F.obj Z) (hF.zero hZ) n := by
  apply Subtype.ext
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
  intro x y f
  simp [sSetMap, zeroSimplex]

/-- Realization maps preserve the image basepoint. -/
@[simp]
theorem deloopingMap_basepoint (Z : C) (hZ : IsZero Z) :
    deloopingMap hF (basepoint cof weq Z hZ) =
      basepoint cof' weq' (F.obj Z) (hF.zero hZ) := by
  have h := SSet.yonedaEquiv_symm_comp (zeroSimplex cof weq Z hZ (op ⦋0⦌)) (sSetMap hF)
  have h' := congrArg (fun f : (Δ[0] : SSet.{max u v}) ⟶ sSet cof' weq' ↦
    SSet.toTop.map f default) h
  simpa only [Functor.map_comp, TopCat.comp_app, sSetMap_zeroSimplex,
    deloopingMap, basepoint, delooping] using h'

/-- The induced homomorphism on genuine homotopy groups, based at the image
zero object. No weak-equivalence/comparison theorem is assumed. -/
def groupsMap (Z : C) (hZ : IsZero Z) (n : ℕ) :
    groups cof weq Z hZ n →* groups cof' weq' (F.obj Z) (hF.zero hZ) n :=
  HomotopyGroup.piMap n (deloopingMap hF).hom (deloopingMap_basepoint hF Z hZ)

/-- A strict equality of chosen zero objects identifies the target basepoint. -/
def groupsMapOfZeroEq (Z : C) (hZ : IsZero Z) (Z' : D) (hZ' : IsZero Z')
    (h : F.obj Z = Z') (n : ℕ) :
    groups cof weq Z hZ n →* groups cof' weq' Z' hZ' n := by
  subst Z'
  exact groupsMap hF Z hZ n

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0155",
  colib_ref "Waldhausen1985" "Section 1.3, pp. 328-330" "background"
    "Background for the stated unnormalized IsZero model; not a strict-model identification"]
  CategoryTheory.Waldhausen.deloopingMap
  CategoryTheory.Waldhausen.deloopingMap_basepoint
  CategoryTheory.Waldhausen.groupsMap
  CategoryTheory.Waldhausen.groupsMapOfZeroEq
