/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import StacksFrontier.Homology.HomologyColimit
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Exact filtered colimits of modules and their homology

The actual forgetful functor to abelian groups transfers AB5 to modules in an
arbitrary universe, independently of the ring universe. Exactness applies to
any filtered indexing category whose object and morphism universes are bounded
by the module universe. The chain-complex comparison is natural and uses the
original colimit homology map, without assuming its invertibility.

These are named theorems rather than new global instances.

Adapted from Quillen.Aglib.Algebra.Category.ModuleCat.FilteredColimits at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The exact-colimit preservation proof
is reused from the pinned Stacks API rather than duplicated.
-/

@[expose] public section

open CategoryTheory Limits
noncomputable section
universe u v w w' t
namespace ModuleCat

/-- Module categories satisfy AB5 even when the ring and module universes differ.
This is a named theorem to avoid adding a competing global instance. -/
theorem ab5 (R : Type v) [Ring R] : AB5 (ModuleCat.{u} R) where
  ofShape J _ _ :=
    HasExactColimitsOfShape.domain_of_functor J
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})

variable (R : Type v) [Ring R]
variable (J : Type w) [Category.{w'} J] [IsFiltered J]
  [UnivLE.{w, u}] [UnivLE.{w', u}]

/-- Filtered colimits are exact for every diagram size bounded by the module universe. -/
theorem hasExactFilteredColimits : HasExactColimitsOfShape J (ModuleCat.{u} R) := by
  let := ab5.{u} R
  let := AB5OfSize_of_univLE.{w', w, u, u} (ModuleCat.{u} R)
  infer_instance

/-- The actual filtered-colimit functor of modules preserves homology. -/
theorem colim_preservesHomology :
    (colim : (J ⥤ ModuleCat.{u} R) ⥤ ModuleCat.{u} R).PreservesHomology := by
  let := hasExactFilteredColimits.{u} R J
  infer_instance

variable {ι : Type t} (c : ComplexShape ι) (n : ι)

/-- Homology of complexes of modules preserves filtered colimits of actual diagrams. -/
theorem homologyFunctor_preservesFilteredColimits :
    PreservesColimitsOfShape J (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) c n) := by
  let := hasExactFilteredColimits.{u} R J
  exact Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor c n

/-- The canonical filtered-colimit comparison, natural in diagrams of complexes. -/
def filteredColimitHomologyNatIso :
    (colim : (J ⥤ HomologicalComplex (ModuleCat.{u} R) c) ⥤ _) ⋙
        HomologicalComplex.homologyFunctor _ c n ≅
      (Functor.whiskeringRight J _ _).obj (HomologicalComplex.homologyFunctor _ c n) ⋙
        colim := by
  letI := hasExactFilteredColimits.{u} R J
  letI := Stacks.HomologyColimit.preservesColimitsOfShape_homologyFunctor
    (A := ModuleCat.{u} R) (J := J) c n
  exact preservesColimitNatIso (HomologicalComplex.homologyFunctor _ c n)

/-- Homology of the actual filtered colimit is the colimit of stage homology. -/
def filteredColimitHomologyIso (F : J ⥤ HomologicalComplex (ModuleCat.{u} R) c) :
    (colimit F).homology n ≅
      colimit (F ⋙ HomologicalComplex.homologyFunctor _ c n) :=
  (filteredColimitHomologyNatIso R J c n).app F

/-- This comparison is the original canonical map out of colimit of homology. -/
@[simp]
theorem filteredColimitHomologyIso_inv (F : J ⥤ HomologicalComplex (ModuleCat.{u} R) c) :
    (filteredColimitHomologyIso R J c n F).inv =
      colimit.post F (HomologicalComplex.homologyFunctor _ c n) := rfl

/-- Each stage enters the comparison by its original induced homology map. -/
@[reassoc]
theorem filteredColimitHomologyIso_ι_inv
    (F : J ⥤ HomologicalComplex (ModuleCat.{u} R) c) (j : J) :
    colimit.ι (F ⋙ HomologicalComplex.homologyFunctor _ c n) j ≫
      (filteredColimitHomologyIso R J c n F).inv =
        HomologicalComplex.homologyMap (colimit.ι F j) n := by
  let := homologyFunctor_preservesFilteredColimits.{u} R J c n
  exact ι_preservesColimitIso_inv _ _ j

end ModuleCat

attribute [colib_tag "COL-0147",
  stacks 00DB "Generalized to possibly noncommutative rings and size-bounded filtered categories"]
  ModuleCat.ab5
  ModuleCat.hasExactFilteredColimits
  ModuleCat.colim_preservesHomology
  ModuleCat.homologyFunctor_preservesFilteredColimits
  ModuleCat.filteredColimitHomologyNatIso
  ModuleCat.filteredColimitHomologyIso
  ModuleCat.filteredColimitHomologyIso_inv
  ModuleCat.filteredColimitHomologyIso_ι_inv

attribute [stacks 04B0 "Exact filtered colimits of abelian groups, transferred to modules",
  stacks 079B "Terminology for the AB5 condition"]
  ModuleCat.ab5
