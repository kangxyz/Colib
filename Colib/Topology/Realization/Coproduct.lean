/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Realization of explicit simplicial coproducts

The degreewise disjoint union is a coproduct, and its geometric realization is
canonically the topological disjoint union. The summand equation identifies the
actual map, rather than only exhibiting an unspecified isomorphic space.

## Implementation provenance

Selected from `Quillen/Topology/Realization/Coproduct.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. These six declarations retain the
source constructions, proofs and universe. Homotopy assembly is not imported.
-/
@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet

variable {ι : Type u}

/-- The degreewise disjoint union of a family of simplicial sets. -/
def simplicialSigma (X : ι → SSet.{u}) : SSet.{u} where
  obj n := Σ i, (X i).obj n
  map f := ↾fun x ↦ ⟨x.1, (X x.1).map f x.2⟩
  map_id n := by ext x : 3; dsimp; simp
  map_comp f g := by ext x : 3; dsimp; simp

/-- The inclusion of one summand. -/
def simplicialSigmaι (X : ι → SSet.{u}) (i : ι) : X i ⟶
  SSet.simplicialSigma X where
  app _n := ↾fun x ↦ ⟨i, x⟩
  naturality _ _ _ := rfl


/-- The explicit disjoint union is the categorical coproduct. -/
def simplicialSigmaIsColimit (X : ι → SSet.{u}) :
    IsColimit (Cofan.mk (SSet.simplicialSigma X)
      (SSet.simplicialSigmaι X)) :=
  Cofan.IsColimit.mk _
    (fun s ↦ {
      app := fun n ↦ ↾fun x ↦ (s.inj x.1).app n x.2
      naturality := by
        intro n m α
        ext ⟨i, x⟩ : 3
        exact ConcreteCategory.congr_hom ((s.inj i).naturality α) x })
    (by intro s i; rfl)
    (by
      intro s m h
      ext n ⟨i, x⟩ : 4
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (h i) n) x)

/-- Realization preserves the explicit coproduct cocone. -/
def realizedSigmaIsColimit (X : ι → SSet.{u}) :
    IsColimit (Cofan.mk (SSet.toTop.obj (SSet.simplicialSigma X))
      (fun i ↦ SSet.toTop.map (SSet.simplicialSigmaι X i))) :=
  isColimitCofanMkObjOfIsColimit SSet.toTop X (SSet.simplicialSigmaι X)
    (SSet.simplicialSigmaIsColimit X)

/-- Realization of a simplicial coproduct is the actual topological disjoint union. -/
def realizationSigmaIso (X : ι → SSet.{u}) :
    SSet.toTop.obj (SSet.simplicialSigma X) ≅ TopCat.of (Σ i, |X i|) :=
  (SSet.realizedSigmaIsColimit X).coconePointUniqueUpToIso
    (TopCat.sigmaCofanIsColimit fun i ↦ SSet.toTop.obj (X i))

@[reassoc (attr := simp)]
theorem realizationSigmaIso_ι (X : ι → SSet.{u}) (i : ι) :
    SSet.toTop.map (SSet.simplicialSigmaι X i) ≫
      (SSet.realizationSigmaIso X).hom =
      TopCat.sigmaι (fun i ↦ SSet.toTop.obj (X i)) i := by
  exact (SSet.realizedSigmaIsColimit X).comp_coconePointUniqueUpToIso_hom _ ⟨i⟩


end SSet

attribute [colib_tag "COL-0090",
  colib_ref "WeibelKBook" "IV, Characterization 3.1(5), page 24"
    "background"
    "Realization of coproducts; the cited categorical statement is background"]
  SSet.simplicialSigmaIsColimit
  SSet.realizedSigmaIsColimit
  SSet.realizationSigmaIso
  SSet.realizationSigmaIso_ι

attribute [stacks 0038 "(1), left-adjoint preservation of the explicit simplicial coproduct"]
  SSet.realizedSigmaIsColimit
  SSet.realizationSigmaIso
