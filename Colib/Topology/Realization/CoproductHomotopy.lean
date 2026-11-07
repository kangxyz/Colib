/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Realization.Coproduct
public import Colib.Topology.Homotopy.Equiv.Sigma

/-!
# Realization of arbitrary simplicial coproducts
-/
@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology unitInterval

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SSet
variable {ι : Type u}
/-- Maps of the summands induce the canonical map on their disjoint union. -/
def simplicialSigmaMap {X Y : ι → SSet.{u}} (f : ∀ i, X i ⟶ Y i) :
    SSet.simplicialSigma X ⟶ SSet.simplicialSigma Y where
  app n := ↾fun x ↦ ⟨x.1, (f x.1).app n x.2⟩
  naturality n m α := by
    ext ⟨i, x⟩ : 3
    exact congrArg (Sigma.mk i) (ConcreteCategory.congr_hom ((f i).naturality α) x)

@[reassoc (attr := simp)]
theorem simplicialSigmaι_map {X Y : ι → SSet.{u}} (f : ∀ i, X i ⟶ Y i) (i : ι) :
    SSet.simplicialSigmaι X i ≫ SSet.simplicialSigmaMap f = f i ≫
      SSet.simplicialSigmaι Y i := rfl

@[simp]
theorem realizationSigmaIso_ι_apply (X : ι → SSet.{u}) (i : ι) (x : |X i|) :
    (SSet.realizationSigmaIso X).hom (SSet.toTop.map
      (SSet.simplicialSigmaι X i) x) = ⟨i, x⟩ :=
  ConcreteCategory.congr_hom (SSet.realizationSigmaIso_ι X i) x

@[simp]
theorem realizationSigmaIso_inv_apply (X : ι → SSet.{u}) (i : ι) (x : |X i|) :
    (SSet.realizationSigmaIso X).inv ⟨i, x⟩ = SSet.toTop.map
      (SSet.simplicialSigmaι X i) x := by
  rw [← SSet.realizationSigmaIso_ι_apply X i x]
  exact ConcreteCategory.congr_hom (SSet.realizationSigmaIso X).hom_inv_id _

/-- The disjoint-union homeomorphism intertwines the canonical realized map
with the actual disjoint union of the realized component maps. -/
theorem realizationSigmaIso_naturality {X Y : ι → SSet.{u}} (f : ∀ i, X i ⟶ Y i) :
    SSet.toTop.map (SSet.simplicialSigmaMap f) ≫
      (SSet.realizationSigmaIso Y).hom =
      (SSet.realizationSigmaIso X).hom ≫
        TopCat.ofHom (ContinuousMap.sigmaContinuousMap fun i ↦ (SSet.toTop.map (f i)).hom) := by
  apply (SSet.realizedSigmaIsColimit X).hom_ext
  intro ⟨i⟩
  dsimp
  rw [← Category.assoc, ← Functor.map_comp, SSet.simplicialSigmaι_map,
    Functor.map_comp,
    Category.assoc, SSet.realizationSigmaIso_ι, ← Category.assoc,
      SSet.realizationSigmaIso_ι]
  rfl

/-- A family of genuine homotopy equivalences of realizations induces a genuine
homotopy equivalence on the realized simplicial coproduct. -/
def realizationSigmaHomotopyEquiv {X Y : ι → SSet.{u}}
    (e : ∀ i, ContinuousMap.HomotopyEquiv |X i| |Y i|) :
    ContinuousMap.HomotopyEquiv |SSet.simplicialSigma X|
      |SSet.simplicialSigma Y| :=
  ((TopCat.homeoOfIso (SSet.realizationSigmaIso X)).toHomotopyEquiv.trans
    (ContinuousMap.sigmaHomotopyEquiv e)).trans
      (TopCat.homeoOfIso (SSet.realizationSigmaIso Y).symm).toHomotopyEquiv

/-- If the fiber equivalences have the specified canonical forward maps, so
does the resulting equivalence on the realized coproduct. -/
theorem realizationSigmaHomotopyEquiv_toFun {X Y : ι → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i)
    (e : ∀ i, ContinuousMap.HomotopyEquiv |X i| |Y i|)
    (he : ∀ i, (e i).toFun = (SSet.toTop.map (f i)).hom) :
    (SSet.realizationSigmaHomotopyEquiv e).toFun =
      (SSet.toTop.map (SSet.simplicialSigmaMap f)).hom := by
  apply ContinuousMap.ext
  intro x
  have h := ConcreteCategory.congr_hom (SSet.realizationSigmaIso_naturality f) x
  change (SSet.realizationSigmaIso Y).inv
      ⟨((SSet.realizationSigmaIso X).hom x).1,
        (e ((SSet.realizationSigmaIso X).hom x).1).toFun
          ((SSet.realizationSigmaIso X).hom x).2⟩ = _
  rw [he]
  change (SSet.realizationSigmaIso Y).inv
      ((TopCat.ofHom (ContinuousMap.sigmaContinuousMap fun i ↦ (SSet.toTop.map (f i)).hom))
        ((SSet.realizationSigmaIso X).hom x)) = _
  change (SSet.realizationSigmaIso Y).hom
      (SSet.toTop.map (SSet.simplicialSigmaMap f) x) =
    (TopCat.ofHom (ContinuousMap.sigmaContinuousMap fun i ↦ (SSet.toTop.map (f i)).hom))
      ((SSet.realizationSigmaIso X).hom x) at h
  rw [← h]
  exact ConcreteCategory.congr_hom (SSet.realizationSigmaIso Y).hom_inv_id _

end SSet
