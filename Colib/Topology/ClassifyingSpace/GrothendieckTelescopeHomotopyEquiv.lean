/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.GrothendieckTelescope
public import Colib.Topology.FilteredRealization.HomotopyEquivalence
public import Colib.Topology.Homotopy.Equiv.HomotopySquare

/-!
# Original telescope stage inclusions are genuine homotopy equivalences

Finite prefixes retract onto their last original fibers. The original prefix
transitions inherit homotopy inverses from the diagram transitions through the
actual cocartesian square. The verified filtered nerve colimit and compact HELP
then supply genuine global inverses, without a Whitehead upgrade or coherent
choices of the given transition inverses.
-/
/-!
Implementation provenance: adapted from
`Quillen/Topology/ClassifyingSpace/GrothendieckTelescopeHomotopyEquiv.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original functors,
comparison maps, homotopies, hypotheses and universes are retained.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace CategoryTheory.Grothendieck.Telescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (F : ℕ ⥤ Cat.{u, u})
  (e : ∀ {n m : ℕ} (_ : n ⟶ m),
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (F.obj n)) (ClassifyingSpace (F.obj m)))
  (he : ∀ {n m : ℕ} (f : n ⟶ m),
    (e f).toFun = (classifyingSpaceMap (F.map f).toFunctor).hom)

/-- Each original finite-prefix transition is a genuine homotopy equivalence. -/
def prefixTransitionHomotopyEquiv {n m : ℕ} (h : n ≤ m) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CategoryTheory.Grothendieck.FiniteTelescope.Model F n))
      (ClassifyingSpace (CategoryTheory.Grothendieck.FiniteTelescope.Model F m)) :=
  ContinuousMap.HomotopyEquiv.ofHomotopySquare
    (CategoryTheory.Grothendieck.FiniteTelescope.classifyingHomotopyEquiv F n).symm
    (CategoryTheory.Grothendieck.FiniteTelescope.classifyingHomotopyEquiv F m).symm
    (e (homOfLE h)) (classifyingSpaceMap (prefixTransition F h)).hom
    (by
      change ((classifyingSpaceMap (prefixTransition F h)).hom.comp
        (classifyingSpaceMap
          (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n (Fin.last n))).hom).Homotopic
          ((classifyingSpaceMap
            (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F m (Fin.last m))).hom.comp
              (e (homOfLE h)).toFun)
      rw [he]
      exact ⟨by simpa only [classifyingSpaceMap_comp, TopCat.hom_comp] using
        classifyingSpaceNaturalTransformationHomotopy (finiteStageTransitionNatTrans F h)⟩)

/-- A finite-prefix inclusion is the original forward map of a genuine homotopy equivalence. -/
def prefixInclusionHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace (CategoryTheory.Grothendieck.FiniteTelescope.Model F n))
      (ClassifyingSpace (Model F)) :=
  Topology.FilteredRealization.stageHomotopyEquiv
    (prefixDiagram F ⋙ nerveFunctor) (nerveFunctor.mapCocone (prefixCocone F))
    (nerveCoconeIsColimit F)
    (fun {_j _k} f ↦ prefixTransitionHomotopyEquiv F e he (leOfHom (AsSmall.down.map f)))
    (fun _ ↦ rfl) (AsSmall.up.obj n)

/-- The original fiber inclusion, not merely a weak replacement, has a homotopy inverse. -/
def fiberInclusionHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (F.obj n)) (ClassifyingSpace (Model F)) :=
  (CategoryTheory.Grothendieck.FiniteTelescope.classifyingHomotopyEquiv F n).symm.trans
    (prefixInclusionHomotopyEquiv F e he n)

/-- The global equivalence retains exactly the original stage inclusion. -/
@[simp]
theorem fiberInclusionHomotopyEquiv_toFun (n : ℕ) :
    (fiberInclusionHomotopyEquiv F e he n).toFun =
      (classifyingSpaceMap (Grothendieck.ι F n)).hom := by
  change (classifyingSpaceMap (prefixInclusion F n)).hom.comp
    (classifyingSpaceMap
      (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n (Fin.last n))).hom = _
  rw [← TopCat.hom_comp, ← classifyingSpaceMap_comp, fiber_prefix_inclusion]
  rfl

end CategoryTheory.Grothendieck.Telescope
