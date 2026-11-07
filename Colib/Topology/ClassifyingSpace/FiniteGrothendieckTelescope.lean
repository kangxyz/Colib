/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.GrothendieckTerminal
/-!
Adapted from `Quillen/Topology/ClassifyingSpace/FiniteGrothendieckTelescope.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original categorical maps.


# Finite categorical telescope models

For an original sequence of categories, restrict to its first `n + 1` stages
and take the actual Grothendieck construction. The terminal-fiber projection
realizes to a homotopy equivalence with the last stage. Every original fiber,
including the stage-zero unit, projects by its original transition functor.
This is a categorical finite model; no identification with an ordinary or fat
topological mapping telescope is asserted here.
-/

@[expose] public section

open CategoryTheory Limits
noncomputable section
universe u
namespace CategoryTheory.Grothendieck.FiniteTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- A common-universe model of the first n + 1 indices. -/
abbrev Index (n : ℕ) := AsSmall.{u} (Fin (n + 1))

/-- The original natural-number index of each finite stage. -/
def indexInclusion (n : ℕ) : Index.{u} n ⥤ ℕ where
  obj i := (AsSmall.down.obj i).val
  map a := homOfLE (leOfHom (AsSmall.down.map a))

/-- The final index of the finite model. -/
abbrev last (n : ℕ) : Index.{u} n := AsSmall.up.obj (Fin.last n)

/-- The last finite index is genuinely terminal. -/
def lastIsTerminal (n : ℕ) : IsTerminal (last.{u} n) :=
  IsTerminal.ofUniqueHom
    (fun i ↦ AsSmall.up.map (homOfLE (Fin.le_last (AsSmall.down.obj i))))
    (fun _ _ ↦ ULift.ext (Subsingleton.elim _ _))

variable (F : ℕ ⥤ Cat.{u, u})

/-- The original category sequence restricted to its first n + 1 stages. -/
def diagram (n : ℕ) : Index.{u} n ⥤ Cat.{u, u} := indexInclusion n ⋙ F

/-- The actual finite Grothendieck construction, not an assumed homotopy colimit. -/
abbrev Model (n : ℕ) := Grothendieck (diagram F n)

/-- The original terminal-transition projection to the final stage. -/
def projection (n : ℕ) : Model F n ⥤ F.obj n :=
  CategoryTheory.Grothendieck.Terminal.projection (diagram F n) (lastIsTerminal n)

/-- Include an original stage as a fiber of the finite model. -/
def inclusion (n : ℕ) (i : Fin (n + 1)) : F.obj i.val ⥤ Model F n :=
  Grothendieck.ι (diagram F n) (AsSmall.up.obj i)

/-- The finite model realizes to the final stage by the actual projection. -/
def classifyingHomotopyEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Model F n))
      (ClassifyingSpace (F.obj n)) :=
  CategoryTheory.Grothendieck.Terminal.classifyingHomotopyEquiv (diagram F n) (lastIsTerminal n)

theorem inclusion_projection (n : ℕ) (i : Fin (n + 1)) :
    inclusion F n i ⋙ projection F n = (F.map (homOfLE (Fin.le_last i))).toFunctor := by
  exact CategoryTheory.Grothendieck.Terminal.inclusion_projection (diagram F n)
    (lastIsTerminal n) (AsSmall.up.obj i)

theorem inclusion_classifying_projection (n : ℕ) (i : Fin (n + 1)) :
    classifyingSpaceMap (inclusion F n i) ≫ classifyingSpaceMap (projection F n) =
      classifyingSpaceMap (F.map (homOfLE (Fin.le_last i))).toFunctor := by
  rw [← classifyingSpaceMap_comp, inclusion_projection]

/-- The stage-zero unit retains its original transition to the last stage. -/
theorem initial_unit_projection (n : ℕ) :
    inclusion F n 0 ⋙ projection F n = (F.map (homOfLE (Nat.zero_le n))).toFunctor :=
  inclusion_projection F n 0

end CategoryTheory.Grothendieck.FiniteTelescope
