/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Topology.Realization.SimplexAttachmentDeformation

/-!
# Parameterized simplex attachment collar regression tests

The homotopy equivalence concerns the open collar and the old space only.
No deformation retraction of the entire attachment or general HEP is asserted.
-/

open CategoryTheory CategoryTheory.Limits stdSimplex Topology
open scoped Topology unitInterval

universe u

noncomputable section

namespace TopCat

variable (X : TopCat.{u}) (n : ℕ) {C D : TopCat.{u}}
  {f : TopCat.of (X × boundary n) ⟶ C}
  {g : TopCat.of (X × _root_.stdSimplex ℝ (Fin (n + 1))) ⟶ D} {j : C ⟶ D}
  (sq : IsPushout (parameterizedSimplexBoundaryInclusion X n) f g j)

example (p : X × boundary n) :
    parameterizedSimplexBoundaryInclusion X n p = (p.1, p.2.1) := rfl

example : IsClosedEmbedding (parameterizedSimplexBoundaryInclusion X n) :=
  isClosedEmbedding_parameterizedSimplexBoundary X n

example (z : X × _root_.stdSimplex ℝ (Fin (n + 1))) :
    simplexAttachmentDefect X n sq (g z) = simplexBoundaryDefect z.2 :=
  simplexAttachmentDefect_cell X n sq z

example (c : C) : simplexAttachmentDefect X n sq (j c) = 1 :=
  simplexAttachmentDefect_old X n sq c

example : simplexAttachmentCollar X n sq =
    {z | (1 : ℝ) / 2 < simplexAttachmentDefect X n sq z} := rfl

example : IsOpen (simplexAttachmentCollar X n sq) :=
  isOpen_simplexAttachmentCollar X n sq

example : IsClosedEmbedding j := simplexAttachment_old_isClosedEmbedding X n sq

example (z : X × _root_.stdSimplex ℝ (Fin (n + 1))) :
    g z ∈ simplexAttachmentCollar X n sq ↔ z.2 ∈ simplexBoundaryCollar n :=
  simplexAttachmentCollar_cell_iff X n sq z

example : Set.range j ⊆ simplexAttachmentCollar X n sq :=
  range_old_subset_simplexAttachmentCollar X n sq

example (t : unitInterval) (z : D) : simplexAttachmentRadial X n sq (t, z) =
    simplexAttachmentRadialCylinder X n sq (z, ULift.up t) := rfl

example (t : unitInterval) (z : X × _root_.stdSimplex ℝ (Fin (n + 1))) :
    simplexAttachmentRadial X n sq (t, g z) =
      g (z.1, simplexBoundaryRetractPoint (z.2, t)) :=
  simplexAttachmentRadial_cell X n sq t z

example (t : unitInterval) (c : C) : simplexAttachmentRadial X n sq (t, j c) = j c :=
  simplexAttachmentRadial_old X n sq t c

example (z : D) : simplexAttachmentRadial X n sq (0, z) = z :=
  simplexAttachmentRadial_zero X n sq z

example (t : unitInterval) (z : simplexAttachmentCollar X n sq) :
    simplexAttachmentRadial X n sq (t, z.1) ∈ simplexAttachmentCollar X n sq :=
  simplexAttachmentRadial_mem_collar X n sq t z

example (z : simplexAttachmentCollar X n sq) :
    simplexAttachmentRadial X n sq (1, z.1) ∈ Set.range j :=
  simplexAttachmentRadial_one_mem_range X n sq z

example (c : C) : (simplexAttachmentCollarInclusion X n sq c).1 = j c := rfl

example (z : simplexAttachmentCollar X n sq) :
    j (simplexAttachmentCollarRetraction X n sq z) =
      simplexAttachmentRadial X n sq (1, z.1) :=
  simplexAttachmentCollarRetractionFun_spec X n sq z

example (c : C) : simplexAttachmentCollarRetraction X n sq
    (simplexAttachmentCollarInclusion X n sq c) = c :=
  simplexAttachmentCollarRetraction_inclusion X n sq c

example (t : unitInterval) (z : simplexAttachmentCollar X n sq) :
    (simplexAttachmentCollarHomotopy X n sq (t, z)).1 =
      simplexAttachmentRadial X n sq (t, z.1) := rfl

example (t : unitInterval) (c : C) :
    simplexAttachmentCollarHomotopy X n sq (t, simplexAttachmentCollarInclusion X n sq c) =
      simplexAttachmentCollarInclusion X n sq c := by
  apply Subtype.ext
  exact simplexAttachmentRadial_old X n sq t c

example : (simplexAttachmentCollarHomotopyEquiv X n sq).toFun =
    simplexAttachmentCollarInclusion X n sq := rfl

example : (simplexAttachmentCollarHomotopyEquiv X n sq).invFun =
    simplexAttachmentCollarRetraction X n sq := rfl

example (t : unitInterval) (z : D) :
    simplexAttachmentRadialHomotopy X n sq (t, z) = simplexAttachmentRadial X n sq (t, z) := rfl

end TopCat
