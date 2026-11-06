/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Resolution.Presentation
public import Colib.CategoryTheory.ExactCategory.Resolution.Closure

/-! Extracted from `Quillen/Aglib/CategoryTheory/ExactCategory/Resolution/Presentation.lean`.
Pinned Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd and
Aglib 2c34f185fa859e862661f939cd216b07bcccfb26.
Actual maps and assumptions are retained; no Resolution K-equivalence is claimed. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)
variable (P : ObjectProperty C) [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
variable (Q : ObjectProperty C) [Q.IsClosedUnderIsomorphisms]
  [E.IsExtensionClosed Q] [E.IsKernelClosed Q]

omit [P.ContainsZero] [P.IsClosedUnderIsomorphisms] in
/-- Presentation independence: any admissible epimorphism from a `Q`-object
onto an object presented by a `P`-object with `Q`-kernel has `Q`-kernel, provided
`P ≤ Q`. The pullback proof needs no projective lifting property. -/
lemma kernel_mem_of_resolutionStep (hPQ : P ≤ Q) {S : ShortComplex C}
    (hS : E.conflation S) (hB : Q S.X₂) (hC : E.ResolutionStep P Q S.X₃) : Q S.X₁ := by
  obtain ⟨T⟩ := hC
  let : HasPullback T.g S.g := E.deflation.hasPullback S.g T.deflation
  let : HasPullback S.g T.g := hasPullback_symmetry _ _
  have hPB : Q (pullback T.g S.g) :=
    E.prop_pullback Q T.conflation T.syzygy_mem hB S.g
  have hPB' : Q (pullback S.g T.g) := Q.prop_of_iso (pullbackSymmetry _ _) hPB
  exact IsKernelClosed.prop_kernel (E := E) (P := Q)
    (S := pullbackConflation (S := S) T.middle T.g)
    (E.pullbackConflation_mem hS T.g) hPB' (hPQ _ T.middle_mem)

end CategoryTheory.ExactCategory.ExactStructure
