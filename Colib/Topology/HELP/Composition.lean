/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HELP.Compact
public import Colib.Topology.Homotopy.BoundaryCorrection

/-! # Composition of compact HELP maps

The final homotopy extends the complete originally prescribed boundary
homotopy. Its temporary constant prefix is removed by the proved relative
interval-square extension, rather than silently changing the boundary data.


Implementation provenance:
`Quillen/Topology/HELP/Composition.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u

namespace Topology
variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Compact HELP is closed under composition of the actual forward maps. -/
theorem CompactHomotopyExtensionLiftingProperty.comp
    {f : C(X, Y)} {g : C(Y, Z)}
    (hg : CompactHomotopyExtensionLiftingProperty g)
    (hf : CompactHomotopyExtensionLiftingProperty f) :
    CompactHomotopyExtensionLiftingProperty (g.comp f) := by
  intro A B _ _ i hi a b H
  obtain ⟨c, hc, K, hK⟩ := hg A B i hi (f.comp a) b H
  let R : (f.comp a).Homotopy (c.comp i.hom) :=
    (ContinuousMap.Homotopy.refl (f.comp a)).cast rfl hc.symm
  obtain ⟨d, hd, L, hL⟩ := hf A B i hi a c R
  let J := ((ContinuousMap.Homotopy.refl g).comp L).trans K
  let H' : (((g.comp f).comp d).comp i.hom).Homotopy (b.comp i.hom) :=
    H.cast (by
      apply ContinuousMap.ext
      intro x
      exact congrArg (g ∘ f) (ContinuousMap.congr_fun hd x).symm) rfl
  have hJ : ∀ t x, J (t, i x) = Path.delayReflLeft 0 (H'.evalAt x) t := by
    intro t x
    rw [Path.delayReflLeft_zero]
    simp only [J, ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
    split_ifs
    · change g (L (_, i x)) = _
      rw [hL]
      exact congrArg (g ∘ f) (ContinuousMap.congr_fun hd x).symm
    · exact hK _ x
  obtain ⟨J', hJ'⟩ := TopCat.homotopyExtensionProperty_unpad_boundary hi
    (Z := TopCat.of Z) J H' hJ
  exact ⟨d, hd, J', hJ'⟩

end Topology
