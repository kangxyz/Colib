/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Homotopy.Contractible

/-!
# Actual maps between contractible spaces

Every specified continuous map between contractible spaces is a homotopy equivalence,
with the constant map at the supplied source point as its inverse.

Implementation provenance: the exact-map equivalence is extracted from
`Quillen/Topology/Realization/BisimplicialContractibility.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. This lower owner uses only the
contractibility API and retains the original forward map and chosen inverse point.
-/
@[expose] public section

noncomputable section

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Any two actual maps into a contractible space are homotopic. -/
theorem homotopic_of_contractible [ContractibleSpace Y] (f g : C(X, Y)) : f.Homotopic g := by
  obtain ⟨y, h⟩ := id_nullhomotopic Y
  have hf : f.Homotopic (const X y) := h.comp (Homotopic.refl f)
  have hg : g.Homotopic (const X y) := h.comp (Homotopic.refl g)
  exact hf.trans hg.symm

/-- Every actual map between contractible spaces is an equivalence with that exact forward map. -/
def homotopyEquivOfContractible [ContractibleSpace X] [ContractibleSpace Y]
    (f : C(X, Y)) (x : X) : HomotopyEquiv X Y where
  toFun := f
  invFun := const Y x
  left_inv := homotopic_of_contractible _ _
  right_inv := homotopic_of_contractible _ _

@[simp] theorem homotopyEquivOfContractible_toFun [ContractibleSpace X] [ContractibleSpace Y]
    (f : C(X, Y)) (x : X) : (homotopyEquivOfContractible f x).toFun = f := rfl

@[simp] theorem homotopyEquivOfContractible_invFun [ContractibleSpace X] [ContractibleSpace Y]
    (f : C(X, Y)) (x : X) : (homotopyEquivOfContractible f x).invFun = const Y x := rfl

end ContinuousMap
