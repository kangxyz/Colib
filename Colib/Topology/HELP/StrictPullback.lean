/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyFiber.StrictWeakTransport
public import Colib.Topology.HELP.TwoOfThree

/-! # Compact HELP for the actual strict-fiber map after base change

The strict-pullback map retains its parameter and applies the original
source map. The actual strict-fiber homeomorphisms commute with it exactly.
Compact HELP transfers through these genuine homeomorphisms by two-of-three.


Implementation provenance:
`Quillen/Topology/HELP/StrictPullback.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Topology
universe u
namespace Topology.HomotopyPullback
variable {E F B D : Type u}
    [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace B] [TopologicalSpace D]
    (p : C(E, B)) (q : C(F, B)) (f : C(E, F)) (sq : q.comp f = p) (r : C(D, B))

/-- The literal map of strict pullbacks over the unchanged parameter. -/
def strictPullbackMapOver :
    C({z : D × E // p z.2 = r z.1}, {z : D × F // q z.2 = r z.1}) where
  toFun z := ⟨(z.1.1, f z.1.2), (ContinuousMap.congr_fun sq z.1.2).trans z.2⟩
  continuous_toFun := by fun_prop

@[simp] theorem strictPullbackMapOver_parameter
    (z : {z : D × E // p z.2 = r z.1}) :
    (strictPullbackMapOver p q f sq r z).1.1 = z.1.1 := rfl

@[simp] theorem strictPullbackMapOver_source
    (z : {z : D × E // p z.2 = r z.1}) :
    (strictPullbackMapOver p q f sq r z).1.2 = f z.1.2 := rfl

@[simp] theorem strictBaseProjection_strictPullbackMapOver :
    (strictBaseProjection q r).comp (strictPullbackMapOver p q f sq r) =
      strictBaseProjection p r := rfl

/-- The actual fiber homeomorphisms identify the new strict-fiber map with
its original counterpart by an exact square of continuous maps. -/
theorem strictPullbackFiberHomeomorph_naturality (d : D) :
    (strictPullbackFiberHomeomorph q r d).toHomotopyEquiv.toFun.comp
      (HomotopyFiber.strictMapOver (strictBaseProjection p r) (strictBaseProjection q r)
        (strictPullbackMapOver p q f sq r) rfl d) =
    (HomotopyFiber.strictMapOver p q f sq (r d)).comp
      (strictPullbackFiberHomeomorph p r d).toHomotopyEquiv.toFun := rfl

/-- Compact HELP of the original strict-fiber map transfers to the actual
strict-fiber map of the literal pullbacks. No fibration assumption is needed
for this homeomorphism transport itself. -/
theorem strictPullbackMapOver_fiber_compactHELP (d : D)
    (hf : CompactHomotopyExtensionLiftingProperty (HomotopyFiber.strictMapOver p q f sq (r d))) :
    CompactHomotopyExtensionLiftingProperty
      (HomotopyFiber.strictMapOver (strictBaseProjection p r) (strictBaseProjection q r)
        (strictPullbackMapOver p q f sq r) rfl d) := by
  have h₁ := compactHELP_of_homotopyEquiv (strictPullbackFiberHomeomorph p r d).toHomotopyEquiv
  have h₂ := compactHELP_of_homotopyEquiv (strictPullbackFiberHomeomorph q r d).toHomotopyEquiv
  have h : CompactHomotopyExtensionLiftingProperty
      ((strictPullbackFiberHomeomorph q r d).toHomotopyEquiv.toFun.comp
        (HomotopyFiber.strictMapOver (strictBaseProjection p r) (strictBaseProjection q r)
          (strictPullbackMapOver p q f sq r) rfl d)) := by
    rw [strictPullbackFiberHomeomorph_naturality]
    exact hf.comp h₁
  exact h.cancel_second h₂

end Topology.HomotopyPullback
