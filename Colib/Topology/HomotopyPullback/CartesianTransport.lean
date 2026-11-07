/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.SourceEquivalence

/-!
# Transport of homotopy-cartesian comparisons across source equivalences

An ordinary homotopy equivalence of total sources over a common base induces
an equivalence of their actual path-space homotopy pullbacks. Consequently,
if the comparison for one commuting square is a homotopy equivalence, the
comparison for the other is too. The resulting forward map is exactly the
canonical constant-path comparison of the original square.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/HomotopyPullback/CartesianTransport.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the actual maps and hypotheses. -/
@[expose] public section


noncomputable section

open scoped Topology unitInterval

universe u

namespace Topology

/-- Cancel a specified homotopy equivalence from the right of a composite,
retaining exactly the specified first continuous map. -/
def homotopyEquivCancelRight {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {a : C(A, B)} {b : C(B, C)}
    (e : ContinuousMap.HomotopyEquiv B C) (he : e.toFun = b)
    (e' : ContinuousMap.HomotopyEquiv A C) (he' : e'.toFun = b.comp a) :
    ContinuousMap.HomotopyEquiv A B := by
  apply HomotopyFiber.replaceForward (e'.trans e.symm) a
  change a.Homotopic (e.invFun.comp e'.toFun)
  rw [he']
  have H := e.left_inv.symm.comp (ContinuousMap.Homotopic.refl a)
  simpa only [he, ContinuousMap.comp_assoc, ContinuousMap.id_comp] using H

@[simp]
theorem homotopyEquivCancelRight_toFun {A B C : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    {a : C(A, B)} {b : C(B, C)}
    (e : ContinuousMap.HomotopyEquiv B C) (he : e.toFun = b)
    (e' : ContinuousMap.HomotopyEquiv A C) (he' : e'.toFun = b.comp a) :
    (Topology.homotopyEquivCancelRight e he e' he').toFun = a := rfl

end Topology

namespace Topology.HomotopyPullback

variable {X Y A B Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace Z]

/-- Transport a genuine homotopy-cartesian comparison across an ordinary
homotopy equivalence of total sources over the common base. Only the supplied
comparison on the right is assumed to be a homotopy equivalence. -/
def comparisonEquivOfSourceEquiv
    (p : C(X, B)) (q : C(Y, B)) (k : C(A, B))
    (r : C(Z, A)) (f : C(Z, X)) (g : C(Z, Y))
    (commP : p.comp f = k.comp r) (commQ : q.comp g = k.comp r)
    (E : ContinuousMap.HomotopyEquiv X Y)
    (hE : q.comp E.toFun = p) (hg : E.toFun.comp f = g)
    (e : ContinuousMap.HomotopyEquiv Z (HomotopyPullback q k))
    (he : e.toFun = comparison q k r g commQ) :
    ContinuousMap.HomotopyEquiv Z (HomotopyPullback p k) := by
  subst p
  apply Topology.homotopyEquivCancelRight
    (a := comparison (q.comp E.toFun) k r f commP)
    (sourceEquiv k q E) rfl e
  rw [he]
  ext z
  apply Subtype.ext
  change (r z, g z, ContinuousMap.const unitInterval (k (r z))) =
    (r z, E.toFun (f z), ContinuousMap.const unitInterval (k (r z)))
  have hz : E.toFun (f z) = g z := ContinuousMap.congr_fun hg z
  rw [hz]

/-- Transport retains the actual canonical constant-path comparison. -/
@[simp]
theorem comparisonEquivOfSourceEquiv_toFun
    (p : C(X, B)) (q : C(Y, B)) (k : C(A, B))
    (r : C(Z, A)) (f : C(Z, X)) (g : C(Z, Y))
    (commP : p.comp f = k.comp r) (commQ : q.comp g = k.comp r)
    (E : ContinuousMap.HomotopyEquiv X Y)
    (hE : q.comp E.toFun = p) (hg : E.toFun.comp f = g)
    (e : ContinuousMap.HomotopyEquiv Z (HomotopyPullback q k))
    (he : e.toFun = comparison q k r g commQ) :
    (comparisonEquivOfSourceEquiv p q k r f g commP commQ E hE hg e he).toFun =
      comparison p k r f commP := by
  subst p
  rfl

end Topology.HomotopyPullback
