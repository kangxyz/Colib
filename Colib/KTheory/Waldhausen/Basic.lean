/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Basic
public import Colib.CategoryTheory.Waldhausen.SConstruction.Zero
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Homotopy groups of the unnormalized Waldhausen S-construction

The space below realizes the existing unnormalized IsZero-diagonal grid model.
The nonnegative
K-groups are its shifted homotopy groups. Weak equivalences occur in the
simplices themselves. This is a definition of connective K-groups, not a
proof of additivity, comparison with Quillen Q, or localization. In
particular it does not construct the nonconnective spectrum of TT §7.
No strict chosen-zero S-model comparison or nerve presentation is asserted here.

## Implementation provenance

Adapted from `Quillen/Waldhausen/KTheory.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original hypotheses, universes,
basepoint and degree shift are retained. The model is the unnormalized diagonal IsZero construction.
-/
@[expose] public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen

variable {C : Type u} [Category.{v} C]
variable (cof weq : MorphismProperty C)

/-- The genuine topological realization of the diagonal S-construction. -/
def delooping : TopCat.{max u v} := SSet.toTop.obj (sSet cof weq)

/-- The chosen zero object supplies a based vertex. -/
def basepoint [cof.ContainsIdentities] [weq.ContainsIdentities]
    (Z : C) (hZ : IsZero Z) : delooping cof weq :=
  SSet.toTop.map (SSet.yonedaEquiv.symm (zeroSimplex cof weq Z hZ (op ⦋0⦌))) default

/-- The S-construction's connective groups at a specified zero object.
This construction is available before verifying the Waldhausen axioms; the
structure-specialized `Structure.K` below records that distinction. -/
abbrev groups [cof.ContainsIdentities] [weq.ContainsIdentities]
    (Z : C) (hZ : IsZero Z) (n : ℕ) :=
  HomotopyGroup.Pi (n + 1) (delooping cof weq) (basepoint cof weq Z hZ)

namespace Structure

variable (W : Structure C)

/-- The realization of the unnormalized S-grid of a Waldhausen category. -/
abbrev Delooping := delooping W.cof W.weq

/-- The point represented by the specified zero object. -/
abbrev kBasepoint : W.Delooping := basepoint W.cof W.weq W.zero W.isZero

/-- Waldhausen's connective K-groups. -/
abbrev K (n : ℕ) := groups W.cof W.weq W.zero W.isZero n

/-- These are actual homotopy groups, with their existing group structure. -/
example (n : ℕ) : Group (W.K n) := inferInstance

/-- Positive K-degrees are commutative by higher homotopy commutativity.
K₀ commutativity still requires the S-construction additivity theorem. -/
example (n : ℕ) : CommGroup (W.K (n + 1)) := inferInstance

end Structure

end CategoryTheory.Waldhausen

attribute [colib_tag "COL-0155",
  colib_ref "Waldhausen1985" "Section 1.3, pp. 328-330" "background"
    "Background for the stated unnormalized IsZero model; not a strict-model identification"]
  CategoryTheory.Waldhausen.delooping
  CategoryTheory.Waldhausen.basepoint
  CategoryTheory.Waldhausen.groups
  CategoryTheory.Waldhausen.Structure.K
