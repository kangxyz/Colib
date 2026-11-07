/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.MatrixAutomorphisms
public import Colib.LinearAlgebra.Matrix.IdempotentAutomorphismClass

/-!
Implementation provenance: `Quillen/Algebra/Matrix/IdempotentSplitExtension.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Stable automorphism classes and split extensions

Extending an automorphism of a retract by the identity on its complementary
summand preserves its original stable elementary-quotient class.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Idempotents
namespace Matrix.RightModule
variable {R : Type u} [Ring R]

/-- Identity extension along a genuine retract preserves the stable automorphism class. -/
theorem automorphismClass_splitExtension {P Q : ProjectiveMatrices R}
    (i : P ⟶ Q) (r : Q ⟶ P) (hr : i ≫ r = 𝟙 P) (g : Aut P) (h : Aut Q)
    (hh : homMatrix h.hom = homMatrix i * homMatrix g.hom * homMatrix r +
      idempotentMatrix Q - homMatrix i * homMatrix r) :
    automorphismClass Q h = automorphismClass P g := by
  let e := retractPresentationIso i r hr
  let g' := Aut.autMulEquivOfIso e g
  have he : extendAut h = extendAut g' := by
    apply Units.ext
    change homMatrix h.hom + (1 - idempotentMatrix Q) =
      homMatrix i * homMatrix g.hom * homMatrix r +
        ((1 : Matrix (Fin Q.X.rank) (Fin Q.X.rank) R) - homMatrix i * homMatrix r)
    rw [hh]
    abel
  change StableGeneralLinear.finiteClass R Q.X.rank (extendAut h) = _
  rw [he]
  exact automorphismClass_conjugate e g

end Matrix.RightModule
