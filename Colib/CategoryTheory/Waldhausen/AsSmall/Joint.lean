/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.AsSmall.Basic
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Functoriality
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.SecondEndpoint
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Actual joint-cylinder data on a common-universe model

The original exact joint functor, its coproduct endpoints, and its weak projection
are transported through the genuine `AsSmall` equivalence. The second-endpoint
section identity is retained for the actual transported endpoint maps.


Implementation provenance:
`Quillen/Waldhausen/SmallModel/Joint.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C]

local instance jointSmallUp_isEquivalence : (AsSmall.up : C ⥤ AsSmall.{0} C).IsEquivalence :=
  (AsSmall.equiv : C ≌ AsSmall.{0} C).isEquivalence_functor
local instance jointSmallDown_isEquivalence : (AsSmall.down : AsSmall.{0} C ⥤ C).IsEquivalence :=
  (AsSmall.equiv : C ≌ AsSmall.{0} C).isEquivalence_inverse

namespace Structure
variable (W : Structure C)

/-- Lowering actual arrows preserves their pointwise Waldhausen structure. -/
theorem asSmall_down_mapArrow_exact :
    IsExact (ArrowCategory.waldhausenStructure W.asSmall).cof
      (ArrowCategory.waldhausenStructure W.asSmall).weq
      (ArrowCategory.waldhausenStructure W).cof
      (ArrowCategory.waldhausenStructure W).weq
      (AsSmall.down : AsSmall.{0} C ⥤ C).mapArrow where
  zero h := IsZero.of_full_of_faithful_of_isZero
    (AsSmall.up : C ⥤ AsSmall.{0} C).mapArrow _ h
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map (AsSmall.down : AsSmall.{0} C ⥤ C).mapArrow

end Structure
namespace Fibration.RowFactorization
variable {W : Structure C} {N : NestedWeakEquivalences W}

/-- The original joint cylinder with the actual lifted endpoint and projection maps. -/
def JointData.asSmall (D : JointData N) : JointData N.asSmall where
  joint := (AsSmall.down : AsSmall.{0} C ⥤ C).mapArrow ⋙ D.joint ⋙
    ExtensionCategory.postcompose W W.asSmall W.asSmall_up_exact
  exact := W.asSmall_down_mapArrow_exact.comp
    (D.exact.comp (ExtensionCategory.postcompose_exact W W.asSmall W.asSmall_up_exact))
  inl := {
    app f := (AsSmall.up : C ⥤ AsSmall.{0} C).map (D.inl.app ((AsSmall.down : AsSmall.{0} C ⥤
      C).mapArrow.obj f))
    naturality f g α := by
      exact congrArg (AsSmall.up : C ⥤ AsSmall.{0} C).map
        (D.inl.naturality ((AsSmall.down : AsSmall.{0} C ⥤ C).mapArrow.map α)) }
  inr := {
    app f := (AsSmall.up : C ⥤ AsSmall.{0} C).map (D.inr.app ((AsSmall.down : AsSmall.{0} C ⥤
      C).mapArrow.obj f))
    naturality f g α := by
      exact congrArg (AsSmall.up : C ⥤ AsSmall.{0} C).map
        (D.inr.naturality ((AsSmall.down : AsSmall.{0} C ⥤ C).mapArrow.map α)) }
  coproduct f := mapIsColimitOfPreservesOfIsColimit (AsSmall.up : C ⥤ AsSmall.{0} C) _ _
    (D.coproduct ((AsSmall.down : AsSmall.{0} C ⥤ C).mapArrow.obj f))
  projection := {
    app f := (AsSmall.up : C ⥤ AsSmall.{0} C).map (D.projection.app ((AsSmall.down : AsSmall.{0} C
      ⥤ C).mapArrow.obj f))
    naturality f g α := by
      exact congrArg (AsSmall.up : C ⥤ AsSmall.{0} C).map
        (D.projection.naturality ((AsSmall.down : AsSmall.{0} C ⥤ C).mapArrow.map α)) }
  factorization f := congrArg (AsSmall.up : C ⥤ AsSmall.{0} C).map
    (D.factorization ((AsSmall.down : AsSmall.{0} C ⥤ C).mapArrow.obj f))
  weak f := D.weak ((AsSmall.down : AsSmall.{0} C ⥤ C).mapArrow.obj f)

/-- The actual transported second endpoint retains its original section identity. -/
theorem SecondEndpointSection.asSmall {D : JointData N} (hs : SecondEndpointSection N D) :
    SecondEndpointSection N.asSmall D.asSmall := by
  intro f
  exact congrArg (AsSmall.up : C ⥤ AsSmall.{0} C).map (hs ((AsSmall.down : AsSmall.{0} C ⥤
    C).mapArrow.obj f))

end Fibration.RowFactorization
end CategoryTheory.Waldhausen
