/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.AsSmall.Basic
public import Colib.KTheory.Waldhausen.Functoriality
public import Colib.KTheory.Waldhausen.ZeroFunctor
public import Colib.Topology.Homotopy.HomotopyGroup.Equivalence
public import Colib.Topology.Realization.EdgePath

/-!
# Realization and K-group comparisons for Mathlib AsSmall

`AsSmall` lifts objects and homs into their original maximum universe. Both
morphism classes are pulled back from the original category. The actual
S-constructions are simplicially isomorphic by exact up/down postcomposition.


Implementation provenance:
`Quillen/Waldhausen/SmallModel/Basic.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology
open CategoryTheory Limits Opposite
open scoped Simplicial Topology
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C]

namespace Structure
variable (W : Structure C)

/-- This is an actual homeomorphism of the original realization spaces. -/
def asSmallDeloopingHomeomorph : W.Delooping ≃ₜ W.asSmall.Delooping :=
  TopCat.homeoOfIso (SSet.toTop.mapIso W.asSmallSSetIso)

/-- The lifted simplicial isomorphism preserves the original zero diagram exactly. -/
@[simp] theorem asSmallSSetIso_zero (n : SimplexCategoryᵒᵖ) :
    W.asSmallSSetIso.hom.app n (zeroSimplex W.cof W.weq W.zero W.isZero n) =
      zeroSimplex W.asSmall.cof W.asSmall.weq W.asSmall.zero W.asSmall.isZero n := by
  apply Subtype.ext
  rfl

/-- The actual homeomorphism retains the chosen realization basepoint. -/
@[simp] theorem asSmallDeloopingHomeomorph_basepoint :
    W.asSmallDeloopingHomeomorph W.kBasepoint = W.asSmall.kBasepoint := by
  change SSet.toTop.map W.asSmallSSetIso.hom
    (SSet.realizationPoint (zeroSimplex W.cof W.weq W.zero W.isZero (op ⦋0⦌))) = _
  rw [SSet.realizationPoint_naturality, asSmallSSetIso_zero]
  rfl

/-- The original homotopy groups are identified through the actual based homeomorphism. -/
def asSmallKEquiv (n : ℕ) : W.K n ≃* W.asSmall.K n :=
  homotopyEquivPiEquiv W.asSmallDeloopingHomeomorph.toHomotopyEquiv
    W.asSmallDeloopingHomeomorph_basepoint n

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem asSmallKEquiv_coe (n : ℕ) :
    (↑(W.asSmallKEquiv n) : W.K n →* W.asSmall.K n) =
      HomotopyGroup.piMap n W.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun
        W.asSmallDeloopingHomeomorph_basepoint := rfl


end Structure

section Functoriality
variable {D : Type u} [Category.{v} D] {W : Structure C} {W' : Structure D}
  {F : C ⥤ D}

/-- The square commutes as actual continuous maps, before any group transport. -/
theorem asSmallDeloopingHomeomorph_naturality
    (hF : IsExact W.cof W.weq W'.cof W'.weq F) :
    W'.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun.comp (deloopingMap hF).hom =
      (deloopingMap hF.asSmall).hom.comp
          W.asSmallDeloopingHomeomorph.toHomotopyEquiv.toFun := by
  change (SSet.toTop.map (sSetMap hF) ≫ SSet.toTop.map W'.asSmallSSetIso.hom).hom =
    (SSet.toTop.map W.asSmallSSetIso.hom ≫ SSet.toTop.map (sSetMap hF.asSmall)).hom
  rw [← SSet.toTop.map_comp, ← SSet.toTop.map_comp, asSmallSSetIso_naturality]

/-- Strictly zero-preserving original functors retain their exact original K-maps. -/
theorem asSmallKEquiv_naturality_of_zeroEq
    (hF : IsExact W.cof W.weq W'.cof W'.weq F) (h0 : F.obj W.zero = W'.zero) (n : ℕ) :
    (W'.asSmallKEquiv n).toMonoidHom.comp (KMap hF n) =
      (KMap hF.asSmall n).comp (W.asSmallKEquiv n).toMonoidHom := by
  simp only [MulEquiv.toMonoidHom_eq_coe]
  rw [Structure.asSmallKEquiv_coe, Structure.asSmallKEquiv_coe,
    KMap_eq_piMap_of_zeroEq hF h0,
    KMap_eq_piMap_of_zeroEq hF.asSmall (congrArg AsSmall.up.obj h0),
    ← HomotopyGroup.mapHom_comp, ← HomotopyGroup.mapHom_comp]
  congr 1
  exact asSmallDeloopingHomeomorph_naturality hF

/-- All original canonical K-maps commute with the actual small-model equivalences;
zero rebasing is transported by its genuine natural isomorphism. -/
theorem asSmallKEquiv_naturality (hF : IsExact W.cof W.weq W'.cof W'.weq F) (n : ℕ) :
    (W'.asSmallKEquiv n).toMonoidHom.comp (KMap hF n) =
      (KMap hF.asSmall n).comp (W.asSmallKEquiv n).toMonoidHom := by
  have hh := asSmallKEquiv_naturality_of_zeroEq hF.rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) n
  have hi := (CategoryTheory.rebaseFunctorIso F W.zero W'.zero
    ((hF.zero W.isZero).iso W'.isZero)).symm
  have hsmall := Functor.isoWhiskerLeft (AsSmall.down : AsSmall.{0} C ⥤ C)
    (Functor.isoWhiskerRight hi (AsSmall.up : D ⥤ AsSmall.{0} D))
  rw [KMap_eq_of_iso hF.rebase hF hi,
    KMap_eq_of_iso hF.rebase.asSmall hF.asSmall hsmall] at hh
  exact hh

end Functoriality
end CategoryTheory.Waldhausen
