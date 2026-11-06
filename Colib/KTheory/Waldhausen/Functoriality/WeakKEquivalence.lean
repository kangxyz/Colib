/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Functoriality
public import Colib.KTheory.Waldhausen.ZeroFunctor
public import Colib.Topology.HomotopyFiber.WeakInvariance

/-! # Canonical K-equivalences from complete weakness of the actual realization

The actual zero normalization is connected to the original exact functor
by its genuine natural-isomorphism homotopy. Complete weak equivalence
therefore passes to the normalized realization, and the original based
K-homomorphism is bijective in every nonnegative degree.

Implementation provenance:
`Quillen/Waldhausen/Functoriality/WeakKEquivalence.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat SSet
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The original canonical zero normalization retains complete weakness via
its actual natural-isomorphism homotopy. No based homotopy is assumed. -/
theorem rebasedDeloopingMap_isWeakHomotopyEquivalence
    (h : IsWeakHomotopyEquivalence (deloopingMap hF).hom) :
    IsWeakHomotopyEquivalence (deloopingMap hF.rebase).hom :=
  h.of_homotopy (weakNaturalTransformationRealizationHomotopy W V hF hF.rebase
    (CategoryTheory.rebaseFunctorIso F W.zero V.zero ((hF.zero W.isZero).iso V.isZero)).hom
    (fun _ ↦ V.weq_iso _ inferInstance))

/-- Complete weakness gives bijectivity for an arbitrary specified image zero. -/
theorem groupsMapOfZeroEq_bijective_of_isWeakHomotopyEquivalence
    (h : IsWeakHomotopyEquivalence (deloopingMap hF).hom)
    (Z : C) (hZ : IsZero Z) (Z' : D) (hZ' : IsZero Z')
    (h0 : F.obj Z = Z') (n : ℕ) :
    Function.Bijective (groupsMapOfZeroEq hF Z hZ Z' hZ' h0 n) := by
  subst Z'
  have hb {x : W.Delooping} {y : V.Delooping} (e : (deloopingMap hF).hom x = y) :
      Function.Bijective (HomotopyGroup.piMap n (deloopingMap hF).hom e) := by
    subst y
    exact h.homotopy_bijective x (n+1)
  exact hb (deloopingMap_basepoint hF Z hZ)

/-- The literal canonical K-map is bijective, including K-zero. -/
theorem KMap_bijective_of_isWeakHomotopyEquivalence
    (h : IsWeakHomotopyEquivalence (deloopingMap hF).hom) (n : ℕ) :
    Function.Bijective (KMap hF n) :=
  groupsMapOfZeroEq_bijective_of_isWeakHomotopyEquivalence hF.rebase
    (rebasedDeloopingMap_isWeakHomotopyEquivalence hF h)
    W.zero W.isZero V.zero V.isZero (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) n

/-- Package the existing canonical K-homomorphism as an actual group equivalence. -/
def KEquivOfWeakRealization
    (h : IsWeakHomotopyEquivalence (deloopingMap hF).hom) (n : ℕ) : W.K n ≃* V.K n :=
  MulEquiv.ofBijective (KMap hF n) (KMap_bijective_of_isWeakHomotopyEquivalence hF h n)

/-- The equivalence retains the unchanged original canonical K-homomorphism. -/
@[simp] theorem KEquivOfWeakRealization_coe (h : IsWeakHomotopyEquivalence (deloopingMap
    hF).hom) (n : ℕ) :
    (↑(KEquivOfWeakRealization hF h n) : W.K n →* V.K n) = KMap hF n := rfl


end CategoryTheory.Waldhausen
