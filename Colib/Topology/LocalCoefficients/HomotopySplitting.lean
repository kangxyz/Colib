/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SquareRelative
public import Colib.Topology.LocalCoefficients.HomotopyTransportLaws
public import Colib.Topology.LocalCoefficients.HomotopyCorrection

/-!
Adapted from `Quillen/Topology/LocalCoefficients/HomotopySplitting.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual coefficient maps.

 # The actual two transport routes in a homotopy splitting -/

@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (i : C(X, Y)) (f : C(Y, Y)) (l : C(X, X)) (g : C(X, Y))
  (w : f.comp i = i.comp l) (H : i.Homotopy (f.comp g))
  (J : (g.comp l).Homotopy (f.comp g))

/-- Translate the specified splitting homotopy by the actual total action. -/
def splittingUpperHomotopy : (f.comp i).Homotopy (f.comp (f.comp g)) :=
  (ContinuousMap.Homotopy.refl f).comp H

/-- Run the splitting after the finite action and then the specified commuting homotopy. -/
def splittingLowerHomotopy : (f.comp i).Homotopy (f.comp (f.comp g)) :=
  ((H.compContinuousMap l).cast w.symm rfl).trans
    ((ContinuousMap.Homotopy.refl f).comp J)

variable (A : System.{u, u} Y)

/-- The factor map carries the coefficient transport of the original splitting. -/
def splittingFactorCoefficient : pullback i A ⟶ pullback g (pullback f A) :=
  (homotopyPullbackIso H A).hom ≫ (pullbackCompositionIso g f A).hom

/-- The upper relative route is exactly the splitting transport with pulled-back coefficients. -/
def splittingUpperCoefficient :
    pullback i (pullback f A) ⟶ pullback (f.comp g) (pullback f A) :=
  (homotopyPullbackIso H (pullback f A)).hom

/-- The lower route includes the finite-action coefficient map and the actual commuting track. -/
def splittingLowerCoefficient :
    pullback i (pullback f A) ⟶ pullback (f.comp g) (pullback f A) :=
  (squareCoefficientMap l i i f w A ≫
    pullbackMap l (splittingFactorCoefficient i f g H A) ≫
      (pullbackCompositionIso l g (pullback f A)).inv) ≫
        (homotopyPullbackIso J (pullback f A)).hom

/-- The upper route on homology is precisely the original stage inclusion map. -/
theorem splittingUpper_relative (n : ℕ) :
    relativeHomologyMap (f.comp g) (splittingUpperCoefficient i f g H A) n =
      pushforwardHomologyMap i (pullback f A) n := by
  have he := relativeHomologyMap_homotopy H (𝟙 _) (splittingUpperCoefficient i f g H A)
    (by simp [splittingUpperCoefficient]) n
  simpa only [relativeHomologyMap, coefficientHomologyMap_id, Category.id_comp] using he.symm

/-- The lower route factors through the original finite-stage action map. -/
theorem splittingLower_relative (n : ℕ) :
    relativeHomologyMap (f.comp g) (splittingLowerCoefficient i f l g w H J A) n =
      squareHomologyMap l i i f w A n ≫
        relativeHomologyMap g (splittingFactorCoefficient i f g H A) n := by
  rw [squareHomologyMap_eq_relative, relativeHomologyMap_comp]
  exact (relativeHomologyMap_homotopy J _ _ rfl n).symm

/-- The upper coefficient route is the actual translated homotopy track. -/
theorem splittingUpperCoefficient_track :
    (pullbackCompositionIso i f A).hom ≫ splittingUpperCoefficient i f g H A =
      (homotopyPullbackIso (splittingUpperHomotopy i f g H) A).hom ≫
        (pullbackCompositionIso (f.comp g) f A).hom := by
  apply NatTrans.ext
  funext x
  change 𝟙 _ ≫ transport (pullback f A) (H.evalAt x.as) =
    transport A (((ContinuousMap.Homotopy.refl f).comp H).evalAt x.as) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- The lower coefficient route is exactly the cast-and-concatenated homotopy track. -/
theorem splittingLowerCoefficient_track :
    (pullbackCompositionIso i f A).hom ≫ splittingLowerCoefficient i f l g w H J A =
      (homotopyPullbackIso (splittingLowerHomotopy i f l g w H J) A).hom ≫
        (pullbackCompositionIso (f.comp g) f A).hom := by
  rw [splittingLowerHomotopy, homotopyPullbackIso_trans_hom,
    homotopyPullbackIso_cast_hom]
  apply NatTrans.ext
  funext x
  simp only [splittingLowerCoefficient, splittingFactorCoefficient, squareCoefficientMap,
    pullbackCompositionIso, pullbackMap,
    NatTrans.comp_app, ContinuousMap.comp_assoc, eqToHom_refl,
    Category.comp_id, Category.assoc, eqToHom_app]
  change (eqToHom _ : fiber A (f (i x.as)) ⟶ fiber A (i (l x.as))) ≫
    transport A (H.evalAt (l x.as)) ≫ 𝟙 _ ≫
      transport (pullback f A) (J.evalAt x.as) =
    (eqToHom _ : fiber A (f (i x.as)) ⟶ fiber A (i (l x.as))) ≫
      transport A ((H.compContinuousMap l).evalAt x.as) ≫
      transport A (((ContinuousMap.Homotopy.refl f).comp J).evalAt x.as)
  simp only [Category.id_comp]
  rfl

end FundamentalGroupoid.LocalCoefficients
