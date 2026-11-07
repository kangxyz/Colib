/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.HomotopySplitting

/-!
Adapted from `Quillen/Topology/LocalCoefficients/AbelianHomotopySplitting.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual coefficient maps.


# Abelian correction makes an actual homotopy splitting detect kernel classes

The hypotheses are specified spatial maps, their actual homotopies, and a finite
support of one given class. No homology equivalence of any action is assumed.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace FundamentalGroupoid.LocalCoefficients
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The corrected splitting argument kills the original image of a finite-stage
kernel class with stable finite support. -/
theorem abelian_homotopy_splitting_kernel_zero
    (i : C(X, Y)) (f : C(Y, Y)) (l : C(X, X)) (g : C(X, Y))
    (w : f.comp i = i.comp l) (H : i.Homotopy (f.comp g))
    (J : (g.comp l).Homotopy (f.comp g))
    (hF : ∀ a b : Y, Joined (f a) (f b) → Joined a b)
    (A : System.{u, u} Y) (hA : AbelianMonodromy A) (n : ℕ)
    (x : homology (pullback i (pullback f A)) n) (s : Finset X)
    (hc : ∀ a ∈ s, ∀ b ∈ s, Joined (i a) (i b) → Joined a b)
    (hs : ∀ (D : System.{u, u} X) (η θ : pullback i (pullback f A) ⟶ D),
      (∀ p ∈ s, η.app (FundamentalGroupoid.mk p) = θ.app (FundamentalGroupoid.mk p)) →
        coefficientHomologyMap η n x = coefficientHomologyMap θ n x)
    (hx : squareHomologyMap l i i f w A n x = 0) :
    pushforwardHomologyMap i (pullback f A) n x = 0 := by
  obtain ⟨T, hT⟩ := finite_homotopy_correction_exists
    (splittingUpperHomotopy i f g H) (splittingLowerHomotopy i f l g w H J) hA s
      (fun a ha b hb hab ↦ hc a ha b hb
        ((show Joined _ _ from ⟨H.evalAt a⟩).trans
          ((hF _ _ hab).trans ⟨(H.evalAt b).symm⟩)))
  let η := splittingUpperCoefficient i f g H A
  let θ := splittingLowerCoefficient i f l g w H J A
  let c := pullbackMap f T.hom
  have he := hs (pullback (f.comp g) (pullback f A))
    (η ≫ pullbackMap (f.comp g) c) θ (fun p hp ↦ ?_)
  · rw [coefficientHomologyMap_comp] at he
    have hz : relativeHomologyMap (f.comp g) θ n x = 0 := by
      rw [show θ = splittingLowerCoefficient i f l g w H J A from rfl,
        splittingLower_relative]
      change relativeHomologyMap g (splittingFactorCoefficient i f g H A) n
        (squareHomologyMap l i i f w A n x) = 0
      rw [hx, map_zero]
    have hn := congrArg (fun k ↦ k (coefficientHomologyMap η n x))
      (pushforwardHomologyMap_coefficient_naturality (f.comp g) c n)
    have hh := (hn.symm.trans (congrArg (pushforwardHomologyMap (f.comp g) (pullback f A) n) he))
    change coefficientHomologyMap c n (relativeHomologyMap (f.comp g) η n x) =
      relativeHomologyMap (f.comp g) θ n x at hh
    rw [hz] at hh
    change coefficientHomologyMap c n
      (relativeHomologyMap (f.comp g) (splittingUpperCoefficient i f g H A) n x) = 0 at hh
    rw [splittingUpper_relative] at hh
    let e := Functor.isoWhiskerLeft (FundamentalGroupoid.map f) T
    have : IsIso (coefficientHomologyMap c n) := by
      change IsIso (coefficientHomologyIso e n).hom
      infer_instance
    apply (ModuleCat.mono_iff_injective (coefficientHomologyMap c n)).mp inferInstance
    rw [map_zero]
    exact hh
  · have hη := NatTrans.congr_app (splittingUpperCoefficient_track i f g H A)
      (FundamentalGroupoid.mk p)
    have hθ := NatTrans.congr_app (splittingLowerCoefficient_track i f l g w H J A)
      (FundamentalGroupoid.mk p)
    change 𝟙 _ ≫ η.app (FundamentalGroupoid.mk p) =
      transport A ((splittingUpperHomotopy i f g H).evalAt p) ≫ 𝟙 _ at hη
    change 𝟙 _ ≫ θ.app (FundamentalGroupoid.mk p) =
      transport A ((splittingLowerHomotopy i f l g w H J).evalAt p) ≫ 𝟙 _ at hθ
    simp only [Category.id_comp, Category.comp_id] at hη hθ
    change η.app (FundamentalGroupoid.mk p) ≫
      T.hom.app (FundamentalGroupoid.mk (f (f (g p)))) = θ.app (FundamentalGroupoid.mk p)
    rw [hη, hθ]
    exact hT p hp

end FundamentalGroupoid.LocalCoefficients
