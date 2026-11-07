/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # The actual relative pushout cube

In a pointwise pushout of arrows, the new relative target map is a cobase
change of the old relative target map. The proof is three applications of
actual pushout pasting/cancellation, with no cofibration assumption.


Implementation provenance:
`Quillen/Waldhausen/ExtensionCategory/PushoutCube.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{v} C]

/-- The displayed relative target square is a genuine pushout. -/
theorem relativePushoutCube
    {A B C₀ D A' B' C' D' R S : C}
    {a : A ⟶ B} {b : A ⟶ C₀} {c : B ⟶ D} {d : C₀ ⟶ D}
    {a' : A' ⟶ B'} {b' : A' ⟶ C'} {c' : B' ⟶ D'} {d' : C' ⟶ D'}
    {u : A ⟶ A'} {w : C₀ ⟶ C'}
    {i : A' ⟶ R} {j : B ⟶ R} {k : R ⟶ B'}
    {l : C' ⟶ S} {m : D ⟶ S} {t : S ⟶ D'} {r : R ⟶ S}
    (hsource : IsPushout a b c d) (htarget : IsPushout a' b' c' d')
    (hrelative : IsPushout u a i j) (hnew : IsPushout w d l m)
    (face : u ≫ b' = b ≫ w)
    (hik : i ≫ k = a') (hlt : l ≫ t = d')
    (hir : i ≫ r = b' ≫ l) (hjr : j ≫ r = c ≫ m)
    (hcomm : k ≫ c' = r ≫ t) : IsPushout k r c' t := by
  have htotal := hsource.paste_vert hnew.flip
  rw [← face, ← hjr] at htotal
  have hleft := htotal.of_top hir hrelative.flip
  rw [← hik, ← hlt] at htarget
  exact htarget.of_left hcomm hleft

end CategoryTheory.Waldhausen.ExtensionCategory
