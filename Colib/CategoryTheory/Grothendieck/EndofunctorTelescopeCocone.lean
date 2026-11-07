/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Grothendieck.EndofunctorTelescope

/-!
Adapted from `Quillen/Aglib/CategoryTheory/Grothendieck/EndofunctorTelescopeCocone.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; original cocone maps retained.

# Successor lax cocones on an actual endofunctor telescope

A family of fiber functors and coherent one-step arrows extends to a functor
from the original Grothendieck telescope. The extension retains the prescribed
fiber functors and the original successor maps exactly. All changes between
iteration counts use explicit equality identifications.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
noncomputable section
universe u v u' v'
open CategoryTheory
namespace CategoryTheory.Grothendieck.EndofunctorTelescope
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (T : C ⥤ C) (F : ℕ → C ⥤ D) (a : ∀ n, F n ⟶ T ⋙ F (n + 1))

/-- Iterate the given successor arrows, keeping the original fiber indices. -/
def coconeIterate : ∀ n k, F n ⟶ iterate T k ⋙ F (n + k)
  | n, 0 => 𝟙 (F n)
  | n, k + 1 => coconeIterate n k ≫ Functor.whiskerLeft (iterate T k) (a (n + k))

/-- The zero-length cocone arrow is the identity. -/
lemma coconeIterate_zero (n : ℕ) : coconeIterate T F a n 0 = 𝟙 (F n) := rfl

/-- A successor extends the cocone by the prescribed next arrow. -/
lemma coconeIterate_succ (n k : ℕ) :
    coconeIterate T F a n (k + 1) =
      coconeIterate T F a n k ≫ Functor.whiskerLeft (iterate T k) (a (n + k)) := rfl

private lemma step_app_heq {n m : ℕ} (h : n = m) {X Y : C} (e : X = Y) :
    (a n).app X ≍ (a m).app Y := by
  subst m
  subst Y
  rfl

/-- Concatenation agrees before inserting the explicit endpoint identifications. -/
lemma coconeIterate_add_heq (n k l : ℕ) (X : C) :
    (coconeIterate T F a n k).app X ≫
        (coconeIterate T F a (n + k) l).app ((iterate T k).obj X) ≍
      (coconeIterate T F a n (k + l)).app X := by
  induction l with
  | zero => simp [coconeIterate]
  | succ l ih =>
    simp only [Nat.add_succ, coconeIterate_succ, NatTrans.comp_app, Functor.whiskerLeft_app]
    rw [← Category.assoc]
    refine heq_comp rfl ?_ ?_ ih ?_
    · simp only [Nat.add_assoc, iterate_add, Functor.comp_obj]
    · simp only [Nat.add_assoc, iterate_add, Functor.comp_obj, iterate_succ]
    · exact step_app_heq T F a (Nat.add_assoc n k l)
        (congrArg (fun G : C ⥤ C => G.obj X) (iterate_add T k l)).symm

/-- Concatenation retains precisely the arithmetic and iterate identifications. -/
lemma coconeIterate_add (n k l : ℕ) (X : C) :
    (coconeIterate T F a n k).app X ≫
        (coconeIterate T F a (n + k) l).app ((iterate T k).obj X) ≫
        eqToHom (by rw [← Nat.add_assoc, iterate_add]; rfl) =
      (coconeIterate T F a n (k + l)).app X := by
  rw [← Category.assoc]
  apply eq_of_heq
  exact (comp_eqToHom_heq _ _).trans (coconeIterate_add_heq T F a n k l X)

/-- The full lax cocone arrow for an original ordered pair of stages. -/
def coconeHom {n m : ℕ} (h : n ≤ m) : F n ⟶ iterate T (m - n) ⋙ F m :=
  coconeIterate T F a n (m - n) ≫ eqToHom (by rw [Nat.add_sub_of_le h])

/-- The lax cocone respects the original identity identification. -/
lemma coconeHom_id (n : ℕ) :
    coconeHom T F a (le_refl n) = eqToHom (by
      simp only [Nat.sub_self, iterate_zero]; rfl) := by
  dsimp only [coconeHom]
  generalize_proofs h₁ h₂
  revert h₁ h₂
  rw [Nat.sub_self]
  intro h₁ h₂
  simp only [coconeIterate_zero, Category.id_comp]

/-- The lax cocone respects the original composite-stage identification. -/
lemma coconeHom_comp {n m k : ℕ} (f : n ⟶ m) (g : m ⟶ k) :
    coconeHom T F a (leOfHom (f ≫ g)) =
      coconeHom T F a (leOfHom f) ≫
        Functor.whiskerLeft (iterate T (m - n))
          (coconeHom T F a (leOfHom g)) ≫
            eqToHom (by
              change iterate T (m - n) ⋙ iterate T (k - m) ⋙ F k =
                iterate T (k - n) ⋙ F k
              rw [← Functor.assoc, ← iterate_add]
              congr 2
              have hf := leOfHom f
              have hg := leOfHom g
              omega) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom f)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le (leOfHom g)
  apply NatTrans.ext
  funext X
  simp only [coconeHom, NatTrans.comp_app, Functor.whiskerLeft_app,
    eqToHom_app]
  generalize_proofs h₁ h₂ h₃ h₄
  revert h₁ h₂ h₃ h₄
  rw [show n + l + r - n = l + r by omega,
    show n + l - n = l by omega, show n + l + r - (n + l) = r by omega]
  intro h₁ h₂ h₃ h₄
  simp only [eqToHom_refl, Category.comp_id]
  rw [← Category.assoc]
  apply eq_of_heq
  exact (comp_eqToHom_heq _ _).trans
    ((coconeIterate_add_heq T F a n l r X).symm.trans (comp_eqToHom_heq _ _).symm)

/-- A coherent successor lax cocone extends to the actual telescope. -/
def functorFromSequence : Model T ⥤ D where
  obj X := (F X.base).obj X.fiber
  map {X Y} f := (coconeHom T F a (leOfHom f.base)).app X.fiber ≫
    (F Y.base).map f.fiber
  map_id X := by
    simp [Grothendieck.id_fiber, coconeHom_id, eqToHom_map]
  map_comp {X Y Z} f g := by
    change (coconeHom T F a (leOfHom (f.base ≫ g.base))).app X.fiber ≫
      (F Z.base).map (f ≫ g).fiber = _
    rw [coconeHom_comp T F a f.base g.base]
    simp [Grothendieck.comp_fiber, eqToHom_map, diagram]

/-- The one-step lax cocone arrow is the originally supplied transformation. -/
lemma coconeHom_succ (n : ℕ) (X : C) :
    (coconeHom T F a (Nat.le_succ n)).app X =
      (a n).app X ≫ eqToHom (by rw [show n.succ - n = 1 by omega]; rfl) := by
  dsimp only [coconeHom, NatTrans.comp_app, eqToHom_app]
  generalize_proofs h₁ h₂
  revert h₁ h₂
  rw [show n.succ - n = 1 by omega]
  intro h₁ h₂
  simp [coconeIterate]

/-- A successor arrow with its actual arithmetic identification. -/
def successorArrow (n : ℕ) {X Y : C} (f : T.obj X ⟶ Y) :
    (⟨n, X⟩ : Model T) ⟶ ⟨n + 1, Y⟩ where
  base := homOfLE (Nat.le_succ n)
  fiber := eqToHom (by
    change (iterate T (n + 1 - n)).obj X = T.obj X
    rw [Nat.add_sub_cancel_left]
    rfl) ≫ f

/-- The extension sends a successor arrow to the prescribed one-step formula. -/
lemma functorFromSequence_map_successor (n : ℕ) {X Y : C} (f : T.obj X ⟶ Y) :
    (functorFromSequence T F a).map (successorArrow T n f) =
      (a n).app X ≫ (F (n + 1)).map f := by
  change (coconeHom T F a (Nat.le_succ n)).app X ≫
      (F (n + 1)).map (eqToHom _ ≫ f) = _
  rw [coconeHom_succ, Functor.map_comp]
  simp only [eqToHom_map, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]

/-- The extension restricts exactly to each prescribed fiber functor. -/
lemma inclusion_functorFromSequence (n : ℕ) :
    Grothendieck.ι (diagram T) n ⋙ functorFromSequence T F a = F n := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (coconeHom T F a (le_refl n)).app X ≫ (F n).map (eqToHom _ ≫ f) = _
  rw [coconeHom_id]
  simp only [eqToHom_app, Functor.map_comp, eqToHom_map,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end CategoryTheory.Grothendieck.EndofunctorTelescope
