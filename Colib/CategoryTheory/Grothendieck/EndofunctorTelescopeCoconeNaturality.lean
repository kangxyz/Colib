/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Grothendieck.EndofunctorTelescopeCocone
public import Colib.CategoryTheory.Grothendieck.FiberTransitions

/-!
Adapted from
`Quillen/Aglib/CategoryTheory/Grothendieck/EndofunctorTelescopeCoconeNaturality.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`; original cocone maps retained.

# Genuine transformations from coherent telescope successors

Coherent transformations between successor lax cocones extend to genuine
natural transformations with the prescribed components. More generally, for
any sequential Grothendieck construction, stage transformations compatible
with the original successor transitions extend uniquely to a transformation
between the original total functors. All original equality identifications
are retained through the fiber-transition composition formula.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v u' v'
open CategoryTheory
namespace CategoryTheory.Grothendieck.EndofunctorTelescope
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (T : C ⥤ C) (F : ℕ → C ⥤ D) (a : ∀ n, F n ⟶ T ⋙ F (n + 1))
  (G : ℕ → C ⥤ D) (b : ∀ n, G n ⟶ T ⋙ G (n + 1))
  (η : ∀ n, F n ⟶ G n)
  (hη : ∀ n, a n ≫ Functor.whiskerLeft T (η (n + 1)) = η n ≫ b n)

include hη

/-- A coherent successor square extends over every original iterate. -/
lemma coconeIterate_naturality (n k : ℕ) (X : C) :
    (coconeIterate T F a n k).app X ≫ (η (n + k)).app ((iterate T k).obj X) =
      (η n).app X ≫ (coconeIterate T G b n k).app X := by
  induction k with
  | zero =>
    simp only [coconeIterate_zero, iterate_zero, Functor.id_obj, NatTrans.id_app,
      Nat.add_zero, Category.id_comp, Category.comp_id]
  | succ k ih =>
    simp only [coconeIterate_succ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Nat.add_succ, iterate_succ, Functor.comp_obj]
    have hs := NatTrans.congr_app (hη (n + k)) ((iterate T k).obj X)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hs
    rw [Category.assoc, hs, ← Category.assoc, ih, Category.assoc]

/-- The full cocone arrows retain the prescribed stagewise transformation. -/
lemma coconeHom_naturality {n m : ℕ} (h : n ≤ m) (X : C) :
    (coconeHom T F a h).app X ≫ (η m).app ((iterate T (m - n)).obj X) =
      (η n).app X ≫ (coconeHom T G b h).app X := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [coconeHom, NatTrans.comp_app, eqToHom_app]
  generalize_proofs h₁ h₂
  revert h₁ h₂
  rw [show n + k - n = k by omega]
  intro h₁ h₂
  simp only [eqToHom_refl, Category.comp_id]
  exact coconeIterate_naturality T F a G b η hη n k X

/-- Coherent stage transformations extend to a genuine telescope transformation. -/
def natTransFromSequence : functorFromSequence T F a ⟶ functorFromSequence T G b where
  app X := (η X.base).app X.fiber
  naturality X Y f := by
    change ((coconeHom T F a (leOfHom f.base)).app X.fiber ≫ (F Y.base).map f.fiber) ≫
        (η Y.base).app Y.fiber =
      (η X.base).app X.fiber ≫
        (coconeHom T G b (leOfHom f.base)).app X.fiber ≫ (G Y.base).map f.fiber
    rw [Category.assoc, (η Y.base).naturality, ← Category.assoc,
      coconeHom_naturality T F a G b η hη, Category.assoc]

/-- The extended transformation has exactly the prescribed stage components. -/
lemma natTransFromSequence_app (n : ℕ) (X : C) :
    (natTransFromSequence T F a G b η hη).app ⟨n, X⟩ = (η n).app X := rfl

end CategoryTheory.Grothendieck.EndofunctorTelescope

namespace CategoryTheory.Grothendieck.Sequence
variable {D : Type u'} [Category.{v'} D] (F : ℕ ⥤ Cat.{v, u})
  (V W : Grothendieck F ⥤ D)
  (ε : ∀ n, Grothendieck.ι F n ⋙ V ⟶ Grothendieck.ι F n ⋙ W)

private lemma naturality_eqToHom
    (η : ∀ X, V.obj X ⟶ W.obj X) {X Y : Grothendieck F} (h : X = Y) :
    V.map (eqToHom h) ≫ η Y = η X ≫ W.map (eqToHom h) := by
  subst Y
  simp only [eqToHom_refl, Functor.map_id, Category.id_comp, Category.comp_id]

private lemma naturality_comp
    (η : ∀ X, V.obj X ⟶ W.obj X) {X Y Z : Grothendieck F} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : V.map f ≫ η Y = η X ≫ W.map f)
    (hg : V.map g ≫ η Z = η Y ≫ W.map g) :
    V.map (f ≫ g) ≫ η Z = η X ≫ W.map (f ≫ g) := by
  rw [V.map_comp, W.map_comp, Category.assoc, hg, ← Category.assoc, hf, Category.assoc]

variable
  (hε : ∀ (n : ℕ) (X : F.obj n),
    V.map ((Grothendieck.ιNatTrans (F := F) (homOfLE (Nat.le_succ n))).app X) ≫
        (ε (n + 1)).app (((F.map (homOfLE (Nat.le_succ n))).toFunctor).obj X) =
      (ε n).app X ≫
        W.map ((Grothendieck.ιNatTrans (F := F) (homOfLE (Nat.le_succ n))).app X))

include hε

/-- Compatibility with original successors implies compatibility with every stage transition. -/
lemma stageTransitions_natural {n m : ℕ} (h : n ≤ m) (X : F.obj n) :
    V.map ((Grothendieck.ιNatTrans (F := F) (homOfLE h)).app X) ≫
        (ε m).app (((F.map (homOfLE h)).toFunctor).obj X) =
      (ε n).app X ≫ W.map ((Grothendieck.ιNatTrans (F := F) (homOfLE h)).app X) := by
  induction h using Nat.leRec with
  | refl =>
    rw [show homOfLE (le_refl n) = 𝟙 n from Subsingleton.elim _ _,
      Grothendieck.fiberTransition_id]
    simp only [eqToHom_app]
    exact naturality_eqToHom F V W (fun Y => (ε Y.base).app Y.fiber) _
  | @le_succ_of_le m h ih =>
    rw [← homOfLE_comp h (Nat.le_succ m), Grothendieck.fiberTransition_comp]
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, eqToHom_app]
    exact naturality_comp F V W (fun Y => (ε Y.base).app Y.fiber) _ _ ih
      (naturality_comp F V W (fun Y => (ε Y.base).app Y.fiber) _ _ (hε m _)
        (naturality_eqToHom F V W (fun Y => (ε Y.base).app Y.fiber) _))

/-- Stage transformations compatible with original successors extend to the total functors. -/
def natTransFromSuccessors : V ⟶ W where
  app X := (ε X.base).app X.fiber
  naturality X Y f := by
    have hfV := congrArg V.map (Grothendieck.fiberTransition_factorization F f)
    have hfW := congrArg W.map (Grothendieck.fiberTransition_factorization F f)
    rw [← hfV, ← hfW]
    simp only [Functor.map_comp]
    change (V.map ((Grothendieck.ιNatTrans (F := F) f.base).app X.fiber) ≫
        (Grothendieck.ι F Y.base ⋙ V).map f.fiber) ≫ (ε Y.base).app Y.fiber =
      (ε X.base).app X.fiber ≫
        W.map ((Grothendieck.ιNatTrans (F := F) f.base).app X.fiber) ≫
        (Grothendieck.ι F Y.base ⋙ W).map f.fiber
    have hs := stageTransitions_natural F V W ε hε (leOfHom f.base) X.fiber
    have hb : homOfLE (leOfHom f.base) = f.base := Subsingleton.elim _ _
    rw [hb] at hs
    rw [Category.assoc, (ε Y.base).naturality, ← Category.assoc, hs, Category.assoc]

/-- The transformation retains each prescribed component literally. -/
lemma natTransFromSuccessors_app (n : ℕ) (X : F.obj n) :
    (natTransFromSuccessors F V W ε hε).app ⟨n, X⟩ = (ε n).app X := rfl

/-- Restriction to each original fiber is exactly the prescribed transformation. -/
lemma natTransFromSuccessors_stage (n : ℕ) :
    Functor.whiskerLeft (Grothendieck.ι F n) (natTransFromSuccessors F V W ε hε) = ε n := by
  apply NatTrans.ext
  funext X
  rfl

omit hε in
/-- Transformations of the original total functors are determined by their stage components. -/
lemma natTrans_ext_stages {α β : V ⟶ W}
    (h : ∀ n (X : F.obj n), α.app ⟨n, X⟩ = β.app ⟨n, X⟩) : α = β := by
  apply NatTrans.ext
  funext X
  exact h X.base X.fiber

/-- The extension is the unique transformation with the given stage components. -/
lemma natTransFromSuccessors_unique (α : V ⟶ W)
    (h : ∀ n (X : F.obj n), α.app ⟨n, X⟩ = (ε n).app X) :
    α = natTransFromSuccessors F V W ε hε :=
  natTrans_ext_stages F V W h

end CategoryTheory.Grothendieck.Sequence
