/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Functor.OfSequence
/-!
Adapted from `Quillen/Aglib/CategoryTheory/Grothendieck/EndofunctorTelescope.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, preserving the original
functors, associators and category universes.
 # Actual telescopes of endofunctors and commuting functor maps -/

@[expose] public section

open CategoryTheory
universe u v
namespace CategoryTheory.Grothendieck.EndofunctorTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C]
/-- The actual iterated endofunctor, with a fixed composition convention. -/
def iterate (T : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => iterate T n ⋙ T
@[simp] theorem iterate_zero (T : C ⥤ C) : iterate T 0 = 𝟭 C := rfl
@[simp] theorem iterate_succ (T : C ⥤ C) (n : ℕ) : iterate T (n + 1) = iterate T n ⋙ T := rfl
theorem iterate_add (T : C ⥤ C) (n m : ℕ) :
    iterate T (n + m) = iterate T n ⋙ iterate T m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [Nat.add_succ, iterate_succ, ih]; rfl

/-- The original sequence with transition given by the corresponding iterate. -/
def diagram (T : C ⥤ C) : ℕ ⥤ Cat.{v,u} where
  obj _ := Cat.of C
  map {n m} f := (iterate T (m - n)).toCatHom
  map_id n := by simp only [Nat.sub_self, iterate_zero]; rfl
  map_comp {n m k} f g := by
    change (iterate T (k - n)).toCatHom = (iterate T (m - n) ⋙ iterate T (k - m)).toCatHom
    rw [← iterate_add]
    have hf := leOfHom f
    have hg := leOfHom g
    congr 2; omega

/-- Iterate an actual commuting natural transformation, without strict commutation. -/
def commuteIterate {L T : C ⥤ C} (a : L ⋙ T ⟶ T ⋙ L) :
    ∀ n, L ⋙ iterate T n ⟶ iterate T n ⋙ L
  | 0 => 𝟙 L
  | n + 1 => Functor.whiskerRight (commuteIterate a n) T ≫
      Functor.whiskerLeft (iterate T n) a
@[simp] theorem commuteIterate_zero {L T : C ⥤ C} (a : L ⋙ T ⟶ T ⋙ L) (X : C) :
    (commuteIterate a 0).app X = 𝟙 _ := rfl
@[simp] theorem commuteIterate_succ {L T : C ⥤ C} (a : L ⋙ T ⟶ T ⋙ L) (n : ℕ) (X : C) :
    (commuteIterate a (n + 1)).app X =
      T.map ((commuteIterate a n).app X) ≫ a.app ((iterate T n).obj X) := rfl
theorem commuteIterate_add {L T : C ⥤ C} (a : L ⋙ T ⟶ T ⋙ L)
    (n m : ℕ) (X : C) :
    eqToHom (congrArg (fun F : C ⥤ C => F.obj (L.obj X)) (iterate_add T n m)) ≫
      (iterate T m).map ((commuteIterate a n).app X) ≫
        (commuteIterate a m).app ((iterate T n).obj X) =
      (commuteIterate a (n + m)).app X ≫
        eqToHom (congrArg (fun F : C ⥤ C => L.obj (F.obj X)) (iterate_add T n m)) := by
  induction m with
  | zero =>
    change (𝟙 _) ≫ (commuteIterate a n).app X ≫ (𝟙 _) =
      (commuteIterate a n).app X ≫ (𝟙 _)
    simp
  | succ m ih =>
    simp only [Nat.add_succ, iterate_succ, Functor.comp_map, commuteIterate_succ]
    have h := congrArg T.map ih
    simp only [Functor.map_comp, eqToHom_map] at h
    have hp := congrArg (fun k => k ≫ a.app ((iterate T m).obj ((iterate T n).obj X))) h
    have hn := a.naturality (eqToHom (congrArg (fun F : C ⥤ C => F.obj X)
      (iterate_add T n m)))
    simp only [Functor.comp_map, eqToHom_map] at hn
    calc
      _ = (T.map ((commuteIterate a (n + m)).app X) ≫
        eqToHom (congrArg (fun F : C ⥤ C => T.obj (L.obj (F.obj X)))
          (iterate_add T n m))) ≫ a.app ((iterate T m).obj ((iterate T n).obj X)) := by
            simpa only [Category.assoc] using hp
      _ = _ := by
        simp only [Category.assoc]
        exact congrArg (fun k => T.map ((commuteIterate a (n + m)).app X) ≫ k) hn

theorem commuteIterate_of_eq_zero {L T : C ⥤ C} (a : L ⋙ T ⟶ T ⋙ L)
    (n : ℕ) (h : n = 0) (X : C) :
    (commuteIterate a n).app X = eqToHom (by subst n; rfl) := by
  subst n
  rfl

theorem commuteIterate_of_add {L T : C ⥤ C} (a : L ⋙ T ⟶ T ⋙ L)
    (n m k : ℕ) (h : k = n + m) (X : C)
    (he : iterate T k = iterate T n ⋙ iterate T m) :
    eqToHom (congrArg (fun F : C ⥤ C => F.obj (L.obj X)) he) ≫
      (iterate T m).map ((commuteIterate a n).app X) ≫
        (commuteIterate a m).app ((iterate T n).obj X) =
      (commuteIterate a k).app X ≫
        eqToHom (congrArg (fun F : C ⥤ C => L.obj (F.obj X)) he) := by
  subst k
  exact commuteIterate_add a n m X

/-- The genuine Grothendieck construction of the endofunctor sequence. -/
abbrev Model (T : C ⥤ C) := Grothendieck (diagram T)

/-- An actual commuting transformation induces an endofunctor on the original telescope. -/
def map {L T : C ⥤ C} (a : L ⋙ T ⟶ T ⋙ L) : Model T ⥤ Model T where
  obj X := ⟨X.base, L.obj X.fiber⟩
  map {X Y} f :=
    { base := f.base
      fiber := (commuteIterate a (Y.base - X.base)).app X.fiber ≫ L.map f.fiber }
  map_id X := by
    refine Grothendieck.ext (F := diagram T) _ _ ?_ ?_
    · rfl
    simp only [Grothendieck.id_fiber, diagram, eqToHom_map, eqToHom_refl, Category.id_comp]
    rw [commuteIterate_of_eq_zero a _ (Nat.sub_self _) ]
    simp only [eqToHom_trans]
  map_comp {X Y Z} f g := by
    refine Grothendieck.ext (F := diagram T) _ _ ?_ ?_
    · rfl
    simp only [Grothendieck.comp_fiber, diagram, Functor.map_comp, eqToHom_map,
      Category.assoc, eqToHom_refl, Category.id_comp]
    have hn := (commuteIterate a (Z.base - Y.base)).naturality f.fiber
    dsimp only [Functor.comp_map] at hn
    have hf := leOfHom f.base
    have hg := leOfHom g.base
    have h : Z.base - X.base = (Y.base - X.base) + (Z.base - Y.base) := by omega
    have he : iterate T (Z.base - X.base) =
        iterate T (Y.base - X.base) ⋙ iterate T (Z.base - Y.base) := by
      rw [h, iterate_add]
    have hc := commuteIterate_of_add a _ _ _ h X.fiber he
    simp only [Functor.toCatHom_toFunctor]
    rw [← Category.assoc ((iterate T (Z.base - Y.base)).map (L.map f.fiber)), hn]
    simp only [Category.assoc]
    simpa only [Category.assoc, diagram, Functor.toCatHom_toFunctor] using
      congrArg (fun k => k ≫ L.map ((iterate T (Z.base - Y.base)).map f.fiber) ≫
        L.map g.fiber) hc.symm

theorem inclusion_map {L T : C ⥤ C} (a : L ⋙ T ⟶ T ⋙ L) (n : ℕ) :
    Grothendieck.ι (diagram T) n ⋙ map a = L ⋙ Grothendieck.ι (diagram T) n := by
  refine Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Grothendieck.ext (F := diagram T) _ _ ?_ ?_
  · rfl
  dsimp [map, Grothendieck.ι]
  rw [commuteIterate_of_eq_zero a _ (Nat.sub_self _)]
  simp only [Functor.map_comp, eqToHom_map, Category.id_comp]
  rw [← Category.assoc, eqToHom_trans]

end CategoryTheory.Grothendieck.EndofunctorTelescope
