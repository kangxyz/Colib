/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.ClassifyingSpace.FiniteGrothendieckTelescope
public import Colib.Topology.FilteredRealization.NerveColimit
/-!
Adapted from `Quillen/Topology/ClassifyingSpace/GrothendieckTelescope.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the original categorical maps.


# The infinite Grothendieck model as an actual filtered nerve colimit

The original finite-prefix inclusions and transitions form a strict categorical
cocone. Every object and arrow lies in an explicit finite prefix; the inclusions
are faithful and injective on objects. Thus their nerves have the infinite
Grothendieck nerve as their actual filtered colimit. Original fiber inclusions
and stabilization natural transformations are retained, including the stage-zero
unit. No ordinary/fat topological telescope identification is asserted.
-/

@[expose] public section

open CategoryTheory.Grothendieck.FiniteTelescope


open CategoryTheory Limits
noncomputable section
universe u
namespace CategoryTheory.Grothendieck.Telescope
open CategoryTheory.Grothendieck.FiniteTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (F : ℕ ⥤ Cat.{u, u})

/-- The actual infinite Grothendieck construction of the original sequence. -/
abbrev Model := Grothendieck F

/-- Include a finite prefix by its original base indices and fiber arrows. -/
def prefixInclusion (n : ℕ) : CategoryTheory.Grothendieck.FiniteTelescope.Model F n ⥤ Model F where
  obj X := ⟨(AsSmall.down.obj X.base).val, X.fiber⟩
  map f := { base := homOfLE (leOfHom (AsSmall.down.map f.base)), fiber := f.fiber }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The original inclusion of one finite prefix in a larger prefix. -/
def prefixTransition {n m : ℕ} (h : n ≤ m) :
    CategoryTheory.Grothendieck.FiniteTelescope.Model F n ⥤
      CategoryTheory.Grothendieck.FiniteTelescope.Model F m where
  obj X := ⟨AsSmall.up.obj ⟨(AsSmall.down.obj X.base).val,
    lt_of_lt_of_le (AsSmall.down.obj X.base).isLt (Nat.succ_le_succ h)⟩, X.fiber⟩
  map f :=
    { base := AsSmall.up.map (homOfLE (leOfHom (AsSmall.down.map f.base)))
      fiber := f.fiber }
  map_id _ := rfl
  map_comp _ _ := rfl

theorem prefixTransition_refl (n : ℕ) : prefixTransition F (le_refl n) = 𝟭 _ := rfl

theorem prefixTransition_comp {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    prefixTransition F (h.trans h') = prefixTransition F h ⋙ prefixTransition F h' := rfl

theorem prefixTransition_inclusion {n m : ℕ} (h : n ≤ m) :
    prefixTransition F h ⋙ prefixInclusion F m = prefixInclusion F n := rfl

/-- A common-universe model of natural-number prefix indices. -/
abbrev PrefixIndex := AsSmall.{u} ℕ

/-- The strict diagram of actual finite-prefix categories. -/
def prefixDiagram : PrefixIndex.{u} ⥤ Cat.{u, u} where
  obj n := Cat.of (CategoryTheory.Grothendieck.FiniteTelescope.Model F (AsSmall.down.obj n))
  map a := (prefixTransition F (leOfHom (AsSmall.down.map a))).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The original prefix inclusions into the infinite Grothendieck category. -/
def prefixCocone : Cocone (prefixDiagram F) where
  pt := Cat.of (Model F)
  ι := { app n := (prefixInclusion F (AsSmall.down.obj n)).toCatHom
         naturality _ _ _ := rfl }

instance prefixInclusion_faithful (n : ℕ) : (prefixInclusion F n).Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨fb, ff⟩ := f
    obtain ⟨gb, gf⟩ := g
    have hb : fb = gb := ULift.ext _ _ (Subsingleton.elim _ _)
    subst gb
    have hf : ff = gf := by
      injection h
    subst gf
    rfl

theorem prefixInclusion_obj_injective (n : ℕ) :
    Function.Injective (prefixInclusion F n).obj := by
  intro X Y h
  obtain ⟨xb, xf⟩ := X
  obtain ⟨yb, yf⟩ := Y
  have hv : (AsSmall.down.obj xb).val = (AsSmall.down.obj yb).val :=
    congrArg Grothendieck.base h
  have hb : xb = yb := ULift.ext _ _ (Fin.ext hv)
  subst yb
  have hf : xf = yf := by injection h
  subst yf
  rfl

theorem prefix_objects_surjective (X : Model F) :
    ∃ n : PrefixIndex.{u}, ∃ x : (prefixDiagram F).obj n,
      (FilteredNerveColimit.leg (prefixDiagram F) (prefixCocone F) n).obj x = X := by
  obtain ⟨n, x⟩ := X
  exact ⟨AsSmall.up.obj n, ⟨last n, x⟩, rfl⟩

theorem prefix_arrows_surjective :
    FilteredNerveColimit.ArrowSurjective (prefixDiagram F) (prefixCocone F) := by
  intro X Y f
  let n := max X.base Y.base
  let x : CategoryTheory.Grothendieck.FiniteTelescope.Model F n :=
    ⟨AsSmall.up.obj ⟨X.base, Nat.lt_succ_of_le (Nat.le_max_left _ _)⟩, X.fiber⟩
  let y : CategoryTheory.Grothendieck.FiniteTelescope.Model F n :=
    ⟨AsSmall.up.obj ⟨Y.base, Nat.lt_succ_of_le (Nat.le_max_right _ _)⟩, Y.fiber⟩
  let g : x ⟶ y := { base := AsSmall.up.map (homOfLE (leOfHom f.base)), fiber := f.fiber }
  refine ⟨AsSmall.up.obj n, x, y, g, rfl, rfl, ?_⟩
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

theorem prefix_eventually_equal :
    FilteredNerveColimit.EventuallyEqualObjects (prefixDiagram F) (prefixCocone F) := by
  intro n x y h
  exact ⟨n, 𝟙 n, prefixInclusion_obj_injective F _ h⟩


/-- Finite categorical lifting proves the actual filtered nerve colimit. -/
def nerveCoconeIsColimit : IsColimit (nerveFunctor.mapCocone (prefixCocone F)) := by
  letI (j : PrefixIndex.{u}) :
      (FilteredNerveColimit.leg (prefixDiagram F) (prefixCocone F) j).Faithful :=
    prefixInclusion_faithful F (AsSmall.down.obj j)
  exact FilteredNerveColimit.nerveCoconeIsColimit (prefixDiagram F) (prefixCocone F)
    (prefix_objects_surjective F) (prefix_arrows_surjective F) (prefix_eventually_equal F)

theorem fiber_prefix_inclusion (n : ℕ) (i : Fin (n + 1)) :
    CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n i ⋙ prefixInclusion F n =
      Grothendieck.ι F i.val := rfl

theorem fiber_prefix_classifying (n : ℕ) (i : Fin (n + 1)) :
    classifyingSpaceMap (CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n i) ≫
        classifyingSpaceMap (prefixInclusion F n) =
      classifyingSpaceMap (Grothendieck.ι F i.val) := by
  rw [← classifyingSpaceMap_comp, fiber_prefix_inclusion]

/-- The original stabilization arrow gives its canonical transformation of fiber inclusions. -/
def stageTransitionNatTrans {n m : ℕ} (h : n ≤ m) :
    Grothendieck.ι F n ⟶ (F.map (homOfLE h)).toFunctor ⋙ Grothendieck.ι F m :=
  Grothendieck.ιNatTrans _

/-- The same stabilization transformation already lies in the larger finite prefix. -/
def finiteStageTransitionNatTrans {n m : ℕ} (h : n ≤ m) :
    CategoryTheory.Grothendieck.FiniteTelescope.inclusion F n (Fin.last n) ⋙ prefixTransition F h ⟶
      (F.map (homOfLE h)).toFunctor ⋙
        CategoryTheory.Grothendieck.FiniteTelescope.inclusion F m (Fin.last m) :=
  Grothendieck.ιNatTrans (F := CategoryTheory.Grothendieck.FiniteTelescope.diagram F m)
    (AsSmall.up.map (homOfLE
      (show (⟨n, Nat.lt_succ_of_le h⟩ : Fin (m + 1)) ≤ Fin.last m from h)))

theorem finiteStageTransitionNatTrans_infinite {n m : ℕ} (h : n ≤ m) :
    Functor.whiskerRight (finiteStageTransitionNatTrans F h) (prefixInclusion F m) =
      stageTransitionNatTrans F h := rfl

/-- The original stabilization transformation realizes to its actual track homotopy. -/
def stageTransitionClassifyingHomotopy {n m : ℕ} (h : n ≤ m) :
    (classifyingSpaceMap (Grothendieck.ι F n)).hom.Homotopy
      ((classifyingSpaceMap (Grothendieck.ι F m)).hom.comp
        (classifyingSpaceMap (F.map (homOfLE h)).toFunctor).hom) := by
  simpa only [classifyingSpaceMap_comp, TopCat.hom_comp] using
    classifyingSpaceNaturalTransformationHomotopy (stageTransitionNatTrans F h)

end CategoryTheory.Grothendieck.Telescope
