/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.QuillenComparison.RowChain
public import Colib.AlgebraicTopology.SimplicialSet.ChainCoreNerve
public import Colib.CategoryTheory.Waldhausen.QuillenComparison.SimplicialMap
public import Colib.AlgebraicTopology.SimplicialSet.MixedNerve

/-! # The actual bisimplicial row comparison -/
/- Implementation provenance: adapted from
   Quillen/Waldhausen/QuillenComparison/BisimplicialMap.lean at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. The actual native weak rows,
   chain-core nerve and prescribed comparison map are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen.QuillenComparison
open QuotientRows SSet


/-- Reindexing central intervals gives the original ordinal-reindexed chain. -/
theorem centralIntervalFunctor_naturality {n m : SimplexCategory} (α : n ⟶ m) :
    centralIntervalFunctor n ⋙ nestedIntervalMap (EdgewiseSubdivision.ε.map α) =
      (SimplexCategory.toCat.map α).toFunctor ⋙ centralIntervalFunctor m := by
  apply CategoryTheory.Functor.ext (fun i ↦ centralInterval_naturality α i)

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)

/-- Changing an interval by equality conjugates its Q-isomorphism by the
corresponding object equalities, with no choice of representatives. -/
theorem qIso_app_congr {I : Type*} [Category I] {F G : I ⥤ C} (e : F ≅ G)
    (p q : I) (h : p = q) :
    (E.qIsoOfIso (e.app p)).hom =
      eqToHom (congrArg (fun i ↦ QConstruction.of E.deflation E.inflation (F.obj i)) h) ≫
        (E.qIsoOfIso (e.app q)).hom ≫
          eqToHom (congrArg (fun i ↦
            QConstruction.of E.deflation E.inflation (G.obj i)) h.symm) := by
  subst q
  simp

private theorem chainCore_eqToHom_app {D : Type*} [Category D] {n : ℕ}
    {F G : Core (ComposableArrows D n)} (h : F = G) (i : Fin (n + 1)) :
    (eqToHom h).iso.hom.app i = eqToHom (congrArg (fun H ↦ H.of.obj i) h) := by
  subst G
  rfl

/-- The row comparison is strictly simplicially natural, including its actual
natural-isomorphism morphisms. -/
theorem rowChainComparison_reindex {n m : SimplexCategory} (α : n ⟶ m) :
    weakRowsReindex (ofExactCategory E) (EdgewiseSubdivision.ε.map α) ⋙ rowChainComparison E n =
      rowChainComparison E m ⋙ chainCoreReindex (QConstruction E.deflation E.inflation) α := by
  have hobj (F : WeakRows (ofExactCategory E) (EdgewiseSubdivision.ε.obj m)) :
      ((weakRowsReindex (ofExactCategory E) (EdgewiseSubdivision.ε.map α) ⋙
        rowChainComparison E n).obj F) =
        ((rowChainComparison E m ⋙
          chainCoreReindex (QConstruction E.deflation E.inflation) α).obj F) := by
    change Core.mk _ = Core.mk _
    apply congrArg Core.mk
    change centralIntervalFunctor n ⋙ intervalQFunctor E ((reindex (ofExactCategory E)
      (EdgewiseSubdivision.ε.map α)).obj F.obj) =
      (SimplexCategory.toCat.map α).toFunctor ⋙ centralIntervalFunctor m ⋙ intervalQFunctor E F.obj
    rw [intervalQFunctor_reindex, ← Functor.assoc, centralIntervalFunctor_naturality,
      Functor.assoc]
  refine CategoryTheory.Functor.ext hobj ?_
  intro F G e
  apply Core.hom_ext
  ext i
  change _ = (eqToHom (hobj F) : _ ⟶ _).iso.hom.app i ≫
    ((rowChainComparison E m ⋙ chainCoreReindex (QConstruction E.deflation E.inflation) α).map
      e).iso.hom.app i ≫
      (eqToHom (hobj G).symm : _ ⟶ _).iso.hom.app i
  simp only [chainCore_eqToHom_app]
  exact qIso_app_congr E (weakRowIso E e) _ _
    (congrArg (fun p ↦ interval p.left p.right p.endpoints) (centralInterval_naturality α i))

/-- The canonical map of bisimplicial sets from subdivided exact rows to
isomorphism groupoids of composable Q-arrows. -/
def rowChainNerveMap : EdgewiseSubdivision.ε.op ⋙ weakRowNerve (ofExactCategory E) ⟶
    chainCoreNerve (QConstruction E.deflation E.inflation) where
  app n := MixedNerve.nerveMap.{u, v, max u v} (rowChainComparison E n.unop)
  naturality n m α := by
    ext k G
    change G ⋙ weakRowsReindex (ofExactCategory E) (EdgewiseSubdivision.ε.map α.unop) ⋙
        rowChainComparison E m.unop =
      G ⋙ rowChainComparison E n.unop ⋙
        chainCoreReindex (QConstruction E.deflation E.inflation) α.unop
    rw [rowChainComparison_reindex]

end CategoryTheory.Waldhausen.QuillenComparison
