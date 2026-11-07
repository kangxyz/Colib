/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Exact
public import Colib.CategoryTheory.Waldhausen.Rows.InitialIntervals


/-! # Recovering quotient-row isomorphisms from initial flags

Every interval quotient is the actual cokernel of the corresponding map in
the initial flag. Thus a natural isomorphism of initial flags extends to the
whole quotient row, uniquely by cokernel descent.
-/
/- Adapted from the corresponding Quillen Q/S reconstruction source at
   c561118b7795eb9780be9ed391c3251d6a4d0afd. Native Colib objects are retained. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial
universe v u

namespace CategoryTheory.Waldhausen.QuotientRows

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
variable (E : CategoryTheory.ExactCategory.ExactStructure C)
variable {n : SimplexCategory}

/-- The initial flag underlying an exact quotient row. -/
def initialFlag (F : Obj (ofExactCategory E) n) : Fin (n.len + 1) ⥤ C := initialIntervals n ⋙ F.obj

/-- Every interval of the row is a specified cokernel of an initial-flag arrow. -/
def initialCofork (F : Obj (ofExactCategory E) n) (p : Interval n) :
    CokernelCofork ((initialFlag E F).map (homOfLE p.2)) :=
  CokernelCofork.ofπ (initialQuotient (ofExactCategory E) F p) (rowMap_zero E F 0 p.1.1 p.1.2
    (Fin.zero_le _) p.2)

/-- Its universal property is a proved consequence of the original S-pushout. -/
def initialCokernel (F : Obj (ofExactCategory E) n) (p : Interval n) : IsColimit (initialCofork E F
  p) :=
  E.cokernel _ (row_conflation E F 0 p.1.1 p.1.2 (Fin.zero_le _) p.2)

/-- An initial-flag isomorphism induces an isomorphism at every quotient interval. -/
def flagIsoAt {F G : Obj (ofExactCategory E) n} (e : initialFlag E F ≅ initialFlag E G) (p :
  Interval n) :
    F.obj.obj p ≅ G.obj.obj p :=
  CokernelCofork.mapIsoOfIsColimit (initialCokernel E F p) (initialCokernel E G p)
    (Arrow.isoMk (e.app p.1.1) (e.app p.1.2) (e.hom.naturality (homOfLE p.2)).symm)

@[reassoc (attr := simp)]
theorem initialQuotient_flagIsoAt {F G : Obj (ofExactCategory E) n}
    (e : initialFlag E F ≅ initialFlag E G) (p : Interval n) :
    initialQuotient (ofExactCategory E) F p ≫ (flagIsoAt E e p).hom =
      e.hom.app p.1.2 ≫ initialQuotient (ofExactCategory E) G p :=
by
  dsimp only [flagIsoAt, CokernelCofork.mapIsoOfIsColimit, CokernelCofork.mapOfIsColimit]
  exact (initialCokernel E F p).fac _ WalkingParallelPair.one

/-- Quotient descent commutes with every map of intervals. -/
theorem flagIsoAt_naturality {F G : Obj (ofExactCategory E) n}
    (e : initialFlag E F ≅ initialFlag E G) {p q : Interval n} (f : p ⟶ q) :
    F.obj.map f ≫ (flagIsoAt E e q).hom = (flagIsoAt E e p).hom ≫ G.obj.map f := by
  let : Epi (initialQuotient (ofExactCategory E) F p) :=
    Cofork.IsColimit.epi (initialCokernel E F p)
  apply (cancel_epi (initialQuotient (ofExactCategory E) F p)).1
  have hF : initialQuotient (ofExactCategory E) F p ≫ F.obj.map f =
      (initialFlag E F).map (homOfLE (leOfHom f).2) ≫ initialQuotient (ofExactCategory E) F q := by
    simp only [initialQuotient, initialFlag, CategoryTheory.Functor.comp_map, ← F.obj.map_comp]
    congr 1
  have hG : initialQuotient (ofExactCategory E) G p ≫ G.obj.map f =
      (initialFlag E G).map (homOfLE (leOfHom f).2) ≫ initialQuotient (ofExactCategory E) G q := by
    simp only [initialQuotient, initialFlag, CategoryTheory.Functor.comp_map, ← G.obj.map_comp]
    congr 1
  calc
    _ = (initialFlag E F).map (homOfLE (leOfHom f).2) ≫
        initialQuotient (ofExactCategory E) F q ≫ (flagIsoAt E e q).hom := by
          rw [← Category.assoc, hF, Category.assoc]
    _ = (initialFlag E F).map (homOfLE (leOfHom f).2) ≫
        e.hom.app q.1.2 ≫ initialQuotient (ofExactCategory E) G q := by
          rw [initialQuotient_flagIsoAt]
    _ = e.hom.app p.1.2 ≫ (initialFlag E G).map (homOfLE (leOfHom f).2) ≫
        initialQuotient (ofExactCategory E) G q := by
          rw [← Category.assoc, e.hom.naturality, Category.assoc]
    _ = e.hom.app p.1.2 ≫ initialQuotient (ofExactCategory E) G p ≫ G.obj.map f := by rw [hG]
    _ = _ := by rw [← Category.assoc, ← initialQuotient_flagIsoAt, Category.assoc]

/-- The unique extension of an isomorphism of initial flags to all quotients. -/
def extendFlagIso {F G : Obj (ofExactCategory E) n} (e : initialFlag E F ≅ initialFlag E G) : F.obj
  ≅ G.obj :=
  NatIso.ofComponents (flagIsoAt E e) (fun f ↦ flagIsoAt_naturality E e f)

end CategoryTheory.Waldhausen.QuotientRows
