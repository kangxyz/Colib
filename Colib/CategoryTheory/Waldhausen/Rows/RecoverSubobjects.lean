/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.InitialFlagIso
public import Colib.CategoryTheory.Waldhausen.Rows.QConstruction
public import Colib.CategoryTheory.ExactCategory.QSpanLifting


/-! # Recovering both initial subobjects from a Q-arrow to the whole row

The apex recovers the upper endpoint subobject. Its actual kernel recovers
the lower endpoint subobject. Thus a Q-naturality square encodes both parts
of the initial flag, rather than forgetting the kernel of its deflation.
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

/-- Regard a containment-ordered interval as an ordinary arrow interval. -/
def nestedToInterval (p : NestedInterval n) : Interval n := interval p.left p.right p.endpoints

/-- The admissible span from an interval quotient to the whole initial object. -/
def wholeSpan (F : Obj (ofExactCategory E) n) (p : NestedInterval n) :
    Span E.deflation E.inflation (F.obj.obj (nestedToInterval p))
      ((initialFlag E F).obj (Fin.last n.len)) where
  apex := (initialFlag E F).obj p.right
  l := initialQuotient (ofExactCategory E) F (nestedToInterval p)
  r := (initialFlag E F).map (homOfLE (Fin.le_last p.right))
  wl := row_deflation E F 0 p.left p.right (Fin.zero_le _) p.endpoints
  wr := F.property.cofibration 0 p.right (Fin.last n.len) (Fin.zero_le _) (Fin.le_last _)

/-- The left initial subobject is the actual kernel of the interval quotient. -/
def initialKernel (F : Obj (ofExactCategory E) n) (p : NestedInterval n) :
    IsLimit (KernelFork.ofι ((initialFlag E F).map (homOfLE p.endpoints))
      (show (initialFlag E F).map (homOfLE p.endpoints) ≫
          initialQuotient (ofExactCategory E) F (nestedToInterval p) = 0 from
        rowMap_zero E F 0 p.left p.right (Fin.zero_le _) p.endpoints)) :=
  E.kernel _ (row_conflation E F 0 p.left p.right (Fin.zero_le _) p.endpoints)

/-- An endpoint-preserving apex isomorphism also identifies the lower
initial subobject, by the kernel universal property. -/
def lowerSubobjectIso {F G : Obj (ofExactCategory E) n} (p : NestedInterval n)
    (a : F.obj.obj (nestedToInterval p) ≅ G.obj.obj (nestedToInterval p))
    (c : (initialFlag E F).obj p.right ≅ (initialFlag E G).obj p.right)
    (h : initialQuotient (ofExactCategory E) F (nestedToInterval p) ≫ a.hom =
      c.hom ≫ initialQuotient (ofExactCategory E) G (nestedToInterval p)) :
    (initialFlag E F).obj p.left ≅ (initialFlag E G).obj p.left :=
  KernelFork.mapIsoOfIsLimit (initialKernel E F p) (initialKernel E G p)
    (Arrow.isoMk c a h.symm)

@[reassoc (attr := simp)]
theorem lowerSubobjectIso_inclusion {F G : Obj (ofExactCategory E) n} (p : NestedInterval n)
    (a : F.obj.obj (nestedToInterval p) ≅ G.obj.obj (nestedToInterval p))
    (c : (initialFlag E F).obj p.right ≅ (initialFlag E G).obj p.right)
    (h : initialQuotient (ofExactCategory E) F (nestedToInterval p) ≫ a.hom =
      c.hom ≫ initialQuotient (ofExactCategory E) G (nestedToInterval p)) :
    (lowerSubobjectIso E p a c h).hom ≫ (initialFlag E G).map (homOfLE p.endpoints) =
      (initialFlag E F).map (homOfLE p.endpoints) ≫ c.hom :=
by
  dsimp only [lowerSubobjectIso, KernelFork.mapIsoOfIsLimit, KernelFork.mapOfIsLimit]
  exact (initialKernel E G p).fac _ WalkingParallelPair.zero

/-- A commuting Q-square to the whole object recovers compatible isomorphisms
of both endpoint subobjects of the original initial flag. -/
theorem recover_initial_subobjects {F G : Obj (ofExactCategory E) n} (p : NestedInterval n)
    (a : F.obj.obj (nestedToInterval p) ≅ G.obj.obj (nestedToInterval p))
    (b : (initialFlag E F).obj (Fin.last n.len) ≅ (initialFlag E G).obj (Fin.last n.len))
    (h : QConstruction.mkHom E.deflation E.inflation (wholeSpan E F p) ≫ (E.qIsoOfIso b).hom =
      (E.qIsoOfIso a).hom ≫ QConstruction.mkHom E.deflation E.inflation (wholeSpan E G p)) :
    (∃ c : (initialFlag E F).obj p.right ≅ (initialFlag E G).obj p.right,
      (initialFlag E F).map (homOfLE (Fin.le_last p.right)) ≫ b.hom =
        c.hom ≫ (initialFlag E G).map (homOfLE (Fin.le_last p.right))) ∧
    (∃ c : (initialFlag E F).obj p.left ≅ (initialFlag E G).obj p.left,
      (initialFlag E F).map (homOfLE (Fin.le_last p.left)) ≫ b.hom =
        c.hom ≫ (initialFlag E G).map (homOfLE (Fin.le_last p.left))) := by
  obtain ⟨c, hl, hr⟩ := E.exists_apexIso_of_q_naturality (wholeSpan E F p) (wholeSpan E G p) a b h
  dsimp only [wholeSpan] at c hl hr
  refine ⟨⟨c, hr⟩, ⟨lowerSubobjectIso E p a c hl, ?_⟩⟩
  calc
    _ = (initialFlag E F).map (homOfLE p.endpoints) ≫
        (initialFlag E F).map (homOfLE (Fin.le_last p.right)) ≫ b.hom := by
      rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
      rfl
    _ = (initialFlag E F).map (homOfLE p.endpoints) ≫
        c.hom ≫ (initialFlag E G).map (homOfLE (Fin.le_last p.right)) := by rw [hr]
    _ = (lowerSubobjectIso E p a c hl).hom ≫
        (initialFlag E G).map (homOfLE p.endpoints) ≫
        (initialFlag E G).map (homOfLE (Fin.le_last p.right)) := by
      rw [← Category.assoc, ← lowerSubobjectIso_inclusion, Category.assoc]
    _ = _ := by rw [← CategoryTheory.Functor.map_comp]; rfl

end CategoryTheory.Waldhausen.QuotientRows
