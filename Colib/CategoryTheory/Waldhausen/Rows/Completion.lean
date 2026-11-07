/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Rows.Basic
public import Colib.CategoryTheory.Waldhausen.Rows.ReedyCofibrations
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.Cofiber
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.IsomorphicSources

/-! # Actual cofiber completion of a cofibration flag

The original interval-arrow diagram takes values in the genuine extension
category. Horizontal arrows are Reedy cofibrations because their source maps
are identities; its quotient squares are actual componentwise pushouts.
Applying the already-proved exact cofiber functor constructs a genuine
quotient row, without exact-category or abelian hypotheses.


Implementation provenance:
`Quillen/Waldhausen/SConstruction/Rows/Completion.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)
variable {n : SimplexCategory} (F : Fin (n.len + 1) ⥤ C)
  (hF : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), W.cof (F.map f))

/-- Every original flag interval, retained as an actual cofibration arrow. -/
def cofibrationArrowDiagram : Interval n ⥤ ExtensionCategory.Obj W where
  obj p := ⟨Arrow.mk (F.map (homOfLE p.property)), hF _⟩
  map {p q} f := (ExtensionCategory.objects W).homMk (Arrow.homMk
    (F.map (homOfLE (leOfHom f).1)) (F.map (homOfLE (leOfHom f).2))
    (by
      change F.map (homOfLE (leOfHom f).1) ≫ F.map (homOfLE q.property) =
        F.map (homOfLE p.property) ≫ F.map (homOfLE (leOfHom f).2)
      rw [← F.map_comp, ← F.map_comp]
      congr 1))
  map_id p := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> exact F.map_id _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> exact F.map_comp _ _

/-- Each horizontal interval map satisfies the genuine Reedy cofibration condition. -/
theorem cofibrationArrowDiagram_horizontal_cof
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    ExtensionCategory.cof W ((cofibrationArrowDiagram W F hF).map
      (homOfLE (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl,hjk⟩))) := by
  let f := (cofibrationArrowDiagram W F hF).map
    (homOfLE (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl,hjk⟩))
  have hf : IsIso f.hom.left := by
    change IsIso (F.map (𝟙 i))
    infer_instance
  exact @ExtensionCategory.cof_of_left_isIso _ _ W _ _ f hf (hF (homOfLE hjk))

/-- The interval-arrow quotient square is a genuine pushout in the extension category. -/
theorem cofibrationArrowDiagram_quotient
    (i j k : Fin (n.len + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    IsPushout
      ((cofibrationArrowDiagram W F hF).map
        (homOfLE (show interval i j hij ≤ interval i k (hij.trans hjk) from ⟨le_rfl,hjk⟩)))
      ((cofibrationArrowDiagram W F hF).map
        (homOfLE (show interval i j hij ≤ interval j j le_rfl from ⟨hij,le_rfl⟩)))
      ((cofibrationArrowDiagram W F hF).map
        (homOfLE (show interval i k (hij.trans hjk) ≤ interval j k hjk from ⟨hij,le_rfl⟩)))
      ((cofibrationArrowDiagram W F hF).map
        (homOfLE (show interval j j le_rfl ≤ interval j k hjk from ⟨le_rfl,hjk⟩))) := by
  apply IsPushout.of_map_of_faithful (ExtensionCategory.forget W)
  apply ExtensionCategory.arrow_isPushout
  · change IsPushout (F.map (𝟙 i)) (F.map (homOfLE hij))
      (F.map (homOfLE hij)) (F.map (𝟙 j))
    simp only [F.map_id]
    exact IsPushout.of_id_fst
  · change IsPushout (F.map (homOfLE hjk)) (F.map (𝟙 j))
      (F.map (𝟙 k)) (F.map (homOfLE hjk))
    simp only [F.map_id]
    exact IsPushout.of_id_snd

/-- The actual existing cofiber of each original flag inclusion. -/
def cofiberCompletion : Interval n ⥤ C :=
  cofibrationArrowDiagram W F hF ⋙ ExtensionCategory.cofiber W

/-- Diagonal cofibers are genuinely zero, since their original arrows are identities. -/
theorem cofiberCompletion_zero (i : Fin (n.len + 1)) :
    IsZero ((cofiberCompletion W F hF).obj (interval i i le_rfl)) := by
  let X := (cofibrationArrowDiagram W F hF).obj (interval i i le_rfl)
  let hi : IsIso ((ExtensionCategory.inclusion W).app X) := by
    change IsIso (F.map (𝟙 i))
    infer_instance
  let hq : IsIso (W.isZero.to_ ((ExtensionCategory.cofiber W).obj X)) :=
    (ExtensionCategory.cofiber_isPushout W X).isIso_inr_of_isIso
  exact W.isZero.of_iso (asIso (W.isZero.to_ ((ExtensionCategory.cofiber W).obj X))).symm

/-- Exactness of the genuine cofiber functor gives every actual row axiom. -/
theorem cofiberCompletion_isRow : IsRow W (cofiberCompletion W F hF) where
  zero := cofiberCompletion_zero W F hF
  cofibration i j k hij hjk := (ExtensionCategory.cofiber_exact W).cofibration _
    (cofibrationArrowDiagram_horizontal_cof W F hF i j k hij hjk)
  quotient i j k hij hjk := (ExtensionCategory.cofiber_exact W).pushout
    (cofibrationArrowDiagram_horizontal_cof W F hF i j k hij hjk)
    (cofibrationArrowDiagram_quotient W F hF i j k hij hjk)

/-- Complete an actual cofibration flag by the existing actual cofiber functor. -/
def completeCofibrationFlag : Obj W n :=
  ⟨cofiberCompletion W F hF, cofiberCompletion_isRow W F hF⟩

/-- The actual original quotient projection at a completed interval. -/
def completionQuotient (p : Interval n) : F.obj p.val.2 ⟶ (completeCofibrationFlag W F
    hF).obj.obj p :=
  (ExtensionCategory.quotient W).app ((cofibrationArrowDiagram W F hF).obj p)

/-- Each completed interval retains the original displayed cofiber square. -/
theorem completionQuotient_isPushout (p : Interval n) :
    IsPushout (F.map (homOfLE p.property)) (W.isZero.from_ (F.obj p.val.1))
      (completionQuotient W F hF p) (W.isZero.to_ ((completeCofibrationFlag W F hF).obj.obj p)) :=
  ExtensionCategory.cofiber_isPushout W ((cofibrationArrowDiagram W F hF).obj p)

/-- Naturality simplifies from the displayed quotient followed by a row map. -/
@[reassoc (attr := simp)] theorem completionQuotient_comp_map {p q : Interval n} (f : p ⟶ q) :
    completionQuotient W F hF p ≫ (cofiberCompletion W F hF).map f =
      F.map (homOfLE (leOfHom f).2) ≫ completionQuotient W F hF q :=
          ((ExtensionCategory.quotient W).naturality ((cofibrationArrowDiagram W F hF).map f)).symm


variable {F} {G : Fin (n.len + 1) ⥤ C}
  (hG : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), W.cof (G.map f))

/-- Every original flag transformation induces its original square at every interval. -/
def cofibrationArrowNatTrans (α : F ⟶ G) :
    cofibrationArrowDiagram W F hF ⟶ cofibrationArrowDiagram W G hG where
  app p := (ExtensionCategory.objects W).homMk (Arrow.homMk (α.app p.val.1) (α.app p.val.2)
    (α.naturality (homOfLE p.property)).symm)
  naturality p q f := by
    apply ObjectProperty.hom_ext
    apply Arrow.hom_ext <;> exact α.naturality _

/-- Completion retains all natural transformations, not only isomorphisms. -/
def completeCofibrationFlagMap (α : F ⟶ G) :
    completeCofibrationFlag W F hF ⟶ completeCofibrationFlag W G hG :=
  (objects W n).homMk (Functor.whiskerRight (cofibrationArrowNatTrans W hF hG α)
    (ExtensionCategory.cofiber W))

/-- The completed map is literally the original cofiber-functor map of the interval square. -/
@[simp] theorem completeCofibrationFlagMap_app (α : F ⟶ G) (p : Interval n) :
    (completeCofibrationFlagMap W hF hG α).hom.app p =
      (ExtensionCategory.cofiber W).map ((cofibrationArrowNatTrans W hF hG α).app p) := rfl

/-- Pointwise original fine weak maps remain fine weak on all actual interval quotients. -/
theorem completeCofibrationFlagMap_weak (α : F ⟶ G) (hα : ∀ i, W.weq (α.app i)) :
    weq W n (completeCofibrationFlagMap W hF hG α) := by
  intro p
  exact (ExtensionCategory.cofiber_exact W).weak _ ⟨hα p.val.1, hα p.val.2⟩


/-- Completion retains identities on the original chain diagrams. -/
@[simp] theorem completeCofibrationFlagMap_id :
    completeCofibrationFlagMap W hF hF (𝟙 F) = 𝟙 (completeCofibrationFlag W F hF) := by
  apply ObjectProperty.hom_ext
  ext p
  change (ExtensionCategory.cofiber W).map (𝟙 ((cofibrationArrowDiagram W F hF).obj p)) = _
  exact (ExtensionCategory.cofiber W).map_id _

/-- Completion retains composition of arbitrary original chain transformations. -/
@[simp] theorem completeCofibrationFlagMap_comp {H : Fin (n.len + 1) ⥤ C}
    (hH : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), W.cof (H.map f))
    (α : F ⟶ G) (β : G ⟶ H) :
    completeCofibrationFlagMap W hF hH (α ≫ β) =
      completeCofibrationFlagMap W hF hG α ≫ completeCofibrationFlagMap W hG hH β := by
  apply ObjectProperty.hom_ext
  ext p
  exact (ExtensionCategory.cofiber W).map_comp
    ((cofibrationArrowNatTrans W hF hG α).app p) ((cofibrationArrowNatTrans W hG hH β).app p)

end CategoryTheory.Waldhausen.QuotientRows
