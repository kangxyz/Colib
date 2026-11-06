/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.ZeroAugmentation
public import Colib.CategoryTheory.Waldhausen.Fibration.RelativeRows.FiltrationWeakMaps
public import Colib.CategoryTheory.Waldhausen.Rows.Completion

/-! # Genuine relative-row completion of coarse-weak cofibration chains

Adjoin the actual chosen zero and apply the existing exact cofiber functor
on actual interval arrows. Original coarse weakness proves tail acyclicity
by genuine gluing; no extension or saturation axiom is needed in this
completion direction. The original initial filtration is recovered through
its actual quotient maps, which are isomorphisms because their source is zero.


Implementation provenance:
`Quillen/Waldhausen/Fibration/RelativeRows/Completion.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RelativeRows
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- The original fine cofiber of a coarse-weak cofibration is genuinely coarse-acyclic. -/
theorem cofiber_acyclic_of_coarseWeak (X : ExtensionCategory.Obj V) (hw : N.coarse.weq X.obj.hom) :
    Acyclic N.coarse ((ExtensionCategory.cofiber V).obj X) := by
  have hp : IsPushout X.obj.hom (N.coarse.isZero.from_ X.obj.left)
      ((ExtensionCategory.quotient V).app X)
      (N.coarse.isZero.to_ ((ExtensionCategory.cofiber V).obj X)) := by
    apply (ExtensionCategory.cofiber_isPushout V X).of_iso (Iso.refl _) (Iso.refl _)
      (V.isZero.iso N.coarse.isZero) (Iso.refl _)
    · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl
    · exact N.coarse.isZero.eq_of_tgt _ _
    · simp
    · exact V.isZero.eq_of_src _ _
  exact acyclic_of_weak_of_isPushout N.coarse (by rw [N.cof_eq]; exact X.property) hp hw

variable {n : SimplexCategory} (F : ComposableArrows C n.len)
  (hF : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), V.cof (F.map f))

/-- Complete the actual zero-augmented flag using the existing cofiber construction. -/
def relativeCompletionUnderlying : QuotientRows.Obj V (addInitial.obj n) :=
  QuotientRows.completeCofibrationFlag V (zeroAugment V F) (zeroAugment_map_cof V F hF)

/-- Original coarse weakness, not an assumed quotient predicate, supplies tail acyclicity. -/
theorem relativeCompletionUnderlying_mem
    (hw : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), N.coarse.weq (F.map f)) :
    objects N n (relativeCompletionUnderlying F hF) := by
  intro p
  exact cofiber_acyclic_of_coarseWeak N
    ((QuotientRows.cofibrationArrowDiagram V (zeroAugment V F) (zeroAugment_map_cof V F hF)).obj
      ((QuotientRows.indexMap (tail.app n)).obj p)) (hw (homOfLE p.property))

variable (hw : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), N.coarse.weq (F.map f))

/-- The actual relative row reconstructed from its original coarse-weak cofibration chain. -/
def relativeCompletion : Obj N n :=
  ⟨relativeCompletionUnderlying F hF, relativeCompletionUnderlying_mem N F hF hw⟩

/-- The original quotient-by-zero maps compare the original chain to its completed initial chain. -/
def relativeCompletionUnit : F ⟶ (initialFiltrationFunctor N n).obj (relativeCompletion N F hF
    hw) where
  app i := QuotientRows.completionQuotient V (zeroAugment V F) (zeroAugment_map_cof V F hF)
    (interval 0 i.succ (Fin.zero_le _))
  naturality _i _j f :=
    (QuotientRows.completionQuotient_comp_map V (zeroAugment V F)
      (zeroAugment_map_cof V F hF) ((initialFiltrationIndex n).map f)).symm

/-- Each original quotient-by-zero projection is an actual isomorphism. -/
theorem relativeCompletionUnit_app_isIso (i : Fin (n.len + 1)) :
    IsIso ((relativeCompletionUnit N F hF hw).app i) := by
  let hzero : IsIso (V.isZero.from_
      ((zeroAugment V F).obj (interval 0 i.succ (Fin.zero_le _)).val.1)) := by
    change IsIso (V.isZero.from_ V.zero)
    exact V.isZero.isIso V.isZero _
  exact (QuotientRows.completionQuotient_isPushout V (zeroAugment V F)
    (zeroAugment_map_cof V F hF) (interval 0 i.succ (Fin.zero_le _))).isIso_inl_of_isIso

/-- The actual original initial filtration is recovered by its genuine quotient isomorphisms. -/
def relativeCompletionInitialIso : F ≅
    (initialFiltrationFunctor N n).obj (relativeCompletion N F hF hw) := by
  letI completionUnitIso (i : Fin (n.len + 1)) : IsIso ((relativeCompletionUnit N F hF hw).app i) :=
    relativeCompletionUnit_app_isIso N F hF hw i
  exact NatIso.ofComponents (fun i ↦ asIso ((relativeCompletionUnit N F hF hw).app i))
    (fun f ↦ (relativeCompletionUnit N F hF hw).naturality f)

/-- Its forward map remains the original categorical cofiber projection. -/
@[simp] theorem relativeCompletionInitialIso_hom_app (i : Fin (n.len + 1)) :
    (relativeCompletionInitialIso N F hF hw).hom.app i =
      QuotientRows.completionQuotient V (zeroAugment V F) (zeroAugment_map_cof V F hF)
        (interval 0 i.succ (Fin.zero_le _)) := rfl

include hF hw in
/-- Every genuine coarse-weak cofibration chain lies in the essential image of the original
functor. -/
theorem initialFiltration_exists_of_cof_weak :
    ∃ R : Obj N n, Nonempty (F ≅ (initialFiltrationFunctor N n).obj R) :=
  ⟨relativeCompletion N F hF hw, ⟨relativeCompletionInitialIso N F hF hw⟩⟩

variable {F} {G : ComposableArrows C n.len}
  (hG : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), V.cof (G.map f))
  (hwG : ∀ {i j : Fin (n.len + 1)} (f : i ⟶ j), N.coarse.weq (G.map f))

/-- Every original chain transformation has its actual zero-augmented cofiber completion map. -/
def relativeCompletionMap (α : F ⟶ G) :
    relativeCompletion N F hF hw ⟶ relativeCompletion N G hG hwG :=
  (objects N n).homMk (QuotientRows.completeCofibrationFlagMap V
    (zeroAugment_map_cof V F hF) (zeroAugment_map_cof V G hG) (zeroAugmentNatTrans V α))

/-- Completion preserves original pointwise fine weak maps by actual cofiber exactness. -/
theorem relativeCompletionMap_weak (α : F ⟶ G) (hα : ∀ i, V.weq (α.app i)) :
    (waldhausenStructure N n).weq (relativeCompletionMap N hF hw hG hwG α) :=
  QuotientRows.completeCofibrationFlagMap_weak V (zeroAugment_map_cof V F hF)
    (zeroAugment_map_cof V G hG) (zeroAugmentNatTrans V α) (zeroAugmentNatTrans_weak V α hα)

/-- The actual initial-chain isomorphisms are natural for every original chain transformation. -/
theorem relativeCompletionUnit_naturality (α : F ⟶ G) :
    α ≫ relativeCompletionUnit N G hG hwG = relativeCompletionUnit N F hF hw ≫
      (initialFiltrationFunctor N n).map (relativeCompletionMap N hF hw hG hwG α) := by
  ext i
  exact (ExtensionCategory.quotient V).naturality
    ((QuotientRows.cofibrationArrowNatTrans V (zeroAugment_map_cof V F hF)
      (zeroAugment_map_cof V G hG) (zeroAugmentNatTrans V α)).app
      (interval 0 i.succ (Fin.zero_le _)))

end CategoryTheory.Waldhausen.Fibration.RelativeRows
