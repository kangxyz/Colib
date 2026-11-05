/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.Category.TopCat.SequentialColimit.Deformation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Sequential cobase change along a colimit cocone

Push each stage of a map of sequential diagrams out along the source
colimit cocone. The resulting diagram has the same colimit as the target.
Its successor maps are cobase changes of the relative latching maps.
-/
/-! Implementation provenance: adapted from
`Quillen/CategoryTheory/TheoremA/SequentialCylinderReduction.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, prescribed forward
comparisons, deformation homotopies, hypotheses and universes are retained.
Only namespace/import ownership and unnecessary broad imports change.
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits
open scoped Topology unitInterval

universe u
set_option backward.isDefEq.respectTransparency false

namespace TopCat

/-- Push every stage out along the actual source colimit cocone. -/
def sequentialCobaseDiagram {F G : ℕ ⥤ TopCat.{u}}
    (c : Cocone F) (η : F ⟶ G) : ℕ ⥤ TopCat.{u} := pushout c.ι η

/-- The natural map from the constant diagram at the cocone point to the stagewise pushout of the
source cocone along `η`. -/
def sequentialCobaseSource {F G : ℕ ⥤ TopCat.{u}}
    (c : Cocone F) (η : F ⟶ G) :
    (Functor.const ℕ).obj c.pt ⟶ sequentialCobaseDiagram c η := pushout.inl _ _

/-- The natural map from `G` to the stagewise pushout of the source cocone along `η`. -/
def sequentialCobaseTarget {F G : ℕ ⥤ TopCat.{u}}
    (c : Cocone F) (η : F ⟶ G) :
    G ⟶ sequentialCobaseDiagram c η := pushout.inr _ _

/-- The stage squares are genuine topological pushouts. -/
theorem sequentialCobaseSquare {F G : ℕ ⥤ TopCat.{u}}
    (c : Cocone F) (η : F ⟶ G) (n : ℕ) :
    IsPushout (c.ι.app n) (η.app n)
      ((sequentialCobaseSource c η).app n) ((sequentialCobaseTarget c η).app n) :=
  (IsPushout.of_hasPushout c.ι η).map ((evaluation ℕ TopCat).obj n)

/-- The cocone from the cobase-changed sequence to the target colimit. -/
def sequentialCobaseCocone {F G : ℕ ⥤ TopCat.{u}}
    (c : Cocone F) (hc : IsColimit c) (η : F ⟶ G) (d : Cocone G) :
    Cocone (sequentialCobaseDiagram c η) where
  pt := d.pt
  ι := pushout.desc ((Functor.const ℕ).map (hc.map d η)) d.ι (by
    apply NatTrans.ext
    funext n
    exact hc.ι_map d η n)

@[reassoc (attr := simp)]
theorem sequentialCobaseCocone_source {F G : ℕ ⥤ TopCat.{u}}
    (c : Cocone F) (hc : IsColimit c) (η : F ⟶ G) (d : Cocone G) (n : ℕ) :
    (sequentialCobaseSource c η).app n ≫ (sequentialCobaseCocone c hc η d).ι.app n =
      hc.map d η := by
  exact NatTrans.congr_app (pushout.inl_desc _ _ _) n

@[reassoc (attr := simp)]
theorem sequentialCobaseCocone_target {F G : ℕ ⥤ TopCat.{u}}
    (c : Cocone F) (hc : IsColimit c) (η : F ⟶ G) (d : Cocone G) (n : ℕ) :
    (sequentialCobaseTarget c η).app n ≫ (sequentialCobaseCocone c hc η d).ι.app n =
      d.ι.app n := by
  exact NatTrans.congr_app (pushout.inr_desc _ _ _) n

/-- The fixed source has the same image through each component of any cocone. -/
theorem sequentialCobaseSource_constant {F G : ℕ ⥤ TopCat.{u}}
    (c : Cocone F) (η : F ⟶ G) (t : Cocone (sequentialCobaseDiagram c η)) (n : ℕ) :
    (sequentialCobaseSource c η).app n ≫ t.ι.app n =
      (sequentialCobaseSource c η).app 0 ≫ t.ι.app 0 := by
  have h := (sequentialCobaseSource c η).naturality (homOfLE (Nat.zero_le n))
  change 𝟙 c.pt ≫ _ = _ at h
  rw [Category.id_comp] at h
  rw [h, Category.assoc, t.w]

/-- Cobase changing a diagram along its own colimit cocone preserves the
target colimit. The proof uses both universal properties, without any
injectivity or compactness assumption. -/
def sequentialCobaseIsColimit {F G : ℕ ⥤ TopCat.{u}}
    (c : Cocone F) (hc : IsColimit c) (η : F ⟶ G)
    (d : Cocone G) (hd : IsColimit d) :
    IsColimit (sequentialCobaseCocone c hc η d) := by
  let target (t : Cocone (sequentialCobaseDiagram c η)) : Cocone G :=
    ⟨t.pt, sequentialCobaseTarget c η ≫ t.ι⟩
  refine {
    desc := fun t ↦ hd.desc (target t)
    fac := ?_
    uniq := ?_ }
  · intro t n
    apply (sequentialCobaseSquare c η n).hom_ext
    · rw [← Category.assoc, sequentialCobaseCocone_source]
      apply hc.hom_ext
      intro m
      rw [← Category.assoc, hc.ι_map, Category.assoc, hd.fac]
      change η.app m ≫ (sequentialCobaseTarget c η).app m ≫ t.ι.app m = _
      rw [← Category.assoc, ← (sequentialCobaseSquare c η m).w, Category.assoc,
        sequentialCobaseSource_constant c η t m]
      rw [sequentialCobaseSource_constant c η t n]
    · rw [← Category.assoc, sequentialCobaseCocone_target, hd.fac]
      rfl
  · intro t m hm
    apply hd.hom_ext
    intro n
    rw [← sequentialCobaseCocone_target c hc η d n, Category.assoc, hm]
    rw [sequentialCobaseCocone_target]
    exact (hd.fac (target t) n).symm

/-- A successor of the cobase-changed sequence is a cobase change of its
relative latching map. This assertion only needs the displayed pushout
presentation of that latching object. -/
theorem sequentialCobaseStepSquare {F G : ℕ ⥤ TopCat.{u}}
    (c : Cocone F) (η : F ⟶ G) (n : ℕ)
    {L : TopCat.{u}} {x : F.obj (n + 1) ⟶ L} {y : G.obj n ⟶ L}
    {l : L ⟶ G.obj (n + 1)}
    (sq : IsPushout (F.map (homOfLE (Nat.le_succ n))) (η.app n) x y)
    (hx : x ≫ l = η.app (n + 1))
    (hy : y ≫ l = G.map (homOfLE (Nat.le_succ n))) :
    ∃ k : L ⟶ (sequentialCobaseDiagram c η).obj n,
      IsPushout l k ((sequentialCobaseTarget c η).app (n + 1))
        ((sequentialCobaseDiagram c η).map (homOfLE (Nat.le_succ n))) := by
  let a := homOfLE (Nat.le_succ n)
  let P := sequentialCobaseDiagram c η
  let s := sequentialCobaseSource c η
  let t := sequentialCobaseTarget c η
  have hw : F.map a ≫ c.ι.app (n + 1) ≫ s.app n = η.app n ≫ t.app n := by
    rw [← Category.assoc, c.w]
    exact (sequentialCobaseSquare c η n).w
  let k : L ⟶ P.obj n := sq.desc (c.ι.app (n + 1) ≫ s.app n) (t.app n) hw
  have hxk : x ≫ k = c.ι.app (n + 1) ≫ s.app n := sq.inl_desc _ _ _
  have hyk : y ≫ k = t.app n := sq.inr_desc _ _ _
  have sqk : IsPushout x (c.ι.app (n + 1)) k (s.app n) := by
    apply IsPushout.of_top _ hxk sq.flip
    rw [c.w, hyk]
    exact (sequentialCobaseSquare c η n).flip
  have hs : s.app n ≫ P.map a = s.app (n + 1) := by
    have h := s.naturality a
    change 𝟙 c.pt ≫ s.app (n + 1) = s.app n ≫ P.map a at h
    simpa using h.symm
  have hcomm : l ≫ t.app (n + 1) = k ≫ P.map a := by
    apply sq.hom_ext
    · rw [← Category.assoc, hx, ← (sequentialCobaseSquare c η (n + 1)).w,
        ← Category.assoc x k, hxk, Category.assoc, hs]
    · rw [← Category.assoc, hy, t.naturality, ← Category.assoc y k, hyk]
  refine ⟨k, IsPushout.of_left ?_ hcomm sqk⟩
  rw [hx, hs]
  exact (sequentialCobaseSquare c η (n + 1)).flip

/-- An acyclic-cofibration relative latching map gives an
acyclic-cofibration successor in the cobase-changed sequence. -/
theorem sequentialCobaseStep_hep_and_equiv {F G : ℕ ⥤ TopCat.{u}}
    (c : Cocone F) (η : F ⟶ G) (n : ℕ)
    {L : TopCat.{u}} {x : F.obj (n + 1) ⟶ L} {y : G.obj n ⟶ L}
    {l : L ⟶ G.obj (n + 1)}
    (sq : IsPushout (F.map (homOfLE (Nat.le_succ n))) (η.app n) x y)
    (hx : x ≫ l = η.app (n + 1))
    (hy : y ≫ l = G.map (homOfLE (Nat.le_succ n)))
    (hl : TopCat.HomotopyExtensionProperty l)
    (e : ContinuousMap.HomotopyEquiv L (G.obj (n + 1))) (he : e.toFun = l.hom) :
    TopCat.HomotopyExtensionProperty
      ((sequentialCobaseDiagram c η).map (homOfLE (Nat.le_succ n))) ∧
    ∃ E : ContinuousMap.HomotopyEquiv
      ((sequentialCobaseDiagram c η).obj n) ((sequentialCobaseDiagram c η).obj (n + 1)),
      E.toFun = ((sequentialCobaseDiagram c η).map (homOfLE (Nat.le_succ n))).hom := by
  obtain ⟨k, hk⟩ := sequentialCobaseStepSquare c η n sq hx hy
  exact ⟨TopCat.homotopyExtensionProperty_pushout hk hl,
    TopCat.pushoutHomotopyEquivOfCofibration hk hl e he, rfl⟩

/-- The relative latching object of a map of sequential diagrams. -/
def sequentialLatchingObject {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) (n : ℕ) : TopCat.{u} :=
  pushout (F.map (homOfLE (Nat.le_succ n))) (η.app n)

/-- The canonical relative latching map. -/
def sequentialLatchingMap {F G : ℕ ⥤ TopCat.{u}} (η : F ⟶ G) (n : ℕ) :
    sequentialLatchingObject η n ⟶ G.obj (n + 1) :=
  pushout.desc (η.app (n + 1)) (G.map (homOfLE (Nat.le_succ n)))
    (η.naturality (homOfLE (Nat.le_succ n)))

/-- An initial acyclic cofibration and acyclic-cofibration relative latching
maps give a genuine homotopy equivalence of sequential colimits.
The inverse and all required homotopies are constructed, rather than
assumed compatible at the colimit. -/
def sequentialColimitHomotopyEquivOfLatching {F G : ℕ ⥤ TopCat.{u}}
    (η : F ⟶ G) (c : Cocone F) (hc : IsColimit c) (d : Cocone G) (hd : IsColimit d)
    (h₀ : TopCat.HomotopyExtensionProperty (η.app 0))
    (e₀ : ContinuousMap.HomotopyEquiv (F.obj 0) (G.obj 0))
    (he₀ : e₀.toFun = (η.app 0).hom)
    (hL : ∀ n, TopCat.HomotopyExtensionProperty (sequentialLatchingMap η n))
    (eL : ∀ n, ContinuousMap.HomotopyEquiv (sequentialLatchingObject η n) (G.obj (n + 1)))
    (heL : ∀ n, (eL n).toFun = (sequentialLatchingMap η n).hom) :
    ContinuousMap.HomotopyEquiv c.pt d.pt := by
  let P := sequentialCobaseDiagram c η
  have hstep (n : ℕ) := sequentialCobaseStep_hep_and_equiv c η n
    (IsPushout.of_hasPushout (F.map (homOfLE (Nat.le_succ n))) (η.app n))
    (pushout.inl_desc (η.app (n + 1)) (G.map (homOfLE (Nat.le_succ n)))
      (η.naturality (homOfLE (Nat.le_succ n))))
    (pushout.inr_desc (η.app (n + 1)) (G.map (homOfLE (Nat.le_succ n)))
      (η.naturality (homOfLE (Nat.le_succ n))))
    (hL n) (eL n) (heL n)
  let E₀ := TopCat.pushoutHomotopyEquivOfCofibration (sequentialCobaseSquare c η 0).flip h₀ e₀ he₀
  let E₁ := sequentialHomotopyEquivOfCofibrations P
    (sequentialCobaseCocone c hc η d) (sequentialCobaseIsColimit c hc η d hd)
    (fun n ↦ (hstep n).1) (fun n ↦ (hstep n).2.choose) (fun n ↦ (hstep n).2.choose_spec)
  let E : ContinuousMap.HomotopyEquiv c.pt d.pt := E₀.trans E₁
  have hE : E.toFun = (hc.map d η).hom := by
    change ((sequentialCobaseSource c η).app 0 ≫
      (sequentialCobaseCocone c hc η d).ι.app 0).hom = _
    rw [sequentialCobaseCocone_source]
  exact { E with
    toFun := (hc.map d η).hom
    left_inv := by simpa only [hE] using E.left_inv
    right_inv := by simpa only [hE] using E.right_inv }

@[simp]
theorem sequentialColimitHomotopyEquivOfLatching_toFun {F G : ℕ ⥤ TopCat.{u}}
    (η : F ⟶ G) (c : Cocone F) (hc : IsColimit c) (d : Cocone G) (hd : IsColimit d)
    (h₀ : TopCat.HomotopyExtensionProperty (η.app 0))
    (e₀ : ContinuousMap.HomotopyEquiv (F.obj 0) (G.obj 0))
    (he₀ : e₀.toFun = (η.app 0).hom)
    (hL : ∀ n, TopCat.HomotopyExtensionProperty (sequentialLatchingMap η n))
    (eL : ∀ n, ContinuousMap.HomotopyEquiv (sequentialLatchingObject η n) (G.obj (n + 1)))
    (heL : ∀ n, (eL n).toFun = (sequentialLatchingMap η n).hom) :
    (sequentialColimitHomotopyEquivOfLatching η c hc d hd h₀ e₀ he₀ hL eL heL).toFun =
      (hc.map d η).hom := rfl

end TopCat
