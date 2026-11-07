/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.DoubleMappingCylinder.Basic
public import Colib.Topology.Pushout.HomotopyEquivalence
public import Colib.Topology.MappingCylinder.HomotopyExtension

/-!
# Homotopy invariance of actual double mapping cylinders

A strict map of spans which is an ordinary homotopy equivalence at each
of its three objects induces an ordinary homotopy equivalence of actual
double mapping cylinders. The cylinder and endpoint formulas are retained
exactly, using the homotopy extension property of the endpoint pair.
-/
/-! Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/Invariance.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining the actual maps and proofs
with native namespace and import ownership. -/
@[expose] public section


noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
open unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.DoubleCylinder

/-- The map of the disjoint endpoint spaces induced by two maps. -/
def sumMap {A B A' B' : TopCat.{u}} (a : A ⟶ A') (b : B ⟶ B') :
    TopCat.of (A ⊕ B) ⟶ TopCat.of (A' ⊕ B') :=
  TopCat.ofHom ⟨Sum.map a b, continuous_sum_dom.mpr
    ⟨continuous_inl.comp a.hom.continuous, continuous_inr.comp b.hom.continuous⟩⟩

@[simp] theorem sumMap_inl {A B A' B' : TopCat.{u}} (a : A ⟶ A') (b : B ⟶ B') (x : A) :
    sumMap a b (Sum.inl x) = Sum.inl (a x) := rfl

@[simp] theorem sumMap_inr {A B A' B' : TopCat.{u}} (a : A ⟶ A') (b : B ⟶ B') (x : B) :
    sumMap a b (Sum.inr x) = Sum.inr (b x) := rfl

/-- Homotopies on the two summands give a homotopy of their sum maps. -/
def sumMapHomotopy {A B A' B' : TopCat.{u}}
    {a₀ a₁ : A ⟶ A'} {b₀ b₁ : B ⟶ B'}
    (H : ContinuousMap.Homotopy a₀.hom a₁.hom)
    (K : ContinuousMap.Homotopy b₀.hom b₁.hom) :
    ContinuousMap.Homotopy (sumMap a₀ b₀).hom (sumMap a₁ b₁).hom where
  toFun z := Sum.elim (fun x ↦ Sum.inl (H (z.1, x)))
    (fun y ↦ Sum.inr (K (z.1, y))) z.2
  continuous_toFun := by
    convert ((continuous_inl.comp H.continuous).sumElim
      (continuous_inr.comp K.continuous)).comp Homeomorph.prodSumDistrib.continuous using 1
    ext ⟨t, x⟩
    cases x <;> rfl
  map_zero_left x := by cases x <;> simp [sumMap]
  map_one_left x := by cases x <;> simp [sumMap]

/-- The coproduct of two ordinary homotopy equivalences. -/
def sumHomotopyEquiv {A B A' B' : TopCat.{u}}
    (ea : ContinuousMap.HomotopyEquiv A A')
    (eb : ContinuousMap.HomotopyEquiv B B') :
    ContinuousMap.HomotopyEquiv (A ⊕ B) (A' ⊕ B') where
  toFun := (sumMap (TopCat.ofHom ea.toFun) (TopCat.ofHom eb.toFun)).hom
  invFun := (sumMap (TopCat.ofHom ea.invFun) (TopCat.ofHom eb.invFun)).hom
  left_inv := ⟨(sumMapHomotopy ea.left_inv.some eb.left_inv.some).cast
    (by ext x; cases x <;> rfl) (by ext x; cases x <;> rfl)⟩
  right_inv := ⟨(sumMapHomotopy ea.right_inv.some eb.right_inv.some).cast
    (by ext x; cases x <;> rfl) (by ext x; cases x <;> rfl)⟩

@[simp] theorem sumHomotopyEquiv_toFun {A B A' B' : TopCat.{u}}
    (ea : ContinuousMap.HomotopyEquiv A A')
    (eb : ContinuousMap.HomotopyEquiv B B') :
    (sumHomotopyEquiv ea eb).toFun =
      (sumMap (TopCat.ofHom ea.toFun) (TopCat.ofHom eb.toFun)).hom := rfl

/-- Naturality of the inclusion of both endpoints. -/
theorem intervalEndpoints_naturality {A A' : TopCat.{u}} (a : A ⟶ A') :
    TopCat.intervalEndpoints A ≫ (a ▷ TopCat.I) =
      sumMap a a ≫ TopCat.intervalEndpoints A' := by
  apply ConcreteCategory.hom_ext
  intro x
  cases x <;> rfl

/-- Naturality of the endpoint attachment of a strict map of spans. -/
theorem endMap_naturality {A B C A' B' C' : TopCat.{u}}
    {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') :
    endMap f g ≫ sumMap b c = sumMap a a ≫ endMap f' g' := by
  ext x
  cases x with
  | inl x => exact congrArg Sum.inl (ConcreteCategory.congr_hom wf x)
  | inr x => exact congrArg Sum.inr (ConcreteCategory.congr_hom wg x)

variable {A B C D A' B' C' D' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {f' : A' ⟶ B'} {g' : A' ⟶ C'}
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  {l' : A' ⊗ TopCat.I ⟶ D'} {e' : TopCat.of (B' ⊕ C') ⟶ D'}

/-- Homotopy invariance for a specified map of actual double cylinders.
Its forward map is exactly the specified map `d`. -/
def homotopyEquivOfMap
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
    (wl : (a ▷ TopCat.I) ≫ l' = l ≫ d)
    (we : sumMap b c ≫ e' = e ≫ d)
    (ea : ContinuousMap.HomotopyEquiv A A') (ha : ea.toFun = a.hom)
    (eb : ContinuousMap.HomotopyEquiv B B') (hb : eb.toFun = b.hom)
    (ec : ContinuousMap.HomotopyEquiv C C') (hc : ec.toFun = c.hom) :
    ContinuousMap.HomotopyEquiv D D' :=
  TopCat.Pushout.pushoutHomotopyEquivOfMap sq sq'
    (TopCat.homotopyExtensionProperty_intervalEndpoints A)
    (TopCat.homotopyExtensionProperty_intervalEndpoints A')
    (sumMap a a) (a ▷ TopCat.I) (sumMap b c) d
    (intervalEndpoints_naturality a) (endMap_naturality a b c wf wg) wl.symm we.symm
    (sumHomotopyEquiv ea ea) (by simp only [sumHomotopyEquiv_toFun, ha]; rfl)
    (ea.prodCongr (ContinuousMap.HomotopyEquiv.refl TopCat.I)) (by
      ext x
      change (ea.toFun x.1, x.2) = (a x.1, x.2)
      rw [ha])
    (sumHomotopyEquiv eb ec) (by simp only [sumHomotopyEquiv_toFun, hb, hc]; rfl)

@[simp] theorem homotopyEquivOfMap_toFun
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (d : D ⟶ D')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
    (wl : (a ▷ TopCat.I) ≫ l' = l ≫ d)
    (we : sumMap b c ≫ e' = e ≫ d)
    (ea : ContinuousMap.HomotopyEquiv A A') (ha : ea.toFun = a.hom)
    (eb : ContinuousMap.HomotopyEquiv B B') (hb : eb.toFun = b.hom)
    (ec : ContinuousMap.HomotopyEquiv C C') (hc : ec.toFun = c.hom) :
    (homotopyEquivOfMap sq sq' a b c d wf wg wl we ea ha eb hb ec hc).toFun = d.hom := rfl


/-- The canonical map of actual double cylinders induced by a strict map
of their underlying spans. -/
def map
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') : D ⟶ D' :=
  sq.desc ((a ▷ TopCat.I) ≫ l') (sumMap b c ≫ e') (by
    rw [← Category.assoc, intervalEndpoints_naturality, Category.assoc, sq'.w,
      ← Category.assoc, ← endMap_naturality a b c wf wg, Category.assoc])

@[reassoc (attr := simp)] theorem map_cylinder
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') :
    l ≫ map sq sq' a b c wf wg = (a ▷ TopCat.I) ≫ l' := sq.inl_desc _ _ _

@[reassoc (attr := simp)] theorem map_ends
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') :
    e ≫ map sq sq' a b c wf wg = sumMap b c ≫ e' := sq.inr_desc _ _ _

@[simp] theorem map_cylinder_apply
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') (x : A) (t : TopCat.I) :
    map sq sq' a b c wf wg (l (x, t)) = l' (a x, t) :=
  ConcreteCategory.congr_hom (map_cylinder sq sq' a b c wf wg) (x, t)

@[simp] theorem map_left
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') (x : B) :
    map sq sq' a b c wf wg (e (Sum.inl x)) = e' (Sum.inl (b x)) :=
  ConcreteCategory.congr_hom (map_ends sq sq' a b c wf wg) (Sum.inl x)

@[simp] theorem map_right
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g') (x : C) :
    map sq sq' a b c wf wg (e (Sum.inr x)) = e' (Sum.inr (c x)) :=
  ConcreteCategory.congr_hom (map_ends sq sq' a b c wf wg) (Sum.inr x)

/-- A componentwise homotopy equivalence of strict spans induces an ordinary
homotopy equivalence via the canonical map of their actual double cylinders. -/
def mapHomotopyEquiv
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
    (ea : ContinuousMap.HomotopyEquiv A A') (ha : ea.toFun = a.hom)
    (eb : ContinuousMap.HomotopyEquiv B B') (hb : eb.toFun = b.hom)
    (ec : ContinuousMap.HomotopyEquiv C C') (hc : ec.toFun = c.hom) :
    ContinuousMap.HomotopyEquiv D D' :=
  homotopyEquivOfMap sq sq' a b c (map sq sq' a b c wf wg) wf wg
    (map_cylinder sq sq' a b c wf wg).symm (map_ends sq sq' a b c wf wg).symm
    ea ha eb hb ec hc

@[simp] theorem mapHomotopyEquiv_toFun
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)
    (sq' : IsPushout (TopCat.intervalEndpoints A') (endMap f' g') l' e')
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
    (ea : ContinuousMap.HomotopyEquiv A A') (ha : ea.toFun = a.hom)
    (eb : ContinuousMap.HomotopyEquiv B B') (hb : eb.toFun = b.hom)
    (ec : ContinuousMap.HomotopyEquiv C C') (hc : ec.toFun = c.hom) :
    (mapHomotopyEquiv sq sq' a b c wf wg ea ha eb hb ec hc).toFun =
      (map sq sq' a b c wf wg).hom := rfl

end TopCat.DoubleCylinder
