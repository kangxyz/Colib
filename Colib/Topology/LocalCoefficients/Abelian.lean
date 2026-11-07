/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.Basic

/-!
Adapted from `Quillen/Topology/LocalCoefficients/Abelian.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, retaining its actual coefficient maps.

# Abelian monodromy and genuine coefficient automorphisms

Abelian monodromy means that images of loops at a point commute. It does not
assert that transport is trivial. A loop then extends, by conjugate transport,
to a natural automorphism on its path component. This is the coefficient
correction needed in the injectivity argument for twisted group completion.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace FundamentalGroupoid.LocalCoefficients

/-- An actual representation has abelian monodromy when its loop actions commute. -/
def AbelianMonodromy {C : Type u} [Category C] {D : Type v} [Category D]
    (A : C ⥤ D) : Prop :=
  ∀ (x : C) (g h : x ⟶ x), A.map g ≫ A.map h = A.map h ≫ A.map g

/-- Pullback preserves the abelian-monodromy condition. -/
theorem AbelianMonodromy.whisker {C : Type u} [Category C] {D : Type v} [Category D]
    {E : Type w} [Category E] {A : D ⥤ E} (hA : AbelianMonodromy A) (F : C ⥤ D) :
    AbelianMonodromy (F ⋙ A) :=
  fun x g h ↦ hA (F.obj x) (F.map g) (F.map h)

/-- Every local system on a groupoid with commutative loop groups is abelian.
This is the precise upgrade needed on the loop-space target of group completion. -/
theorem abelianMonodromy_of_commutative_loops {C : Type u} [Category C]
    {D : Type v} [Category D] (A : C ⥤ D)
    (h : ∀ (x : C) (g k : x ⟶ x), g ≫ k = k ≫ g) : AbelianMonodromy A := by
  intro x g k
  rw [← A.map_comp, ← A.map_comp, h x g k]

section Groupoid

variable {C : Type u} [Groupoid C] {D : Type v} [Category D]
    {A : C ⥤ D}

/-- Conjugate transport of a loop commutes with every connecting arrow.
The connecting paths need not be chosen compatibly. -/
theorem conjugateLoop_naturality (hA : AbelianMonodromy A) {b x y : C} (g : b ⟶ b)
    (p : b ⟶ x) (q : b ⟶ y) (f : x ⟶ y) :
    A.map (inv p ≫ g ≫ p) ≫ A.map f =
      A.map f ≫ A.map (inv q ≫ g ≫ q) := by
  have h := hA b g (p ≫ f ≫ inv q)
  have h' := congrArg (fun k ↦ A.map (inv p) ≫ k ≫ A.map q) h
  simpa only [Functor.map_comp, Category.assoc, ← Functor.map_comp,
    IsIso.inv_hom_id, IsIso.hom_inv_id, IsIso.inv_hom_id_assoc,
    Category.id_comp, Category.comp_id] using h'

/-- The correction is independent of the chosen path from the basepoint. -/
theorem conjugateLoop_independent (hA : AbelianMonodromy A) {b x : C} (g : b ⟶ b) (p q : b ⟶ x) :
    A.map (inv p ≫ g ≫ p) = A.map (inv q ≫ g ≫ q) := by
  simpa using conjugateLoop_naturality hA g p q (𝟙 x)

/-- A loop gives a genuine natural coefficient automorphism on a component
with specified connecting arrows. No homological conclusion is assumed. -/
def loopCorrectionIso (hA : AbelianMonodromy A) (b : C) (p : ∀ x : C, b ⟶ x) (g : b ⟶ b) : A ≅ A :=
  NatIso.ofComponents (fun x ↦ A.mapIso (asIso (inv (p x) ≫ g ≫ p x)))
    (fun {x y} f ↦ (conjugateLoop_naturality hA g (p x) (p y) f).symm)

@[simp]
theorem loopCorrectionIso_hom_app (hA : AbelianMonodromy A) (b : C) (p : ∀ x : C, b ⟶ x) (g : b ⟶ b)
    (x : C) :
    (loopCorrectionIso hA b p g).hom.app x = A.map (inv (p x) ≫ g ≫ p x) := rfl

/-- Different choices of connecting arrows produce the identical coefficient iso. -/
theorem loopCorrectionIso_independent (hA : AbelianMonodromy A) (b : C) (p q : ∀ x : C, b ⟶ x)
    (g : b ⟶ b) : loopCorrectionIso hA b p g = loopCorrectionIso hA b q g := by
  apply Iso.ext
  ext x
  exact conjugateLoop_independent hA g (p x) (q x)

/-- Extend one loop action by the identity off its entire groupoid component. -/
def componentLoopIsoApp (b : C) (g : b ⟶ b) (x : C) : A.obj x ≅ A.obj x := by
  classical
  exact if h : Nonempty (b ⟶ x) then
    A.mapIso (asIso (inv h.some ≫ g ≫ h.some)) else Iso.refl _

/-- Extension by the identity is natural even when the groupoid is disconnected. -/
theorem componentLoopIsoApp_naturality (hA : AbelianMonodromy A)
    (b : C) (g : b ⟶ b) {x y : C} (f : x ⟶ y) :
    A.map f ≫ (componentLoopIsoApp (A := A) b g y).hom =
      (componentLoopIsoApp (A := A) b g x).hom ≫ A.map f := by
  classical
  by_cases hx : Nonempty (b ⟶ x)
  · have hy : Nonempty (b ⟶ y) := ⟨hx.some ≫ f⟩
    simp only [componentLoopIsoApp, dite_eq_left hx, dite_eq_left hy, Functor.mapIso_hom,
      asIso_hom]
    exact (conjugateLoop_naturality hA g hx.some hy.some f).symm
  · have hy : ¬ Nonempty (b ⟶ y) := fun hy ↦ hx ⟨hy.some ≫ inv f⟩
    simp [componentLoopIsoApp, hx, hy]

/-- The genuine coefficient correction associated to a loop, acting trivially
outside its component. In particular, no global connectedness is assumed. -/
def componentLoopCorrectionIso (hA : AbelianMonodromy A)
    (b : C) (g : b ⟶ b) : A ≅ A :=
  NatIso.ofComponents (componentLoopIsoApp b g)
    (fun f ↦ componentLoopIsoApp_naturality hA b g f)

/-- On its component the correction is conjugate transport along any chosen path. -/
theorem componentLoopCorrectionIso_hom_app (hA : AbelianMonodromy A)
    {b x : C} (g : b ⟶ b) (p : b ⟶ x) :
    (componentLoopCorrectionIso hA b g).hom.app x = A.map (inv p ≫ g ≫ p) := by
  classical
  have h : Nonempty (b ⟶ x) := ⟨p⟩
  change (componentLoopIsoApp b g x).hom = _
  simp only [componentLoopIsoApp, dite_eq_left h, Functor.mapIso_hom, asIso_hom]
  exact conjugateLoop_independent hA g h.some p

/-- At the chosen basepoint the correction is precisely the original loop action. -/
@[simp]
theorem componentLoopCorrectionIso_hom_base (hA : AbelianMonodromy A)
    {b : C} (g : b ⟶ b) :
    (componentLoopCorrectionIso hA b g).hom.app b = A.map g := by
  simpa using componentLoopCorrectionIso_hom_app hA g (𝟙 b)

/-- No transport is changed on the other components. -/
theorem componentLoopCorrectionIso_hom_off (hA : AbelianMonodromy A)
    {b x : C} (g : b ⟶ b) (hx : ¬ Nonempty (b ⟶ x)) :
    (componentLoopCorrectionIso hA b g).hom.app x = 𝟙 _ := by
  classical
  simp [componentLoopCorrectionIso, componentLoopIsoApp, hx]

/-- Two paths with the same endpoints differ by the value of a genuine
coefficient automorphism, rather than by an unjustified equality of transports. -/
theorem map_eq_map_comp_loopCorrection (hA : AbelianMonodromy A)
    {x y : C} (p q : x ⟶ y) :
    A.map p = A.map q ≫
      (componentLoopCorrectionIso hA y (inv q ≫ p)).hom.app y := by
  rw [componentLoopCorrectionIso_hom_base, ← A.map_comp]
  simp

end Groupoid

/-- Constant coefficients have abelian monodromy. -/
theorem constant_abelianMonodromy (X : Type u) [TopologicalSpace X]
    (V : ModuleCat.{v} ℤ) : AbelianMonodromy (constant X V) := by
  intro x g h
  rfl

/-- Spatial pullback of a possibly nonconstant abelian system is again abelian. -/
theorem pullback_abelianMonodromy {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    {A : System.{v, w} Y} (hA : AbelianMonodromy A) :
    AbelianMonodromy (pullback f A) :=
  hA.whisker (FundamentalGroupoid.map f)

/-- A genuine path-loop determines the correction on its path component. -/
def pathLoopCorrectionIso {X : Type u} [TopologicalSpace X]
    {A : System.{u, v} X} (hA : AbelianMonodromy A) {b : X} (g : Path b b) : A ≅ A :=
  componentLoopCorrectionIso hA (FundamentalGroupoid.mk b) (Path.Homotopic.Quotient.mk g)

/-- Its component is exactly reverse-path, loop, forward-path transport. -/
theorem pathLoopCorrectionIso_hom_app {X : Type u} [TopologicalSpace X]
    {A : System.{u, v} X} (hA : AbelianMonodromy A) {b x : X}
    (g : Path b b) (p : Path b x) :
    (pathLoopCorrectionIso hA g).hom.app (FundamentalGroupoid.mk x) =
      transport A p.symm ≫ transport A g ≫ transport A p := by
  rw [pathLoopCorrectionIso, componentLoopCorrectionIso_hom_app hA
    (Path.Homotopic.Quotient.mk g) (Path.Homotopic.Quotient.mk p)]
  simp only [Functor.map_comp, ← Groupoid.inv_eq_inv]
  rfl

end FundamentalGroupoid.LocalCoefficients
