/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.QConstruction.ObjectClass
public import Colib.KTheory.GrothendieckGroup.Basic
public import Mathlib.CategoryTheory.SingleObj

/-!
# The Grothendieck cocycle of the Q-category

The weight of an admissible span is exactly `[apex] - [source]`. The original
kernel pullback relation proves its additivity. The resulting actual functor
to SingleObj uses the existing reverse-composition multiplication convention.
The apex isomorphism is extracted by Mathlib Span.SpanBicat.apexIso.

## Implementation provenance

Extracted from `Quillen/KTheory/GrothendieckComparison/Cocycle.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The exact-structure assumptions,
independent object/hom universes, actual functors and generator maps are retained.
This is purely algebraic and makes no identification with topological π₁ or K₀.
-/

@[expose] public noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.ExactCategory.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- The Grothendieck classes in a pullback along an admissible quotient satisfy
the expected additive square relation. -/
lemma grothendieckClass_pullback {A B T P : C} {a : P ⟶ A} {b : P ⟶ B}
    {i : A ⟶ T} {p : B ⟶ T} (sq : IsPullback a b i p) (hp : E.deflation p) :
    E.grothendieckClass P + E.grothendieckClass T =
      E.grothendieckClass A + E.grothendieckClass B := by
  obtain ⟨K, k, hk, hS⟩ := hp
  have h₁ := E.grothendieckClass_additive hS
  have h₂ := E.grothendieckClass_additive (E.conflation_pullback_same_kernel hS sq)
  change E.grothendieckClass B = E.grothendieckClass K + E.grothendieckClass T at h₁
  change E.grothendieckClass P = E.grothendieckClass K + E.grothendieckClass A at h₂
  rw [h₁, h₂]
  abel

/-- The additive Grothendieck weight of a representative Q-span. -/
def qSpanGrothendieckWeight {X Y : C} (s : Span E.deflation E.inflation X Y) :
    E.GrothendieckGroup := E.grothendieckClass s.apex - E.grothendieckClass X

lemma qSpanGrothendieckWeight_iso {X Y : C}
    {s t : Span E.deflation E.inflation X Y} (e : s ≅ t) :
    E.qSpanGrothendieckWeight s = E.qSpanGrothendieckWeight t := by
  let e' : s.apex ≅ t.apex := Span.SpanBicat.apexIso e
  simp only [qSpanGrothendieckWeight, E.grothendieckClass_iso e']

/-- The pullback definition of span composition makes the weights additive. -/
lemma qSpanGrothendieckWeight_comp {X Y Z : C}
    (s : Span E.deflation E.inflation X Y) (t : Span E.deflation E.inflation Y Z) :
    E.qSpanGrothendieckWeight (Span.comp s t) =
      E.qSpanGrothendieckWeight s + E.qSpanGrothendieckWeight t := by
  have h := E.grothendieckClass_pullback (IsPullback.of_hasPullback s.r t.l) t.wl
  dsimp only [qSpanGrothendieckWeight, Span.comp_apex]
  rw [eq_sub_iff_add_eq.mpr h]
  abel

/-- The Grothendieck weight descends through the actual apex-isomorphism quotient. -/
def qGrothendieckWeight {X Y : E.QCategory} (f : X ⟶ Y) : E.GrothendieckGroup :=
  Quotient.lift (fun s : Span E.deflation E.inflation X.obj.of Y.obj.of => E.qSpanGrothendieckWeight
    s)
    (fun s t (h : Nonempty (s ≅ t)) => E.qSpanGrothendieckWeight_iso h.some) f

@[simp] lemma qGrothendieckWeight_mkHom {X Y : C}
    (s : Span E.deflation E.inflation X Y) :
    E.qGrothendieckWeight (QConstruction.mkHom E.deflation E.inflation s) =
      E.qSpanGrothendieckWeight s := rfl

@[simp] lemma qGrothendieckWeight_id (X : E.QCategory) :
    E.qGrothendieckWeight (𝟙 X) = 0 := sub_self _

lemma qGrothendieckWeight_comp {X Y Z : E.QCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    E.qGrothendieckWeight (f ≫ g) = E.qGrothendieckWeight f + E.qGrothendieckWeight g := by
  refine Quotient.inductionOn₂ f g (fun s t => ?_)
  exact E.qSpanGrothendieckWeight_comp s t

/-- The canonical Grothendieck cocycle as an actual functor on QConstruction. -/
def qGrothendieckFunctor : E.QCategory ⥤ SingleObj (Multiplicative E.GrothendieckGroup) where
  obj _ := SingleObj.star _
  map f := Multiplicative.ofAdd (E.qGrothendieckWeight f)
  map_id X := by change Multiplicative.ofAdd _ = 1; simp
  map_comp f g := by
    change Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [E.qGrothendieckWeight_comp, add_comm]
    rfl

/-- The zero-apex path has weight zero. -/
@[simp] lemma qGrothendieckWeight_fromZero (X : E.QCategory) :
    E.qGrothendieckWeight (E.fromZero X) = 0 := by
  change E.grothendieckClass (0 : C) - E.grothendieckClass (0 : C) = 0
  simp

/-- The whole-apex path has the canonical Grothendieck class as its weight. -/
@[simp] lemma qGrothendieckWeight_fromZeroTotal (X : E.QCategory) :
    E.qGrothendieckWeight (E.fromZeroTotal X) = E.grothendieckClass X.obj.of := by
  change E.grothendieckClass X.obj.of - E.grothendieckClass (0 : C) = _
  simp

/-- The Q-cocycle recovers each canonical object generator exactly. -/
@[simp] lemma qObjectClass_qGrothendieckFunctor (X : C) :
    E.qObjectClass E.qGrothendieckFunctor X =
      SingleObj.toEnd (Multiplicative E.GrothendieckGroup)
        (Multiplicative.ofAdd (E.grothendieckClass X)) := by
  simp only [qObjectClass, qGrothendieckFunctor, qGrothendieckWeight_fromZeroTotal,
    qGrothendieckWeight_fromZero, SingleObj.inv_as_inv, SingleObj.comp_as_mul]
  change (1 : Multiplicative E.GrothendieckGroup)⁻¹ *
      Multiplicative.ofAdd (E.grothendieckClass X) = Multiplicative.ofAdd (E.grothendieckClass X)
  simp

end CategoryTheory.ExactCategory.ExactStructure

attribute [colib_tag "COL-0079",
  colib_ref "WeibelKBook" "IV, Example 6.2.3, page 54"
    "adaptation"
    "Algebraic kernel-class weight equals apex class minus source class; no topological comparison"]
  CategoryTheory.ExactCategory.ExactStructure.qGrothendieckWeight
  CategoryTheory.ExactCategory.ExactStructure.qGrothendieckFunctor
  CategoryTheory.ExactCategory.ExactStructure.qObjectClass_qGrothendieckFunctor
