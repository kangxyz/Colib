/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/

module

public import Colib.Topology.Realization.SimplexBoundary.Annulus
public import Colib.Topology.Realization.SimplexAttachment.OverlapFunctor

/-!
# Attachment Charts

The original attaching map restricted to one actual higher-cell boundary.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set CategoryTheory CategoryTheory.Limits _root_.stdSimplex TopCat
open FundamentalGroupoid.OpenCover
universe u v w
namespace TopCat.SimplexAttachment
open FundamentalGroupoid.OpenCover
variable (A : TopCat.{u}) [DiscreteTopology A] (n : ℕ) {O D : TopCat.{u}}
    {f : TopCat.of (A × _root_.stdSimplex.boundary (n + 3)) ⟶ O}
    {g : TopCat.of (A × _root_.stdSimplex ℝ (Fin (n + 4))) ⟶ D} {j : O ⟶ D}
    (sq : IsPushout (parameterizedSimplexBoundaryInclusion A (n + 3)) f g j)
    {C : Type v} [Groupoid.{w} C] (F : FundamentalGroupoid O ⥤ C)

/-- The original attaching map restricted to one actual higher-cell boundary. -/
def boundaryMap (a : A) : C(_root_.stdSimplex.boundary (n + 3), O) :=
  ⟨fun x => f (a, x), f.hom.continuous.comp (continuous_const.prodMk continuous_id)⟩

/-- Pullback of the given old-space decoder to the original boundary. -/
def boundaryFunctor (a : A) : FundamentalGroupoid (_root_.stdSimplex.boundary (n + 3)) ⥤ C :=
  FundamentalGroupoid.map (boundaryMap A n (f := f) a) ⋙ F

/-- The old-space decoder pulled back through the actual collar retraction. -/
def collarFunctor : FundamentalGroupoid (simplexAttachmentCollar A (n + 3) sq) ⥤ C :=
  FundamentalGroupoid.map (simplexAttachmentCollarRetraction A (n + 3) sq) ⋙ F

omit [DiscreteTopology A] in
/-- The original annulus-to-collar map really retracts to the original attaching map
following the original radial boundary projection. -/
theorem annulusFunctor_eq (a : A) :
    FundamentalGroupoid.map (annulusToCollar A (n + 3) sq a) ⋙ collarFunctor A n sq F =
      FundamentalGroupoid.map (annulusBoundary (n + 3)) ⋙ boundaryFunctor A n (f := f) F a := by
  let r := simplexAttachmentCollarRetraction A (n + 3) sq
  let k := annulusToCollar A (n + 3) sq a
  have hk : r.comp k = (boundaryMap A n (f := f) a).comp (annulusBoundary (n + 3)) := by
    ext x
    exact collarRetraction_annulus A (n + 3) sq a x
  change FundamentalGroupoid.map k ⋙ (FundamentalGroupoid.map r ⋙ F) = _
  rw [← Functor.assoc, ← FundamentalGroupoid.map_comp, hk, FundamentalGroupoid.map_comp]
  rfl

/-- A constructed trivialization on every actual higher-cell annulus. -/
def annulusTransition (a : A) :
    FundamentalGroupoid.map (annulusToCollar A (n + 3) sq a) ⋙ collarFunctor A n sq F ≅
      (Functor.const (FundamentalGroupoid (simplexAnnulus (n + 3)))).obj
        (F.obj (FundamentalGroupoid.mk
          (f (a, _root_.stdSimplex.Boundary.vertex (0 : Fin (n + 4)))))) :=
  eqToIso (annulusFunctor_eq A n sq F a) ≪≫
    _root_.stdSimplex.Boundary.annulusConstantIso (boundaryFunctor A n (f := f) F a)

/-- Naturality on EVERY actual collar/interior overlap path, not merely edge generators. -/
def overlapTransition (a : A) :
    FundamentalGroupoid.map ((ContinuousMap.inclusion (s := (simplexAttachmentCollar A (n + 3)
        sq) ∩ (simplexAttachmentInterior A (n + 3) (g := g) a)) Set.inter_subset_left)) ⋙
        collarFunctor A n sq F ≅
      (Functor.const (FundamentalGroupoid ↥(simplexAttachmentCollar A (n + 3) sq ∩
        simplexAttachmentInterior A (n + 3) (g := g) a))).obj
          (F.obj (FundamentalGroupoid.mk
            (f (a, _root_.stdSimplex.Boundary.vertex (0 : Fin (n + 4)))))) :=
  actualOverlapIsoOfAnnulus A (n + 3) sq a (collarFunctor A n sq F) _
    (annulusTransition A n sq F a)

end TopCat.SimplexAttachment
