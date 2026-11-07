/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Topology.HomotopyPullback.Pushout
public import Colib.Topology.DoubleMappingCylinder.WeakCartesian
public import Colib.Topology.HomotopyPullback.WeakPasting

/-!
# Weak-cartesian cofibrant pushout cubes with the original comparison maps

The unchanged double cylinders and their genuine cofibrant collapse
homotopy equivalences transfer weak endpoint comparisons to the original
pushout. The final theorems use only the two original weak edge comparisons
and actual compact closed graphs in the target double cylinder. Weak pasting
and the exact collapse triangles retain both original
point coordinates and the canonical constant comparison path.


Implementation provenance:
`Quillen/Topology/HomotopyPullback/WeakPushout.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. Original maps,
hypotheses, path coordinates and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open Topology TopCat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace TopCat.CartesianPushout
open DoubleCylinder
variable {A B C P A' B' C' P' : TopCat.{u}}
  {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ P} {j : C ⟶ P}
  {f' : A' ⟶ B'} {g' : A' ⟶ C'} {i' : B' ⟶ P'} {j' : C' ⟶ P'}
  (sq : IsPushout f g i j) (sq' : IsPushout f' g' i' j')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') (p : P ⟶ P')
  (wf : f ≫ b = a ≫ f') (wg : g ≫ c = a ≫ g')
  (wi : i ≫ p = b ≫ i') (wj : j ≫ p = c ≫ j')
  (hf : TopCat.HomotopyExtensionProperty f) (hf' : TopCat.HomotopyExtensionProperty f')

include sq sq' wf wg wi wj hf hf' in
/-- The actual left cylinder comparison pastes with the original collapse
square. No homotopy inverse of that weak comparison is requested. -/
theorem leftComparison_isWeak_of_cylinder_comparison
    (hE : IsWeakHomotopyEquivalence (HomotopyPullback.comparison
      (cylinderMap a b c wf wg).hom
      (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f' g')).hom b.hom
      (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f g)).hom
      (DoubleCylinder.FiniteNormalization.left_square (cylinderSquare f g) (cylinderSquare f' g')
        a b c wf wg))) :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison p.hom i'.hom b.hom i.hom (congrArg TopCat.Hom.hom wi)) := by
  have h := HomotopyPullback.comparison_paste_isWeakHomotopyEquivalence
    b.hom (cylinderMap a b c wf wg).hom p.hom
    (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f g)).hom (collapseOfPushout sq).hom
    (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f' g')).hom (collapseOfPushout sq').hom
    (DoubleCylinder.FiniteNormalization.left_square (cylinderSquare f g) (cylinderSquare f' g')
      a b c wf wg)
    (collapse_square sq sq' a b c p wf wg wi wj) hE
    (isWeakHomotopyEquivalence_of_homotopyEquiv
      (collapseSquareEquiv sq sq' a b c p wf wg wi wj hf hf'))
  have hl : (collapseOfPushout sq).hom.comp (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f
    g)).hom = i.hom :=
    congrArg TopCat.Hom.hom (DoubleCylinder.collapse_leftEnd (cylinderSquare f g) sq)
  have hb : (collapseOfPushout sq').hom.comp
      (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f' g')).hom = i'.hom :=
    congrArg TopCat.Hom.hom (DoubleCylinder.collapse_leftEnd (cylinderSquare f' g') sq')
  let e := (HomotopyPullback.baseMapCongr p.hom _ i'.hom hb).toHomotopyEquiv
  have he := (isWeakHomotopyEquivalence_of_homotopyEquiv e).comp h
  convert he using 1
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (b x, i x, ContinuousMap.const unitInterval (i' (b x))) =
    (b x, collapseOfPushout sq (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f g) x),
      ContinuousMap.const unitInterval
        (collapseOfPushout sq' (DoubleCylinder.Subdivision.leftEnd (e := cylinderEnd f' g') (b x))))
  exact Prod.ext rfl (Prod.ext (ContinuousMap.congr_fun hl x).symm
    (ContinuousMap.ext (fun _ ↦ (ContinuousMap.congr_fun hb (b x)).symm)))

include sq sq' wf wg wi wj hf hf' in
/-- The symmetric original right comparison uses the same genuine collapse
and the original right triangle, with its canonical path unchanged. -/
theorem rightComparison_isWeak_of_cylinder_comparison
    (hE : IsWeakHomotopyEquivalence (HomotopyPullback.comparison
      (cylinderMap a b c wf wg).hom
      (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f' g')).hom c.hom
      (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f g)).hom
      (DoubleCylinder.FiniteNormalization.right_square (cylinderSquare f g) (cylinderSquare f' g')
        a b c wf wg))) :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison p.hom j'.hom c.hom j.hom (congrArg TopCat.Hom.hom wj)) := by
  have h := HomotopyPullback.comparison_paste_isWeakHomotopyEquivalence
    c.hom (cylinderMap a b c wf wg).hom p.hom
    (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f g)).hom (collapseOfPushout sq).hom
    (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f' g')).hom (collapseOfPushout sq').hom
    (DoubleCylinder.FiniteNormalization.right_square (cylinderSquare f g) (cylinderSquare f' g')
      a b c wf wg)
    (collapse_square sq sq' a b c p wf wg wi wj) hE
    (isWeakHomotopyEquivalence_of_homotopyEquiv
      (collapseSquareEquiv sq sq' a b c p wf wg wi wj hf hf'))
  have hr : (collapseOfPushout sq).hom.comp (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f
    g)).hom = j.hom :=
    congrArg TopCat.Hom.hom (DoubleCylinder.collapse_rightEnd (cylinderSquare f g) sq)
  have hc : (collapseOfPushout sq').hom.comp
      (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f' g')).hom = j'.hom :=
    congrArg TopCat.Hom.hom (DoubleCylinder.collapse_rightEnd (cylinderSquare f' g') sq')
  let e := (HomotopyPullback.baseMapCongr p.hom _ j'.hom hc).toHomotopyEquiv
  have he := (isWeakHomotopyEquivalence_of_homotopyEquiv e).comp h
  convert he using 1
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (c x, j x, ContinuousMap.const unitInterval (j' (c x))) =
    (c x, collapseOfPushout sq
      (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f g) x),
      ContinuousMap.const unitInterval
        (collapseOfPushout sq'
          (DoubleCylinder.Subdivision.rightEnd (e := cylinderEnd f' g') (c x))))
  exact Prod.ext rfl (Prod.ext (ContinuousMap.congr_fun hr x).symm
    (ContinuousMap.ext (fun _ ↦ (ContinuousMap.congr_fun hc (c x)).symm)))

variable
  (hgraph : ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [LocallyCompactSpace K]
    (d : C(K, Cylinder f' g')), IsClosed (Set.ofPred (fun z : K × Cylinder f' g' ↦ d z.1 = z.2)))
  (hL : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison b.hom f'.hom a.hom f.hom (congrArg TopCat.Hom.hom wf)))
  (hR : IsWeakHomotopyEquivalence
    (HomotopyPullback.comparison c.hom g'.hom a.hom g.hom (congrArg TopCat.Hom.hom wg)))

include sq sq' a b c p wf wg wi wj hf hf' hgraph hL hR in
/-- Weak canonical incoming comparisons give the original outgoing left
comparison in a cofibrant pushout cube. The only additional geometric input
is the actual compact closed-graph property of the target double cylinder. -/
theorem leftComparison_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison p.hom i'.hom b.hom i.hom (congrArg TopCat.Hom.hom wi)) :=
  leftComparison_isWeak_of_cylinder_comparison sq sq' a b c p wf wg wi wj hf hf'
    (DoubleCylinder.Cartesian.leftComparison_isWeakHomotopyEquivalence
      (cylinderSquare f g) (cylinderSquare f' g') a b c wf wg hgraph hL hR)

include sq sq' a b c p wf wg wi wj hf hf' hgraph hL hR in
/-- The symmetric original outgoing comparison, again with only weak
canonical edge inputs and genuine cofibrant collapse geometry. -/
theorem rightComparison_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence
      (HomotopyPullback.comparison p.hom j'.hom c.hom j.hom (congrArg TopCat.Hom.hom wj)) :=
  rightComparison_isWeak_of_cylinder_comparison sq sq' a b c p wf wg wi wj hf hf'
    (DoubleCylinder.Cartesian.rightComparison_isWeakHomotopyEquivalence
      (cylinderSquare f g) (cylinderSquare f' g') a b c wf wg hgraph hL hR)

end TopCat.CartesianPushout
