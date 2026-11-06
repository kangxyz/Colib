/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.KTheory.Quillen.Localization.Serre.FiberComparison
public import Colib.KTheory.Quillen.Map.Functoriality

/-! # A basepoint-compatible Serre-localization fiber comparison

This uses exactly the normalized Q-functors underlying the defined K-group
maps. The comparison fixes the original chosen zero basepoints. The later
`FiberEquivalence` module proves that this actual map is a weak homotopy
equivalence; no global continuous homotopy inverse is asserted here.
-/
/-! Implementation provenance: adapted from
`Quillen/Localization/Serre/BasedFiberComparison.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual functors, maps and
basepoint tracks are retained, using native Colib lower owners. -/

@[expose] public section

open CategoryTheory.ExactCategory

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Topology HomotopyGroup
open scoped ZeroObject unitInterval

namespace CategoryTheory.ExactCategory.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The normalized quotient/inclusion composite is naturally isomorphic to zero. -/
def normalizedQuotientInclusionZeroIso :
    (ObjectProperty.exactInclusion P).normalizedQ ⋙
      (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ ≅
      (Functor.const (abelianExactStructure P.FullSubcategory).QCategory).obj
        ((abelianExactStructure P.isoModSerre.Localization)).qZero :=
  (rebaseFunctorCompRightIso (Abelian.Devissage.mapQ P) (quotientMapQ P)
    (abelianExactStructure P.FullSubcategory).qZero (abelianExactStructure
      C).qZero
    ((abelianExactStructure P.isoModSerre.Localization)).qZero
    ((abelianExactStructure C).qIsoOfIso (ObjectProperty.exactInclusion
      P).toFunctor.mapZeroObject)
    (((abelianExactStructure P.isoModSerre.Localization)).qIsoOfIso
      ((ExactFunctor.serreLocalization P
      P.isoModSerre.Q)).toFunctor.mapZeroObject)).symm ≪≫
      quotientInclusionZeroIso P

/-- The normalized composite sends the source zero exactly to the target zero. -/
theorem normalizedComposite_obj_zero :
    ((ObjectProperty.exactInclusion P).normalizedQ ⋙
      (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ).obj
      (abelianExactStructure P.FullSubcategory).qZero =
        ((abelianExactStructure P.isoModSerre.Localization)).qZero :=
  rebaseFunctor_comp_obj_base _ _ _ _ _ _ _

/-- Its comparison at zero is the identity after the exact displayed equality. -/
theorem normalizedZeroIso_hom_base :
    (normalizedQuotientInclusionZeroIso P).hom.app
      (abelianExactStructure P.FullSubcategory).qZero =
        eqToHom (normalizedComposite_obj_zero P) :=
  (((abelianExactStructure P.isoModSerre.Localization)).qHom_subsingleton_of_isZero _ _
    (isZero_zero (P.isoModSerre.Localization))).elim _ _

/-- The actual relative topological nullhomotopy for the normalized maps. -/
def normalizedQuotientInclusionHomotopy :
    ((classifyingSpaceMap ((ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ)).hom.comp
      (classifyingSpaceMap ((ObjectProperty.exactInclusion P).normalizedQ)).hom).HomotopyRel
      (ContinuousMap.const _ ((abelianExactStructure P.isoModSerre.Localization)).kBasepoint)
      {(abelianExactStructure P.FullSubcategory).kBasepoint} :=
  (classifyingSpaceNaturalTransformationBasedHomotopy
    (normalizedQuotientInclusionZeroIso P).hom
    (abelianExactStructure P.FullSubcategory).qZero
    (normalizedComposite_obj_zero P) (normalizedZeroIso_hom_base P)).cast
      (by simp only [classifyingSpaceMap_comp, TopCat.hom_comp])
      (by rw [classifyingSpaceMap_const_direct]; rfl)

/-- The nullhomotopy stays at the target's actual chosen basepoint. -/
theorem normalizedQuotientInclusionHomotopy_based (t : I) :
    normalizedQuotientInclusionHomotopy P
      (t, (abelianExactStructure P.FullSubcategory).kBasepoint) =
        ((abelianExactStructure P.isoModSerre.Localization)).kBasepoint := by
  have hh := (normalizedQuotientInclusionHomotopy P).prop t
    (abelianExactStructure P.FullSubcategory).kBasepoint (Set.mem_singleton _)
  exact hh.trans (by
    change classifyingSpaceMap ((ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ)
      (classifyingSpaceMap ((ObjectProperty.exactInclusion P).normalizedQ)
        (abelianExactStructure P.FullSubcategory).kBasepoint) = _
    rw [(ObjectProperty.exactInclusion P).normalizedQ_map_point,
      ((ExactFunctor.serreLocalization P
        P.isoModSerre.Q)).normalizedQ_map_point])

/-- The localization comparison into the fiber of precisely the normalized
map that defines the quotient's K-group homomorphisms. -/
def basedLocalizationFiberComparison :
    C((abelianExactStructure P.FullSubcategory).KSpace,
      HomotopyFiber
        (classifyingSpaceMap (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ).hom
        ((abelianExactStructure P.isoModSerre.Localization)).kBasepoint) :=
  HomotopyFiber.lift _ _ (classifyingSpaceMap ((ObjectProperty.exactInclusion P).normalizedQ)).hom
    (normalizedQuotientInclusionHomotopy P).toHomotopy

/-- The comparison preserves the chosen zero/constant-path basepoint. -/
theorem basedLocalizationFiberComparison_basepoint :
    basedLocalizationFiberComparison P (abelianExactStructure P.FullSubcategory).kBasepoint =
      HomotopyFiber.basepoint
        (classifyingSpaceMap (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ).hom
        ((abelianExactStructure P.isoModSerre.Localization)).kBasepoint (abelianExactStructure
          C).kBasepoint
        ((ExactFunctor.serreLocalization P
          P.isoModSerre.Q)).normalizedQ_map_point := by
  apply Subtype.ext
  apply Prod.ext
  · exact (ObjectProperty.exactInclusion P).normalizedQ_map_point
  · apply ContinuousMap.ext
    intro t
    exact normalizedQuotientInclusionHomotopy_based P t

/-- The normalized path-space fiber used by the canonical K-map. -/
abbrev NormalizedLocalizationFiber :=
  HomotopyFiber
        (classifyingSpaceMap (ExactFunctor.serreLocalization P P.isoModSerre.Q).normalizedQ).hom
    ((abelianExactStructure P.isoModSerre.Localization)).kBasepoint

/-- Its chosen constant-path basepoint. -/
def normalizedFiberBasepoint : NormalizedLocalizationFiber P :=
  HomotopyFiber.basepoint _ _ (abelianExactStructure C).kBasepoint
    ((ExactFunctor.serreLocalization P
      P.isoModSerre.Q)).normalizedQ_map_point

/-- The based comparison induces a genuine homomorphism into the fiber's
homotopy groups. No assertion that it is an isomorphism is made. -/
def localizationFiberComparisonHom (n : ℕ) :
    (abelianExactStructure P.FullSubcategory).K n →*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P) :=
  piMap n (basedLocalizationFiberComparison P) (basedLocalizationFiberComparison_basepoint P)

/-- Fiber projection on the same homotopy groups. -/
def localizationFiberProjectionHom (n : ℕ) :
    HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P) →*
      (abelianExactStructure C).K n :=
  piMap n (HomotopyFiber.projection _ _)
    (show HomotopyFiber.projection _ _ (normalizedFiberBasepoint P) =
      (abelianExactStructure C).kBasepoint from rfl)

set_option backward.isDefEq.respectTransparency false in
/-- The based comparison is compatible with the actual inclusion K-map. -/
theorem localizationFiberComparisonHom_projection (n : ℕ) :
    (localizationFiberProjectionHom P n).comp (localizationFiberComparisonHom P n) =
      Abelian.Devissage.KMap P n := by
  change (piMap n _ _).comp (piMap n _ _) = _
  rw [← HomotopyGroup.mapHom_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical inclusion and quotient K-maps have trivial composite.
This follows from the actual based nullhomotopy, independently of the later
fiber weak-equivalence theorem. -/
theorem quotientKMap_comp_inclusion (n : ℕ) :
    (quotientKMap P n).comp (Abelian.Devissage.KMap P n) = 1 := by
  change (((ExactFunctor.serreLocalization P P.isoModSerre.Q)).KMap
    n).comp ((ObjectProperty.exactInclusion
    P).KMap n) = 1
  rw [CategoryTheory.ExactCategory.ExactFunctor.KMap_eq_piMap,
    CategoryTheory.ExactCategory.ExactFunctor.KMap_eq_piMap,
    ← HomotopyGroup.mapHom_comp]
  exact piMap_eq_one_of_based_nullhomotopy n _
    (normalizedQuotientInclusionHomotopy P).toHomotopy
    (normalizedQuotientInclusionHomotopy_based P)

end CategoryTheory.ExactCategory.SerreLocalization

attribute [colib_ref "WeibelKBook" "V, Theorem 5.1 and proof, page 35" "ingredient"
  "The original inclusion lifts to the genuine quotient homotopy fiber; no equivalence asserted"]
  CategoryTheory.ExactCategory.SerreLocalization.basedLocalizationFiberComparison
  CategoryTheory.ExactCategory.SerreLocalization.basedLocalizationFiberComparison_basepoint
  CategoryTheory.ExactCategory.SerreLocalization.localizationFiberComparisonHom_projection
  CategoryTheory.ExactCategory.SerreLocalization.quotientKMap_comp_inclusion
