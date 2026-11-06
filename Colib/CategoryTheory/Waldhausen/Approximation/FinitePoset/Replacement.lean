/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Approximation.FinitePoset.Colimits
public import Colib.CategoryTheory.Waldhausen.FunctorialFactorization.Basic
public import Mathlib.Order.Preorder.Finite
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cofibrant replacement of finite-poset diagrams

Insertion diagrams and projections construct a cofibrant replacement step with preserved
    latching colimits. Finite induction supplies a replacement preserving the specified lower ideal.

Implementation provenance: `Quillen/Waldhausen/Approximation/FinitePoset/Replacement.lean` at
Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps, hypotheses,
chosen zero objects and universe parameters are retained.
-/
@[expose] public section

open CategoryTheory.Waldhausen



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Limits.FinitePosetLatching
universe w w' z u v u' v'

namespace CategoryTheory.Limits.FinitePosetInsertion
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  (m : J) (hm : IsMax m)

/-- The unchanged old indexing subposet. -/
abbrev Old := ({m}ᶜ : Set J)

/-- The strict boundary embeds literally into the old subposet. -/
def boundaryInclusion : Set.Iio m ⥤ Old m :=
  (show Monotone (fun x : Set.Iio m ↦ (⟨x.val, ne_of_lt x.property⟩ : Old m)) from
    fun _ _ h ↦ h).functor

include hm in
/-- A predecessor of an old vertex cannot be the removed maximal vertex. -/
theorem predecessor_ne {x y : J} (hxy : x ≤ y) (hy : y ≠ m) : x ≠ m := by
  intro hx
  subst x
  exact hy (hm.eq_of_le hxy).symm

variable (R : Old m ⥤ C) (c : Cocone (boundaryInclusion m ⋙ R))

/-- The one new object is the actual latching cocone point. -/
def insertedObj (x : J) : C := by
  classical
  exact if hx : x = m then c.pt else R.obj ⟨x, hx⟩

/-- Canonical equality identification at an unchanged old object. -/
def insertedOldIso (x : Old m) : insertedObj m R c x.val ≅ R.obj x :=
  eqToIso (by
    have hx : x.val ≠ m := x.property
    simp [insertedObj, hx])

/-- Canonical equality identification at the newly attached object. -/
def insertedNewIso : insertedObj m R c m ≅ c.pt :=
  eqToIso (by simp [insertedObj])

/-- Every new arrow is either an old diagram arrow or an actual boundary leg. -/
def insertedMap {x y : J} (f : x ⟶ y) : insertedObj m R c x ⟶ insertedObj m R c y := by
  classical
  by_cases hy : y = m
  · subst y
    by_cases hx : x = m
    · subst x
      exact 𝟙 _
    · exact (insertedOldIso m R c ⟨x, hx⟩).hom ≫
        c.ι.app ⟨x, lt_of_le_of_ne (leOfHom f) hx⟩ ≫ (insertedNewIso m R c).inv
  · have hx := predecessor_ne m hm (leOfHom f) hy
    exact (insertedOldIso m R c ⟨x, hx⟩).hom ≫
      R.map (homOfLE (show (⟨x, hx⟩ : Old m) ≤ ⟨y, hy⟩ from leOfHom f)) ≫
        (insertedOldIso m R c ⟨y, hy⟩).inv

/-- Insertion respects the original identities. -/
theorem insertedMap_id (x : J) : insertedMap m hm R c (𝟙 x) = 𝟙 (insertedObj m R c x) := by
  classical
  by_cases hx : x = m
  · subst x
    simp [insertedMap]
  · simp [insertedMap, hx]

/-- The full original composition law follows from strict cocone naturality. -/
theorem insertedMap_comp {x y z : J} (f : x ⟶ y) (g : y ⟶ z) :
    insertedMap m hm R c (f ≫ g) = insertedMap m hm R c f ≫ insertedMap m hm R c g := by
  classical
  by_cases hz : z = m
  · subst z
    by_cases hy : y = m
    · subst y
      by_cases hx : x = m
      · subst x; simp [insertedMap]
      · simp [insertedMap, hx]
    · have hx := predecessor_ne m hm (leOfHom f) hy
      simp only [insertedMap, dite_eq_right hx, dite_eq_right hy, dite_true,
        Category.assoc, Iso.inv_hom_id_assoc]
      let bx : Set.Iio m := ⟨x, lt_of_le_of_ne (leOfHom (f ≫ g)) hx⟩
      let by' : Set.Iio m := ⟨y, lt_of_le_of_ne (leOfHom g) hy⟩
      let a : bx ⟶ by' := homOfLE (leOfHom f)
      have ha : (boundaryInclusion m).map a =
          homOfLE (show (⟨x, hx⟩ : Old m) ≤ ⟨y, hy⟩ from leOfHom f) :=
        Subsingleton.elim _ _
      have hc := c.w a
      change R.map ((boundaryInclusion m).map a) ≫ c.ι.app by' = c.ι.app bx at hc
      rw [ha] at hc
      simpa only [Category.assoc] using congrArg
        (fun k ↦ (insertedOldIso m R c ⟨x, hx⟩).hom ≫
          k ≫ (insertedNewIso m R c).inv) hc.symm
  · have hy := predecessor_ne m hm (leOfHom g) hz
    have hx := predecessor_ne m hm (leOfHom f) hy
    simp only [insertedMap, dite_eq_right hx, dite_eq_right hy, dite_eq_right hz,
      Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc (R.map _), ← R.map_comp]
    rfl

/-- The complete original poset diagram with its genuinely attached maximal
vertex. No functoriality or commuting-face assertion is assumed. -/
def insertedDiagram : J ⥤ C where
  obj := insertedObj m R c
  map := insertedMap m hm R c
  map_id := insertedMap_id m hm R c
  map_comp := insertedMap_comp m hm R c

@[simp] theorem insertedDiagram_obj_old (x : Old m) :
    (insertedDiagram m hm R c).obj x.val = R.obj x := by
  have hx : x.val ≠ m := x.property
  simp [insertedDiagram, insertedObj, hx]

@[simp] theorem insertedDiagram_obj_new :
    (insertedDiagram m hm R c).obj m = c.pt := by
  simp [insertedDiagram, insertedObj]

/-- Insertion restricts to the original old diagram through the canonical
object equalities, on every old arrow simultaneously. -/
def insertedOldDiagramIso :
    FinitePosetLatching.inclusion (Old m) ⋙ insertedDiagram m hm R c ≅ R :=
  NatIso.ofComponents (fun x ↦ insertedOldIso m R c x) (by
    intro x y f
    have hy : y.val ≠ m := y.property
    change insertedMap m hm R c (homOfLE (show x.val ≤ y.val from leOfHom f)) ≫
      (insertedOldIso m R c y).hom = (insertedOldIso m R c x).hom ≫ R.map f
    simp only [insertedMap, dite_eq_right hy, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    congr 1)

variable (G : J ⥤ C)
  (p : R ⟶ FinitePosetLatching.restriction G (Old m)) (q : c.pt ⟶ G.obj m)

/-- Comparison with the original diagram, retaining every specified old map. -/
def insertedProjectionApp (x : J) : (insertedDiagram m hm R c).obj x ⟶ G.obj x := by
  classical
  by_cases hx : x = m
  · subst x
    exact (insertedNewIso m R c).hom ≫ q
  · exact (insertedOldIso m R c ⟨x, hx⟩).hom ≫ p.app ⟨x, hx⟩

variable (comm : ∀ x : Set.Iio m,
  c.ι.app x ≫ q = p.app ((boundaryInclusion m).obj x) ≫ G.map (homOfLE x.property.le))

/-- Strict agreement on the full lower boundary makes the original comparison
natural on the extended diagram. -/
def insertedProjection : insertedDiagram m hm R c ⟶ G where
  app := insertedProjectionApp m hm R c G p q
  naturality x y f := by
    classical
    change insertedMap m hm R c f ≫ insertedProjectionApp m hm R c G p q y =
      insertedProjectionApp m hm R c G p q x ≫ G.map f
    by_cases hy : y = m
    · subst y
      by_cases hx : x = m
      · subst x
        have hf : f = 𝟙 m := Subsingleton.elim _ _
        subst f
        simp [insertedMap, insertedProjectionApp]
      · simp only [insertedMap, insertedProjectionApp, dite_eq_right hx, dite_true,
          Category.assoc, Iso.inv_hom_id_assoc]
        exact congrArg (fun k ↦ (insertedOldIso m R c ⟨x, hx⟩).hom ≫ k)
          (comm ⟨x, lt_of_le_of_ne (leOfHom f) hx⟩)
    · have hx := predecessor_ne m hm (leOfHom f) hy
      simp only [insertedMap, insertedProjectionApp, dite_eq_right hx, dite_eq_right hy,
        Category.assoc, Iso.inv_hom_id_assoc]
      exact congrArg (fun k ↦ (insertedOldIso m R c ⟨x, hx⟩).hom ≫ k)
        (p.naturality (homOfLE (show (⟨x, hx⟩ : Old m) ≤ ⟨y, hy⟩ from leOfHom f)))

/-- The complete previously specified comparison is preserved on the old
subdiagram; it is not re-chosen independently at its vertices. -/
theorem insertedProjection_restrict :
    Functor.whiskerLeft (FinitePosetLatching.inclusion (Old m))
      (insertedProjection m hm R c G p q comm) =
        (insertedOldDiagramIso m hm R c).hom ≫ p := by
  ext x
  have hx : x.val ≠ m := x.property
  change insertedProjectionApp m hm R c G p q x.val = _
  simp only [insertedProjectionApp, dite_eq_right hx]
  rfl

/-- Weakness is inherited from the specified old comparison and the actual
new projection, with only equality identifications at the unchanged objects. -/
theorem insertedProjection_weak (W : CategoryTheory.Waldhausen.Structure C)
    (hp : ∀ x, W.weq (p.app x)) (hq : W.weq q) (x : J) :
    W.weq ((insertedProjection m hm R c G p q comm).app x) := by
  classical
  by_cases hx : x = m
  · subst x
    change W.weq (insertedProjectionApp m hm R c G p q m)
    simp only [insertedProjectionApp, dite_true]
    exact W.weq.comp_mem _ _ (W.weq_iso _ inferInstance) hq
  · change W.weq (insertedProjectionApp m hm R c G p q x)
    simp only [insertedProjectionApp, dite_eq_right hx]
    exact W.weq.comp_mem _ _ (W.weq_iso _ inferInstance) (hp ⟨x, hx⟩)

/-- A comparison on the old diagram gives the actual boundary cocone in the
original new target vertex. -/
def comparisonBoundaryCocone : Cocone (boundaryInclusion m ⋙ R) where
  pt := G.obj m
  ι := {
    app x := p.app ((boundaryInclusion m).obj x) ≫ G.map (homOfLE x.property.le)
    naturality x y f := by
      change R.map ((boundaryInclusion m).map f) ≫
        (p.app ((boundaryInclusion m).obj y) ≫ G.map (homOfLE y.property.le)) =
        (p.app ((boundaryInclusion m).obj x) ≫ G.map (homOfLE x.property.le)) ≫ 𝟙 (G.obj m)
      rw [Category.comp_id, ← Category.assoc, p.naturality, Category.assoc]
      change p.app ((boundaryInclusion m).obj x) ≫
        (G.map _ ≫ G.map _) = _
      rw [← G.map_comp]
      rfl }

end CategoryTheory.Limits.FinitePosetInsertion

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Limits.FinitePosetLatching
universe w w' z u v u' v'

namespace CategoryTheory.Limits.FinitePosetInsertion
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  {W : Structure C} (T : FunctorialFactorization W)
  (m : J) (hm : IsMax m) (G : J ⥤ C)
  (R : Old m ⥤ C) (p : R ⟶ FinitePosetLatching.restriction G (Old m))
  (c : Cocone (boundaryInclusion m ⋙ R)) (hc : IsColimit c)

/-- The genuine latching-to-original-vertex arrow from the previous comparison. -/
def replacementBoundaryArrow : Arrow C :=
  Arrow.mk (hc.desc (comparisonBoundaryCocone m R G p))

/-- The original factorization attaches the new vertex to the whole boundary. -/
def replacementBoundaryCocone : Cocone (boundaryInclusion m ⋙ R) :=
  c.extend (T.inclusion.app (replacementBoundaryArrow m G R p c hc))

/-- The actual new source diagram; all old data are inherited by insertion. -/
def replacementStep : J ⥤ C :=
  insertedDiagram m hm R (replacementBoundaryCocone T m G R p c hc)

/-- The weak original projection strictly respects every actual boundary leg. -/
theorem replacementBoundary_projection (x : Set.Iio m) :
    (replacementBoundaryCocone T m G R p c hc).ι.app x ≫
      T.projection.app (replacementBoundaryArrow m G R p c hc) =
        p.app ((boundaryInclusion m).obj x) ≫ G.map (homOfLE x.property.le) := by
  change (c.ι.app x ≫ T.inclusion.app (replacementBoundaryArrow m G R p c hc)) ≫
    T.projection.app (replacementBoundaryArrow m G R p c hc) = _
  rw [Category.assoc, T.factorization]
  exact hc.fac (comparisonBoundaryCocone m R G p) x

/-- The coherent weak comparison to the original whole diagram. -/
def replacementStepProjection : replacementStep T m hm G R p c hc ⟶ G :=
  insertedProjection m hm R (replacementBoundaryCocone T m G R p c hc) G p
    (T.projection.app (replacementBoundaryArrow m G R p c hc))
    (replacementBoundary_projection T m G R p c hc)

/-- The whole previously constructed old diagram is retained under canonical
object equalities, not merely its individual isomorphism classes. -/
def replacementStepOldIso :
    FinitePosetLatching.inclusion (Old m) ⋙ replacementStep T m hm G R p c hc ≅ R :=
  insertedOldDiagramIso m hm R (replacementBoundaryCocone T m G R p c hc)

/-- Restriction recovers the original specified old comparison simultaneously
on all of its vertices and arrows. -/
theorem replacementStepProjection_restrict :
    Functor.whiskerLeft (FinitePosetLatching.inclusion (Old m))
      (replacementStepProjection T m hm G R p c hc) =
        (replacementStepOldIso T m hm G R p c hc).hom ≫ p :=
  insertedProjection_restrict m hm R (replacementBoundaryCocone T m G R p c hc) G p
    (T.projection.app (replacementBoundaryArrow m G R p c hc))
    (replacementBoundary_projection T m G R p c hc)

/-- Every projection component is weak by the actual original factorization;
no saturation or higher-filling assertion is needed for this step. -/
theorem replacementStepProjection_weak (hp : ∀ x, W.weq (p.app x)) (x : J) :
    W.weq ((replacementStepProjection T m hm G R p c hc).app x) :=
  insertedProjection_weak m hm R (replacementBoundaryCocone T m G R p c hc) G p
    (T.projection.app (replacementBoundaryArrow m G R p c hc))
    (replacementBoundary_projection T m G R p c hc) W hp (T.weak _) x

/-- The actual map from the previously computed latching colimit into the new
vertex. Its target is the literal newly inserted original-diagram object. -/
def replacementStepLatching : c.pt ⟶ (replacementStep T m hm G R p c hc).obj m :=
  T.inclusion.app (replacementBoundaryArrow m G R p c hc) ≫
    (insertedNewIso m R (replacementBoundaryCocone T m G R p c hc)).inv

/-- The new latching map is a genuine source cofibration. -/
theorem replacementStepLatching_cof :
    W.cof (replacementStepLatching T m hm G R p c hc) :=
  W.cof.comp_mem _ _ (T.cofibration _) (W.cof_iso _ inferInstance)

/-- Every original boundary leg agrees strictly with the map of the inserted
diagram after the canonical unchanged-old-object identification. -/
theorem replacementStepLatching_leg (x : Set.Iio m) :
    c.ι.app x ≫ replacementStepLatching T m hm G R p c hc =
      (replacementStepOldIso T m hm G R p c hc).inv.app ((boundaryInclusion m).obj x) ≫
        (replacementStep T m hm G R p c hc).map (homOfLE x.property.le) := by
  have hx : x.val ≠ m := ne_of_lt x.property
  change c.ι.app x ≫
      (T.inclusion.app (replacementBoundaryArrow m G R p c hc) ≫
        (insertedNewIso m R (replacementBoundaryCocone T m G R p c hc)).inv) =
    (insertedOldIso m R (replacementBoundaryCocone T m G R p c hc)
      ⟨x.val, hx⟩).inv ≫
      insertedMap m hm R (replacementBoundaryCocone T m G R p c hc)
        (homOfLE x.property.le)
  simp only [insertedMap, dite_true, dite_eq_right hx,
    Iso.inv_hom_id_assoc]
  simp only [replacementBoundaryCocone, Cocone.extend, NatTrans.comp_app, Category.assoc]
  rfl

/-- The new latching projection factors exactly the original boundary descent. -/
theorem replacementStepLatching_projection :
    replacementStepLatching T m hm G R p c hc ≫
      (replacementStepProjection T m hm G R p c hc).app m =
        (replacementBoundaryArrow m G R p c hc).hom := by
  change (T.inclusion.app (replacementBoundaryArrow m G R p c hc) ≫
      (insertedNewIso m R (replacementBoundaryCocone T m G R p c hc)).inv) ≫
    insertedProjectionApp m hm R (replacementBoundaryCocone T m G R p c hc) G p
      (T.projection.app (replacementBoundaryArrow m G R p c hc)) m = _
  simp only [insertedProjectionApp, dite_true, Category.assoc, Iso.inv_hom_id_assoc]
  exact T.factorization _

/-- The old vertex objects are literally unchanged by the finite induction step. -/
theorem replacementStep_obj_old (x : Old m) :
    (replacementStep T m hm G R p c hc).obj x.val = R.obj x :=
  insertedDiagram_obj_old m hm R (replacementBoundaryCocone T m G R p c hc) x

end CategoryTheory.Limits.FinitePosetInsertion

namespace CategoryTheory.Limits.FinitePosetInsertion
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]
  (m : J) (hm : IsMax m) (R : Old m ⥤ C)
  (c : Cocone (boundaryInclusion m ⋙ R)) {M : C} (k : c.pt ⟶ M)

/-- The intersection in the actual maximal-vertex lower cover is precisely
its strict boundary, including its original order arrows. -/
def maximalIntersectionIso : (Old m ∩ Set.Iic m : Set J) ≃o Set.Iio m where
  toFun x := ⟨x.val, lt_of_le_of_ne x.property.2 x.property.1⟩
  invFun x := ⟨x.val, ne_of_lt x.property, x.property.le⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The old canonical identification reindexes the original entire boundary
of the inserted diagram, not just separate vertices. -/
def insertedBoundaryIso :
    restriction (insertedDiagram m hm R (c.extend k)) (Set.Iio m) ≅
      boundaryInclusion m ⋙ R :=
  Functor.isoWhiskerLeft (boundaryInclusion m)
    (insertedOldDiagramIso m hm R (c.extend k))

/-- The old boundary colimit cocone, viewed on the literal inserted diagram. -/
def insertedBoundaryCocone :
    Cocone (restriction (insertedDiagram m hm R (c.extend k)) (Set.Iio m)) :=
  (Cocone.precompose (insertedBoundaryIso m hm R c k).hom).obj c

/-- The overlap cocone in the actual two-lower-ideal cover. -/
def insertedIntersectionCocone :
    Cocone (restriction (insertedDiagram m hm R (c.extend k))
      (Old m ∩ Set.Iic m)) :=
  (insertedBoundaryCocone m hm R c k).whisker (maximalIntersectionIso m).equivalence.functor

/-- The actual latching cofibration lands in the literal new object. -/
def insertedLatching : c.pt ⟶ (insertedDiagram m hm R (c.extend k)).obj m :=
  k ≫ (insertedNewIso m R (c.extend k)).inv

/-- All overlap legs factor strictly through the actual attaching map. -/
theorem insertedIntersection_leg (x : (Old m ∩ Set.Iic m : Set J)) :
    (insertedIntersectionCocone m hm R c k).ι.app x ≫ insertedLatching m hm R c k =
      (principalCocone (insertedDiagram m hm R (c.extend k)) m).ι.app
        ⟨x.val, x.property.2⟩ := by
  have hx : x.val ≠ m := x.property.1
  change ((insertedOldIso m R (c.extend k) ⟨x.val, hx⟩).hom ≫ c.ι.app ⟨x.val, lt_of_le_of_ne
    x.property.2 hx⟩) ≫
    (k ≫ (insertedNewIso m R (c.extend k)).inv) =
      insertedMap m hm R (c.extend k) (homOfLE x.property.2)
  simp only [insertedMap, dite_true, dite_eq_right hx, Cocone.extend,
    NatTrans.comp_app, Functor.const_map_app, Category.assoc]

variable (F : C ⥤ D)
  (W : Structure C) (V : Structure D) (hF : IsExact W.cof W.weq V.cof V.weq F)

include hF in
/-- An actual cofibrant boundary attachment constructs a preserved colimit for
the whole inserted original diagram. No full-diagram colimit is assumed. -/
theorem insertedDiagram_hasPreservedColimit
    (hc : IsColimit c) (hFc : IsColimit (F.mapCocone c))
    (hR : HasPreservedColimit F R) (hk : W.cof k) :
    HasPreservedColimit F (insertedDiagram m hm R (c.extend k)) := by
  let H := insertedDiagram m hm R (c.extend k)
  obtain ⟨cA, ⟨hcA⟩, ⟨hFA⟩⟩ :=
    hR.ofIso F (insertedOldDiagramIso m hm R (c.extend k))
  let cB := principalCocone H m
  let cI := insertedIntersectionCocone m hm R c k
  let hcBoundary := (IsColimit.precomposeHomEquiv (insertedBoundaryIso m hm R c k) c).symm hc
  let hcI : IsColimit cI := hcBoundary.whiskerEquivalence (maximalIntersectionIso m).equivalence
  let hFBoundary := (IsColimit.precomposeHomEquiv
    (Functor.isoWhiskerRight (insertedBoundaryIso m hm R c k) F) (F.mapCocone c)).symm hFc
  let hFBoundary' : IsColimit (F.mapCocone (insertedBoundaryCocone m hm R c k)) :=
    hFBoundary.ofIsoColimit F.mapCoconePrecompose.symm
  let hFI : IsColimit (F.mapCocone cI) :=
    hFBoundary'.whiskerEquivalence (maximalIntersectionIso m).equivalence
  have hj : intersectionToRight cB cI hcI = insertedLatching m hm R c k := by
    apply hcI.hom_ext
    intro x
    rw [intersectionToRight, hcI.fac]
    exact (insertedIntersection_leg m hm R c k x).symm
  have hcof : W.cof (intersectionToRight cB cI hcI) := by
    rw [hj]
    exact W.cof.comp_mem _ _ hk (W.cof_iso _ inferInstance)
  exact exists_preserved_gluedColimit cA cB cI
    (maximal_lower_cover m) (complement_singleton_isLowerSet m hm) (isLowerSet_Iic m)
    F W V hF hcA (principalCoconeIsColimit H m) hcI (Or.inr hcof)
    hFA (mappedPrincipalCoconeIsColimit H F m) hFI

end CategoryTheory.Limits.FinitePosetInsertion

end

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Limits.FinitePosetLatching
universe w w' z u v u' v'

namespace CategoryTheory.Limits.FinitePosetInsertion
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (W : Structure C) (V : Structure D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

include hF in
/-- A maximal attachment's literal boundary map, with actual colimit universal
properties, constructs the preserved colimit of the original whole diagram. -/
theorem maximalAttachment_hasPreservedColimit (G : J ⥤ C) (m : J) (hm : IsMax m)
    (hOld : HasPreservedColimit F (restriction G (Old m)))
    (c : Cocone (restriction G (Set.Iio m)))
    (hc : IsColimit c) (hFc : IsColimit (F.mapCocone c))
    (k : c.pt ⟶ G.obj m) (hk : W.cof k)
    (hleg : ∀ x : Set.Iio m, c.ι.app x ≫ k = G.map (homOfLE x.property.le)) :
    HasPreservedColimit F G := by
  obtain ⟨cA, ⟨hcA⟩, ⟨hFA⟩⟩ := hOld
  let cB := principalCocone G m
  let cI := c.whisker (maximalIntersectionIso m).equivalence.functor
  let hcI := hc.whiskerEquivalence (maximalIntersectionIso m).equivalence
  let hFI := hFc.whiskerEquivalence (maximalIntersectionIso m).equivalence
  have hj : intersectionToRight cB cI hcI = k := by
    apply hcI.hom_ext
    intro x
    rw [intersectionToRight, hcI.fac]
    exact (hleg ⟨x.val, lt_of_le_of_ne x.property.2 x.property.1⟩).symm
  have hcof : W.cof (intersectionToRight cB cI hcI) := hj ▸ hk
  exact exists_preserved_gluedColimit cA cB cI
    (maximal_lower_cover m) (complement_singleton_isLowerSet m hm) (isLowerSet_Iic m)
    F W V hF hcA (principalCoconeIsColimit G m) hcI (Or.inr hcof)
    hFA (mappedPrincipalCoconeIsColimit G F m) hFI

/-- The finite induction invariant: actual preserved colimits on all lower
ideals. No weak-equivalence or contraction endpoint is part of this invariant. -/
def HasLowerPreservedColimits (G : J ⥤ C) : Prop :=
  ∀ A : Set J, IsLowerSet A → HasPreservedColimit F (restriction G A)

variable (m : J) (A : Set J)

/-- The old portion of a lower ideal, indexed in the unchanged old poset. -/
def oldPart : Set (Old m) := {x | x.val ∈ A}

/-- Lower ideals stay lower on the old subposet. -/
theorem oldPart_isLowerSet (hA : IsLowerSet A) : IsLowerSet (oldPart m A) :=
  fun _ _ h hx ↦ hA h hx

/-- A lower ideal which omits the new vertex is entirely old. -/
def omittingOldIso (hmA : m ∉ A) : A ≃o oldPart m A where
  toFun x := ⟨⟨x.val, fun h ↦ hmA (h ▸ x.property)⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Removing the distinguished vertex inside an ideal gives its actual old
portion in the original ambient poset. -/
def containingOldIso (hmA : m ∈ A) : Old (⟨m, hmA⟩ : A) ≃o oldPart m A where
  toFun x := ⟨⟨x.val.val, fun h ↦ x.property (Subtype.ext h)⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, fun h ↦ x.val.property (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- An ideal containing the new vertex contains its entire strict boundary. -/
def containingBoundaryIso (hA : IsLowerSet A) (hmA : m ∈ A) :
    Set.Iio (⟨m, hmA⟩ : A) ≃o Set.Iio m where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, hA x.property.le hmA⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- Ambient maximality also holds inside any containing ideal. -/
theorem maximal_in_ideal (hm : IsMax m) (hmA : m ∈ A) : IsMax (⟨m, hmA⟩ : A) := by
  intro x hx
  exact hm hx

variable (hm : IsMax m) (R : Old m ⥤ C)
  (c : Cocone (boundaryInclusion m ⋙ R)) {M : C} (k : c.pt ⟶ M)

include hF in
/-- A single genuine cofibrant attachment simultaneously preserves the actual
colimit invariant on every lower ideal, including ideals which contain only
part of the unchanged diagram. -/
theorem insertedDiagram_hasLowerPreservedColimits
    (hc : IsColimit c) (hFc : IsColimit (F.mapCocone c))
    (hR : HasLowerPreservedColimits F R) (hk : W.cof k) :
    HasLowerPreservedColimits F (insertedDiagram m hm R (c.extend k)) := by
  intro A hA
  classical
  let H := insertedDiagram m hm R (c.extend k)
  have hOldPart := hR (oldPart m A) (oldPart_isLowerSet m A hA)
  by_cases hmA : m ∈ A
  · let mA : A := ⟨m, hmA⟩
    let eOld := (containingOldIso m A hmA).equivalence
    let oldEmb := eOld.functor ⋙ inclusion (oldPart m A)
    have hOld : HasPreservedColimit F (restriction (restriction H A) (Old mA)) :=
      (hOldPart.whisker F eOld).ofIso F
        (Functor.isoWhiskerLeft oldEmb (insertedOldDiagramIso m hm R (c.extend k)))
    let eBoundary := (containingBoundaryIso m A hA hmA).equivalence
    let cb := insertedBoundaryCocone m hm R c k
    let cbA : Cocone (restriction (restriction H A) (Set.Iio mA)) :=
      cb.whisker eBoundary.functor
    let hcb := (IsColimit.precomposeHomEquiv (insertedBoundaryIso m hm R c k) c).symm hc
    let hFcb : IsColimit (F.mapCocone cb) :=
      ((IsColimit.precomposeHomEquiv
        (Functor.isoWhiskerRight (insertedBoundaryIso m hm R c k) F)
        (F.mapCocone c)).symm hFc).ofIsoColimit F.mapCoconePrecompose.symm
    apply maximalAttachment_hasPreservedColimit F W V hF (restriction H A) mA
      (maximal_in_ideal m A hm hmA) hOld cbA
      (hcb.whiskerEquivalence eBoundary) (hFcb.whiskerEquivalence eBoundary)
      (insertedLatching m hm R c k)
      (W.cof.comp_mem _ _ hk (W.cof_iso _ inferInstance))
    intro x
    exact insertedIntersection_leg m hm R c k
      ⟨x.val.val, ne_of_lt x.property, x.property.le⟩
  · let eOld := (omittingOldIso m A hmA).equivalence
    let oldEmb := eOld.functor ⋙ inclusion (oldPart m A)
    exact (hOldPart.whisker F eOld).ofIso F
      (Functor.isoWhiskerLeft oldEmb (insertedOldDiagramIso m hm R (c.extend k)))

end CategoryTheory.Limits.FinitePosetInsertion

namespace CategoryTheory.Limits.FinitePosetInsertion
variable {J : Type w} [PartialOrder J] {C : Type u} [Category.{v} C]
  {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (W : Structure C) (V : Structure D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- Reindex the whole poset as its literal full lower ideal. -/
def fullIdealIso : J ≃o (Set.univ : Set J) where
  toFun x := ⟨x, Set.mem_univ x⟩
  invFun x := x.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- The all-lower-ideals invariant includes the actual original whole diagram. -/
theorem HasLowerPreservedColimits.whole {G : J ⥤ C}
    (h : HasLowerPreservedColimits F G) : HasPreservedColimit F G :=
  (h Set.univ isLowerSet_univ).whisker F (fullIdealIso (J := J)).equivalence

/-- The strict boundary is an actual lower ideal of the unchanged old poset. -/
theorem HasLowerPreservedColimits.boundary (m : J) {R : Old m ⥤ C}
    (h : HasLowerPreservedColimits F R) :
    HasPreservedColimit F (boundaryInclusion m ⋙ R) :=
  (h (oldPart m (Set.Iio m)) (oldPart_isLowerSet m (Set.Iio m) (isLowerSet_Iio m))).whisker
    F (omittingOldIso m (Set.Iio m) (lt_irrefl m)).equivalence

/-- The literal zero cocone on an empty diagram. -/
def emptyZeroCocone [IsEmpty J] (G : J ⥤ C) : Cocone G where
  pt := W.zero
  ι := { app x := isEmptyElim x, naturality x := isEmptyElim x }

include hF in
/-- Exactness preserves the actual empty colimit, including the empty-poset
base case of the finite induction. -/
theorem empty_hasPreservedColimit [IsEmpty J] (G : J ⥤ C) :
    HasPreservedColimit F G := by
  let c := emptyZeroCocone W G
  refine ⟨c, ⟨?_⟩, ⟨?_⟩⟩
  · exact {
      desc s := W.isZero.to_ s.pt
      fac s x := isEmptyElim x
      uniq s f hf := W.isZero.eq_of_src _ _ }
  · exact {
      desc s := (hF.zero W.isZero).to_ s.pt
      fac s x := isEmptyElim x
      uniq s f hf := (hF.zero W.isZero).eq_of_src _ _ }

include hF in
/-- Actual finite induction constructs a coherent weak replacement with
preserved colimits on every lower ideal. The original functor and original
source diagram appear literally in the comparison and universal properties. -/
theorem exists_lowerPreservedReplacement (T : FunctorialFactorization W)
    [Finite J] (G : J ⥤ C) :
    ∃ (R : J ⥤ C) (p : R ⟶ G),
      (∀ x, W.weq (p.app x)) ∧ HasLowerPreservedColimits F R := by
  classical
  suffices ∀ n : ℕ, ∀ (K : Type w) [PartialOrder K] [Finite K], Nat.card K = n →
      ∀ G : K ⥤ C, ∃ (R : K ⥤ C) (p : R ⟶ G),
        (∀ x, W.weq (p.app x)) ∧ HasLowerPreservedColimits F R by
    exact this (Nat.card J) J rfl G
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro K _ _ hcard G
    cases isEmpty_or_nonempty K with
    | inl hEmpty =>
      let _ := hEmpty
      refine ⟨G, 𝟙 G, fun x ↦ isEmptyElim x, ?_⟩
      intro A hA
      exact empty_hasPreservedColimit F W V hF (restriction G A)
    | inr hNonempty =>
      let _ := hNonempty
      obtain ⟨m, hm⟩ := (Set.finite_univ : (Set.univ : Set K).Finite).exists_maximal
        (Set.univ_nonempty)
      have hm' : IsMax m := fun x hmx ↦ hm.2 (Set.mem_univ x) hmx
      have hlt : Nat.card (Old m) < n := by
        let _ := Fintype.ofFinite K
        let _ := Fintype.ofFinite (Old m)
        rw [← hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_lt (x := m) (by simp [Old])
      obtain ⟨R, p, hp, hR⟩ := ih (Nat.card (Old m)) hlt (Old m) rfl
        (restriction G (Old m))
      obtain ⟨c, ⟨hc⟩, ⟨hFc⟩⟩ := hR.boundary F m
      refine ⟨replacementStep T m hm' G R p c hc,
        replacementStepProjection T m hm' G R p c hc,
        replacementStepProjection_weak T m hm' G R p c hc hp, ?_⟩
      exact insertedDiagram_hasLowerPreservedColimits F W V hF m hm' R c
        (T.inclusion.app (replacementBoundaryArrow m G R p c hc)) hc hFc hR (T.cofibration _)

end CategoryTheory.Limits.FinitePosetInsertion

end
