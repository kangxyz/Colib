/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory
public import Colib.CategoryTheory.Waldhausen.Rows.Reindex
public import Colib.CategoryTheory.Waldhausen.Rows.ReindexExact

/-! # Nested weak classes on the exact same quotient-row category

The coarse structure uses the existing fine quotient-row objects, every
original natural transformation, the literal fine Reedy cofibration class,
and the literal chosen zero row. Only weak equivalences change to the
pointwise coarse class. Gluing is derived from the actual component pushouts.
No row-cylinder, factorization, or realization property is assumed.


Implementation provenance:
`Quillen/Waldhausen/Fibration/Rows/NestedWeakEquivalences.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The original maps,
hypotheses, chosen zero objects and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.Fibration.RowWeakEquivalences
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V)

/-- Coarse weakness of the unchanged original quotient-row map is pointwise. -/
def coarseWeak (n : SimplexCategory) : MorphismProperty (QuotientRows.Obj V n) :=
  fun _ _ f ↦ ∀ p, N.coarse.weq (f.hom.app p)

instance coarseWeak_multiplicative (n : SimplexCategory) : (coarseWeak N n).IsMultiplicative where
  id_mem _ _ := N.coarse.weq.id_mem _
  comp_mem _ _ hf hg p := N.coarse.weq.comp_mem _ _ (hf p) (hg p)

/-- The actual coarse Waldhausen structure on the original fine row object type. -/
def coarseStructure (n : SimplexCategory) : Structure (QuotientRows.Obj V n) where
  zero := QuotientRows.zero V n
  isZero := QuotientRows.isZero V n
  cof := QuotientRows.cof V n
  weq := coarseWeak N n
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := QuotientRows.cof_iso V n
  weq_iso := by
    intro F G f hf p
    let : IsIso f := hf
    exact N.coarse.weq_iso _ (inferInstance : IsIso ((QuotientRows.evaluation V p).map f))
  cof_zero := QuotientRows.cof_zero V n
  pushout_exists := (QuotientRows.waldhausenStructure V n).pushout_exists
  cof_pushout := (QuotientRows.waldhausenStructure V n).cof_pushout
  gluing := by
    intro A B D P A' B' D' P' f g i j f' g' i' j' a b d p hf hf' h h' ef eg ei ej ha hb hd q
    exact N.coarse.gluing (a.hom.app q) (b.hom.app q) (d.hom.app q) (p.hom.app q)
      (by rw [N.cof_eq]; exact QuotientRows.cof_app V hf q)
      (by rw [N.cof_eq]; exact QuotientRows.cof_app V hf' q)
      (QuotientRows.pointwise_of_isPushout V hf h q)
      (QuotientRows.pointwise_of_isPushout V hf' h' q)
      (congrArg (fun k ↦ k.hom.app q) ef) (congrArg (fun k ↦ k.hom.app q) eg)
      (congrArg (fun k ↦ k.hom.app q) ei) (congrArg (fun k ↦ k.hom.app q) ej)
      (ha q) (hb q) (hd q)

/-- The two row cofibration classes are literally the same actual Reedy class. -/
@[simp] theorem coarseStructure_cof (n : SimplexCategory) :
    (coarseStructure N n).cof = (QuotientRows.waldhausenStructure V n).cof := rfl

/-- The two row structures retain exactly the original chosen zero. -/
@[simp] theorem coarseStructure_zero (n : SimplexCategory) :
    (coarseStructure N n).zero = (QuotientRows.waldhausenStructure V n).zero := rfl

@[simp] theorem coarseStructure_weq_iff {n : SimplexCategory} {F G : QuotientRows.Obj V n}
    (f : F ⟶ G) : (coarseStructure N n).weq f ↔ ∀ p, N.coarse.weq (f.hom.app p) := Iff.rfl

/-- Genuine nested weak classes on the unchanged fine quotient-row category. -/
def nested (n : SimplexCategory) : NestedWeakEquivalences (QuotientRows.waldhausenStructure V n)
    where
  coarse := coarseStructure N n
  cof_eq := rfl
  zero_eq := rfl
  le_weq := by
    intro F G f hf p
    exact N.le_weq _ (hf p)

/-- Evaluation is genuinely exact from the new coarse row structure to the original coarse
structure. -/
theorem evaluation_coarse_exact {n : SimplexCategory} (p : Interval n) :
    IsExact (coarseStructure N n).cof (coarseStructure N n).weq N.coarse.cof N.coarse.weq
      (QuotientRows.evaluation V p) where
  zero h := QuotientRows.evaluation_isZero V h p
  cofibration _ h := by rw [N.cof_eq]; exact QuotientRows.cof_app V h p
  weak _ h := h p
  pushout hf h := QuotientRows.pointwise_of_isPushout V hf h p

/-- Every original ordinal reindexing is genuinely exact for the coarse row structures. -/
theorem reindex_coarse_exact {m n : SimplexCategory} (α : m ⟶ n) :
    IsExact (coarseStructure N n).cof (coarseStructure N n).weq
      (coarseStructure N m).cof (coarseStructure N m).weq (QuotientRows.reindex V α) where
  zero := (QuotientRows.reindex_exact V α).zero
  cofibration := (QuotientRows.reindex_exact V α).cofibration
  weak _ h p := h ((QuotientRows.indexMap α).obj p)
  pushout := (QuotientRows.reindex_exact V α).pushout

/-- Coarse two-out-of-three is inherited componentwise; no fine saturation is needed. -/
instance coarseStructure_twoOutOfThree (n : SimplexCategory)
    [N.coarse.weq.HasTwoOutOfThreeProperty] :
    (coarseStructure N n).weq.HasTwoOutOfThreeProperty where
  comp_mem _ _ hf hg p := N.coarse.weq.comp_mem _ _ (hf p) (hg p)
  of_postcomp f g hg hfg p := N.coarse.weq.of_postcomp (f.hom.app p) (g.hom.app p) (hg p) (hfg p)
  of_precomp f g hf hfg p := N.coarse.weq.of_precomp (f.hom.app p) (g.hom.app p) (hf p) (hfg p)

end CategoryTheory.Waldhausen.Fibration.RowWeakEquivalences
