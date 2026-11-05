/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.CategoryTheory.ExactCategory.Functor.SerreLocalization
public import Colib.KTheory.GrothendieckGroup.AbelianNaturality
public import Colib.KTheory.GrothendieckGroup.SerreSubgroup

/-!
# Algebraic Grothendieck-group localization by a Serre class

The conflation presentation is compared with the pinned Stacks group, its
object-generated Serre subgroup with the inclusion image, and the resulting
quotient with Stacks 02MX (1). The composite equivalence is proved to be the
actual map induced by localization, not just an abstract group isomorphism.

The map, quotient lift and object-class interfaces are adapted from
`Quillen/Localization/Serre/Localization.lean` and
`Quillen/Localization/Serre/GrothendieckExactness.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Their independent object/hom universes
and abelian hypotheses are retained. Exactness itself reuses the pinned Stacks
proof through explicit generator-preserving comparisons. No Q-construction or
homotopical K-group occurs here.
-/

@[expose] public noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory.Limits

namespace CategoryTheory.ExactCategory.SerreLocalization

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
  (P : ObjectProperty C)

/-- The source object's class modulo classes of objects in the Serre class. -/
def classModuloSerre (X : C) :
    (abelianExactStructure C).GrothendieckGroup ⧸ serreSubgroup P :=
  QuotientAddGroup.mk' (serreSubgroup P) ((abelianExactStructure C).grothendieckClass X)

lemma classModuloSerre_eq_zero {X : C} (hX : P X) : classModuloSerre P X = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).2
  exact AddSubgroup.subset_closure ⟨X, hX, rfl⟩

lemma classModuloSerre_additive {S : ShortComplex C} (hS : S.ShortExact) :
    classModuloSerre P S.X₂ = classModuloSerre P S.X₁ + classModuloSerre P S.X₃ := by
  unfold classModuloSerre
  rw [(abelianExactStructure C).grothendieckClass_additive hS, map_add]

variable [P.IsSerreClass]

lemma classModuloSerre_eq_of_mono {X Y : C} (f : X ⟶ Y) [Mono f]
    (hf : P.epiModSerre f) : classModuloSerre P X = classModuloSerre P Y := by
  have hS : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact f }
  have h := classModuloSerre_additive P hS
  change classModuloSerre P Y = classModuloSerre P X + classModuloSerre P (cokernel f) at h
  rw [classModuloSerre_eq_zero P hf, add_zero] at h
  exact h.symm

lemma classModuloSerre_eq_of_epi {X Y : C} (f : X ⟶ Y) [Epi f]
    (hf : P.monoModSerre f) : classModuloSerre P X = classModuloSerre P Y := by
  have hS : (ShortComplex.mk (kernel.ι f) f (kernel.condition f)).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact f }
  have h := classModuloSerre_additive P hS
  change classModuloSerre P X = classModuloSerre P (kernel f) + classModuloSerre P Y at h
  rw [classModuloSerre_eq_zero P hf, zero_add] at h
  exact h

/-- An isomorphism modulo the Serre class identifies the two object classes
in the quotient algebraic Grothendieck group. -/
lemma classModuloSerre_eq_of_isoModSerre {X Y : C} (f : X ⟶ Y)
    (hf : P.isoModSerre f) : classModuloSerre P X = classModuloSerre P Y :=
  (classModuloSerre_eq_of_epi P (Abelian.factorThruImage f)
    hf.1.isoModSerre_factorThruImage.1).trans
    (classModuloSerre_eq_of_mono P (Abelian.image.ι f)
      hf.2.isoModSerre_image_ι.2)


/-- The exact source Serre quotient presentation is identified with the quotient
by the inclusion image in the pinned Stacks presentation. -/
def serreQuotientComparison :
    (abelianExactStructure C).GrothendieckGroup ⧸ serreSubgroup P ≃+
      CategoryTheory.GrothendieckGroup C ⧸
        (CategoryTheory.GrothendieckGroup.map P.ι P.shortExact_map_ι).range :=
  QuotientAddGroup.congr _ _ (abelianGrothendieckEquiv C)
    (map_serreSubgroup_eq_range_of_isSerreClass P)

/-- The quotient comparison identifies the actual source object classes. -/
@[simp]
lemma serreQuotientComparison_class (X : C) :
    serreQuotientComparison P (classModuloSerre P X) =
      QuotientAddGroup.mk (CategoryTheory.GrothendieckGroup.of X) := by
  change QuotientAddGroup.mk
      (abelianGrothendieckEquiv C ((abelianExactStructure C).grothendieckClass X)) = _
  rw [abelianGrothendieckEquiv_class]

variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
  (L : C ⥤ D) [L.IsLocalization P.isoModSerre] [L.Additive]

/-- The algebraic map induced by the actual localization functor. -/
def grothendieckMap :
    (abelianExactStructure C).GrothendieckGroup →+
      (abelianExactStructure D).GrothendieckGroup :=
  (ExactFunctor.serreLocalization P L).grothendieckMap

@[simp]
lemma grothendieckMap_class (X : C) :
    grothendieckMap P L ((abelianExactStructure C).grothendieckClass X) =
      (abelianExactStructure D).grothendieckClass (L.obj X) :=
  (ExactFunctor.serreLocalization P L).grothendieckMap_class X

/-- Objects in the Serre class have zero localized class. -/
lemma grothendieckMap_class_eq_zero {X : C} (hX : P X) :
    grothendieckMap P L ((abelianExactStructure C).grothendieckClass X) = 0 := by
  rw [grothendieckMap_class]
  exact (abelianExactStructure D).grothendieckClass_of_isZero
    ((ObjectProperty.SerreClassLocalization.isZero_obj_iff L P X).2 hX)

lemma serreSubgroup_le_ker : serreSubgroup P ≤ (grothendieckMap P L).ker := by
  apply (AddSubgroup.closure_le _).2
  rintro a ⟨X, hX, rfl⟩
  exact grothendieckMap_class_eq_zero P L hX

/-- The actual localization map descends through its Serre relations. -/
def grothendieckMapModuloSerre :
    (abelianExactStructure C).GrothendieckGroup ⧸ serreSubgroup P →+
      (abelianExactStructure D).GrothendieckGroup :=
  QuotientAddGroup.lift (serreSubgroup P) (grothendieckMap P L)
    (serreSubgroup_le_ker P L)

@[simp]
lemma grothendieckMapModuloSerre_mk (x : (abelianExactStructure C).GrothendieckGroup) :
    grothendieckMapModuloSerre P L (QuotientAddGroup.mk x) = grothendieckMap P L x := rfl

/-- Stacks 02MX transported through the specified object-generator comparisons. -/
def grothendieckModuloSerreEquiv :
    (abelianExactStructure C).GrothendieckGroup ⧸ serreSubgroup P ≃+
      (abelianExactStructure D).GrothendieckGroup :=
  (serreQuotientComparison P).trans
    ((ObjectProperty.SerreClassLocalization.grothendieckGroupEquiv L P
      P.shortExact_map_ι (ObjectProperty.SerreClassLocalization.shortExact_map L P)).trans
        (abelianGrothendieckEquiv D).symm)

/-- The transported equivalence sends the class of `X` to the class of `L.obj X`. -/
@[simp]
lemma grothendieckModuloSerreEquiv_class (X : C) :
    grothendieckModuloSerreEquiv P L (classModuloSerre P X) =
      (abelianExactStructure D).grothendieckClass (L.obj X) := by
  change (abelianGrothendieckEquiv D).symm
      (ObjectProperty.SerreClassLocalization.grothendieckGroupEquiv L P
        P.shortExact_map_ι (ObjectProperty.SerreClassLocalization.shortExact_map L P)
          (serreQuotientComparison P (classModuloSerre P X))) = _
  rw [serreQuotientComparison_class,
    ObjectProperty.SerreClassLocalization.grothendieckGroupEquiv_mk_of,
    abelianGrothendieckEquiv_symm_of]

/-- The equivalence composed with the actual quotient projection is the actual
localization map on the conflation presentation. -/
lemma grothendieckModuloSerreEquiv_comp_mk :
    (grothendieckModuloSerreEquiv P L).toAddMonoidHom.comp
      (QuotientAddGroup.mk' (serreSubgroup P)) = grothendieckMap P L := by
  apply (abelianExactStructure C).grothendieck_hom_ext
  intro X
  change grothendieckModuloSerreEquiv P L (classModuloSerre P X) =
    grothendieckMap P L ((abelianExactStructure C).grothendieckClass X)
  exact (grothendieckModuloSerreEquiv_class P L X).trans (grothendieckMap_class P L X).symm

lemma grothendieckModuloSerreEquiv_mk (x : (abelianExactStructure C).GrothendieckGroup) :
    grothendieckModuloSerreEquiv P L (QuotientAddGroup.mk x) = grothendieckMap P L x :=
  DFunLike.congr_fun (grothendieckModuloSerreEquiv_comp_mk P L) x

/-- The constructed equivalence agrees with the original quotient lift. -/
lemma grothendieckModuloSerreEquiv_toAddMonoidHom :
    (grothendieckModuloSerreEquiv P L).toAddMonoidHom = grothendieckMapModuloSerre P L := by
  apply AddMonoidHom.ext
  intro q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (serreSubgroup P) q
  exact grothendieckModuloSerreEquiv_mk P L x

/-- The kernel consists exactly of the source classes generated by Serre objects. -/
theorem grothendieckMap_ker : (grothendieckMap P L).ker = serreSubgroup P := by
  rw [← grothendieckModuloSerreEquiv_comp_mk P L,
    AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.ker_addEquiv_comp,
    QuotientAddGroup.ker_mk']

/-- The actual localization map on the algebraic presentation is surjective. -/
theorem grothendieckMap_surjective : Function.Surjective (grothendieckMap P L) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk'_surjective (serreSubgroup P)
    ((grothendieckModuloSerreEquiv P L).symm y)
  refine ⟨x, ?_⟩
  change QuotientAddGroup.mk x = (grothendieckModuloSerreEquiv P L).symm y at hx
  rw [← grothendieckModuloSerreEquiv_mk P L, hx, AddEquiv.apply_symm_apply]

theorem grothendieckMapModuloSerre_surjective :
    Function.Surjective (grothendieckMapModuloSerre P L) := by
  rw [← grothendieckModuloSerreEquiv_toAddMonoidHom P L]
  exact (grothendieckModuloSerreEquiv P L).surjective

theorem grothendieckMapModuloSerre_injective :
    Function.Injective (grothendieckMapModuloSerre P L) := by
  rw [← grothendieckModuloSerreEquiv_toAddMonoidHom P L]
  exact (grothendieckModuloSerreEquiv P L).injective

/-- The inverse identifies any chosen source representative, not just one
particular object supplied by essential surjectivity. -/
lemma grothendieckModuloSerreEquiv_symm_class {Y : D} {X : C} (e : Y ≅ L.obj X) :
    (grothendieckModuloSerreEquiv P L).symm
        ((abelianExactStructure D).grothendieckClass Y) = classModuloSerre P X := by
  apply (grothendieckModuloSerreEquiv P L).injective
  rw [AddEquiv.apply_symm_apply, grothendieckModuloSerreEquiv_class]
  exact (abelianExactStructure D).grothendieckClass_iso e

/-- Isomorphic localized objects have equal source classes modulo the Serre subgroup. -/
lemma classModuloSerre_eq_of_localized_iso {X Y : C} (e : L.obj X ≅ L.obj Y) :
    classModuloSerre P X = classModuloSerre P Y := by
  apply (grothendieckModuloSerreEquiv P L).injective
  rw [grothendieckModuloSerreEquiv_class, grothendieckModuloSerreEquiv_class]
  exact (abelianExactStructure D).grothendieckClass_iso e

/-- The source class associated to the localization functor's chosen preimage. -/
def inverseObjClass (Y : D) :
    (abelianExactStructure C).GrothendieckGroup ⧸ serreSubgroup P :=
  let := Localization.essSurj L P.isoModSerre
  classModuloSerre P (L.objPreimage Y)

lemma inverseObjClass_eq_symm_class (Y : D) :
    inverseObjClass P L Y = (grothendieckModuloSerreEquiv P L).symm
      ((abelianExactStructure D).grothendieckClass Y) := by
  let := Localization.essSurj L P.isoModSerre
  exact (grothendieckModuloSerreEquiv_symm_class P L (L.objObjPreimageIso Y).symm).symm

lemma inverseObjClass_obj (X : C) :
    inverseObjClass P L (L.obj X) = classModuloSerre P X := by
  rw [inverseObjClass_eq_symm_class]
  exact grothendieckModuloSerreEquiv_symm_class P L (Iso.refl _)

lemma inverseObjClass_iso {X Y : D} (e : X ≅ Y) :
    inverseObjClass P L X = inverseObjClass P L Y := by
  rw [inverseObjClass_eq_symm_class, inverseObjClass_eq_symm_class,
    (abelianExactStructure D).grothendieckClass_iso e]

lemma inverseObjClass_additive {S : ShortComplex D} (hS : S.ShortExact) :
    inverseObjClass P L S.X₂ = inverseObjClass P L S.X₁ + inverseObjClass P L S.X₃ := by
  rw [inverseObjClass_eq_symm_class, inverseObjClass_eq_symm_class,
    inverseObjClass_eq_symm_class, (abelianExactStructure D).grothendieckClass_additive hS,
    map_add]

/-- The original universal lift of the preimage object invariant. -/
def inverseGrothendieckMap :
    (abelianExactStructure D).GrothendieckGroup →+
      (abelianExactStructure C).GrothendieckGroup ⧸ serreSubgroup P :=
  (abelianExactStructure D).grothendieckLift (inverseObjClass P L)
    (fun _ hS => inverseObjClass_additive P L hS)

@[simp]
lemma inverseGrothendieckMap_class (Y : D) :
    inverseGrothendieckMap P L ((abelianExactStructure D).grothendieckClass Y) =
      inverseObjClass P L Y :=
  (abelianExactStructure D).grothendieckLift_class _ _ Y

lemma inverseGrothendieckMap_eq_symm :
    inverseGrothendieckMap P L = (grothendieckModuloSerreEquiv P L).symm.toAddMonoidHom := by
  apply (abelianExactStructure D).grothendieck_hom_ext
  intro Y
  exact (inverseGrothendieckMap_class P L Y).trans (inverseObjClass_eq_symm_class P L Y)

lemma inverseGrothendieckMap_comp :
    (inverseGrothendieckMap P L).comp (grothendieckMap P L) =
      QuotientAddGroup.mk' (serreSubgroup P) := by
  apply (abelianExactStructure C).grothendieck_hom_ext
  intro X
  change inverseGrothendieckMap P L
      (grothendieckMap P L ((abelianExactStructure C).grothendieckClass X)) =
    classModuloSerre P X
  rw [grothendieckMap_class, inverseGrothendieckMap_class, inverseObjClass_obj]

lemma inverseGrothendieckMap_leftInverse :
    Function.LeftInverse (inverseGrothendieckMap P L) (grothendieckMapModuloSerre P L) := by
  intro a
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (serreSubgroup P) a
  exact DFunLike.congr_fun (inverseGrothendieckMap_comp P L) x

/-- Exact functors landing in the Serre class have zero localized K₀ map. -/
theorem grothendieckMap_comp_eq_zero
    {B : Type u₃} [Category.{v₃} B] [Preadditive B] [HasFiniteBiproducts B]
    {EB : ExactStructure B} (F : ExactFunctor EB (abelianExactStructure C))
    (hF : ∀ X : B, P (F.toFunctor.obj X)) :
    (grothendieckMap P L).comp F.grothendieckMap = 0 := by
  apply EB.grothendieck_hom_ext
  intro X
  simp only [AddMonoidHom.comp_apply, ExactFunctor.grothendieckMap_class,
    AddMonoidHom.zero_apply]
  exact grothendieckMap_class_eq_zero P L (hF X)

end CategoryTheory.ExactCategory.SerreLocalization

attribute [colib_tag "COL-0028",
  stacks 02MX "(1), quotient equivalence for the actual additive localization map"]
  CategoryTheory.ExactCategory.SerreLocalization.grothendieckModuloSerreEquiv

attribute [colib_tag "COL-0028"]
  CategoryTheory.ExactCategory.SerreLocalization.grothendieckModuloSerreEquiv_class
  CategoryTheory.ExactCategory.SerreLocalization.grothendieckModuloSerreEquiv_toAddMonoidHom

attribute [colib_tag "COL-0028",
  stacks 02MX "(1), kernel of localization equals the subgroup generated by Serre object classes"]
  CategoryTheory.ExactCategory.SerreLocalization.grothendieckMap_ker

attribute [colib_tag "COL-0028",
  stacks 02MX "(1), surjectivity of the actual localization map on algebraic K0"]
  CategoryTheory.ExactCategory.SerreLocalization.grothendieckMap_surjective
