/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

/- Adapted from Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.
Uses native Q-construction and intrinsic abelian full-subcategory exact structure. -/

public import Colib.KTheory.Quillen.Localization.Serre.KernelPushoutExistence
public import Colib.KTheory.Quillen.Localization.Serre.KernelPushoutUniqueness
public import Colib.CategoryTheory.TheoremA.ContractibleComma
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Colib.CategoryTheory.Abelian.Devissage.QInclusion

/-! # The actual reflection of the kernel comma category

The mono–epi cospan of a kernel Q-arrow enlarges the middle extension by
pushout. Its universal property gives a genuine reflection onto the
subcategory of surjective kernel arrows.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.ExactCategory.SerreLocalization

open CategoryTheory.Abelian.SerreLocalization CategoryTheory.Abelian
attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{u} C] [Abelian C]
variable (P : ObjectProperty C) [P.IsSerreClass]

instance epiAuxiliary_obj_epi {N : C} (X : EpiAuxiliaryKernel P N) :
    Epi X.obj.obj.of.hom := X.property.2

lemma subcategoryQ_surjection_iff {X Y : (abelianExactStructure P.FullSubcategory).QCategory}
    (f : X ⟶ Y) : QConstruction.IsSurjection ((Devissage.mapQ P).map f) ↔
      QConstruction.IsSurjection f := by
  let : (CategoryTheory.ObjectProperty.exactInclusion P).toFunctor.ReflectsIsomorphisms :=
    inferInstanceAs P.ι.ReflectsIsomorphisms
  exact QConstruction.isSurjection_mapQ_iff (CategoryTheory.ObjectProperty.exactInclusion P) f

section ReflectionData
variable {N : C} {T : (abelianExactStructure P.FullSubcategory).QCategory}
  (A : EpiKernelComma P N T) {U : C}
  (i : (overKernel N).obj A.left.obj.obj.of ⟶ U) [Mono i]
  (p : T.obj.of.obj ⟶ U) [Epi p]

/-- The pushed-out epimorphic extension belongs to the original Serre class. -/
@[implicit_reducible]
def kernelCommaReflectionExtension : EpiAuxiliaryKernel P N :=
  kernelPushoutAuxiliary A.left.obj.obj.of i P (P.prop_of_epi p T.obj.of.property)

/-- Its new kernel arrow is the reversal of the prescribed epi. -/
@[implicit_reducible]
def kernelCommaReflectionArrow :
    (epiAuxiliaryKernelFunctor P N).obj (kernelCommaReflectionExtension P A i p) ⟶ T :=
  (Devissage.mapQ P).preimage
    (QConstruction.surjectionArrow (p ≫ (kernelPushoutIso A.left.obj.obj.of i).hom))

omit [Mono i] in
@[simp]
lemma kernelCommaReflectionArrow_map :
    (Devissage.mapQ P).map (kernelCommaReflectionArrow P A i p) =
      QConstruction.surjectionArrow (p ≫ (kernelPushoutIso A.left.obj.obj.of i).hom) :=
  (Devissage.mapQ P).map_preimage _

omit [Mono i] in
lemma kernelCommaReflectionArrow_surjection : QConstruction.IsSurjection
  (kernelCommaReflectionArrow P A i p) :=
  by
  apply (subcategoryQ_surjection_iff P _).1
  rw [kernelCommaReflectionArrow_map]
  exact QConstruction.isSurjection_surjectionArrow _

/-- The reflection object has a genuinely surjective kernel arrow. -/
@[implicit_reducible]
def kernelCommaReflectionObject : SurjectiveKernelComma P N T :=
  ⟨CostructuredArrow.mk (kernelCommaReflectionArrow P A i p),
    kernelCommaReflectionArrow_surjection P A i p⟩

/-- Its slice arrow is the ordinary monomorphism into the pushout extension. -/
@[implicit_reducible]
def kernelCommaReflectionUnitLeft : A.left ⟶ kernelCommaReflectionExtension P A i p :=
  ObjectProperty.homMk (overInflationArrow (kernelPushoutOverHom A.left.obj.obj.of i))

variable (hc : QConstruction.inflationArrow i ≫ QConstruction.surjectionArrow p = (Devissage.mapQ
  P).map A.hom)

/-- The unit satisfies the actual comma equation. -/
@[implicit_reducible]
def kernelCommaReflectionUnit : A ⟶ (kernelCommaReflectionObject P A i p).obj :=
  CostructuredArrow.homMk (kernelCommaReflectionUnitLeft P A i p) (by
    apply (Devissage.mapQ P).map_injective
    rw [Functor.map_comp]
    change (Devissage.mapQ P).map ((epiAuxiliaryKernelFunctor P N).map
      (kernelCommaReflectionUnitLeft P A i p)) ≫
      (Devissage.mapQ P).map (kernelCommaReflectionArrow P A i p) = _
    rw [kernelCommaReflectionArrow_map, map_epiAuxiliaryKernelFunctor]
    change (overKernelQ N).map (overInflationArrow (kernelPushoutOverHom A.left.obj.obj.of i)) ≫ _ =
      _
    rw [overKernelQ_inflationArrow]
    exact (QConstruction.cospan_eq_of_iso i p _ _ (kernelPushoutIso A.left.obj.obj.of i)
      (kernelPushoutOverHom_kernel A.left.obj.obj.of i).symm rfl).symm.trans hc)

/-- The reflection object as a universal arrow to the inclusion. -/
@[implicit_reducible]
def kernelCommaReflectionStructured :
    StructuredArrow A (surjectiveKernelCommaProperty P N T).ι :=
  StructuredArrow.mk (Y := kernelCommaReflectionObject P A i p) (kernelCommaReflectionUnit P A i p
    hc)


/-- Every competing arrow into a surjective kernel object factors through
the pushed-out extension, with its comma triangle intact. -/
theorem kernelCommaReflectionStructured_nonempty_hom
    (V : StructuredArrow A (surjectiveKernelCommaProperty P N T).ι) :
    Nonempty (kernelCommaReflectionStructured P A i p hc ⟶ V) := by
  have hv : QConstruction.IsSurjection ((Devissage.mapQ P).map V.right.obj.hom) :=
    (subcategoryQ_surjection_iff P _).2 V.right.property
  obtain ⟨q, hq, hqeq⟩ := QConstruction.isSurjection_iff_exists_epi _ |>.1 hv
  change T.obj.of.obj ⟶ (overKernel N).obj V.right.obj.left.obj.obj.of at q
  have hw : (overKernelQ N).map V.hom.left.hom ≫ QConstruction.surjectionArrow q =
      QConstruction.inflationArrow i ≫ QConstruction.surjectionArrow p := by
    rw [hqeq, ← map_epiAuxiliaryKernelFunctor, ← Functor.map_comp]
    exact (congrArg ((Devissage.mapQ P).map) (CostructuredArrow.w V.hom)).trans hc.symm
  obtain ⟨g, hg, hkg⟩ := kernelPushout_factor_exists i p q V.hom.left.hom hw
  let ga : kernelCommaReflectionExtension P A i p ⟶ V.right.obj.left := ObjectProperty.homMk g
  let gc : (kernelCommaReflectionObject P A i p).obj ⟶ V.right.obj :=
    CostructuredArrow.homMk ga (by
      apply (Devissage.mapQ P).map_injective
      rw [Functor.map_comp, map_epiAuxiliaryKernelFunctor]
      change (overKernelQ N).map g ≫ (Devissage.mapQ P).map V.right.obj.hom =
        (Devissage.mapQ P).map (kernelCommaReflectionArrow P A i p)
      rw [← hqeq, kernelCommaReflectionArrow_map]
      exact hkg)
  refine ⟨StructuredArrow.homMk (ObjectProperty.homMk gc) ?_⟩
  apply CostructuredArrow.hom_ext
  apply ObjectProperty.hom_ext
  exact hg


/-- The factorization through the pushout unit is unique. -/
theorem kernelCommaReflectionStructured_hom_ext
    {V : StructuredArrow A (surjectiveKernelCommaProperty P N T).ι}
    (f g : kernelCommaReflectionStructured P A i p hc ⟶ V) : f = g := by
  have hv : QConstruction.IsSurjection ((Devissage.mapQ P).map V.right.obj.hom) :=
    (subcategoryQ_surjection_iff P _).2 V.right.property
  obtain ⟨q, hq, hqeq⟩ := QConstruction.isSurjection_iff_exists_epi _ |>.1 hv
  change T.obj.of.obj ⟶ (overKernel N).obj V.right.obj.left.obj.obj.of at q
  have : Epi (Over.mk (kernelPushoutMap A.left.obj.obj.of i)).hom :=
    kernelPushoutMap_epi A.left.obj.obj.of i
  apply StructuredArrow.hom_ext
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  apply ObjectProperty.hom_ext
  apply overQ_hom_ext_of_kernel_triangles (kernelPushoutOverHom A.left.obj.obj.of i)
    q (p ≫ (kernelPushoutIso A.left.obj.obj.of i).hom)
  · exact (congrArg (fun k => k.left.hom) (StructuredArrow.w f)).trans
      (congrArg (fun k => k.left.hom) (StructuredArrow.w g)).symm
  · rw [hqeq, ← map_epiAuxiliaryKernelFunctor, ← Functor.map_comp]
    exact (congrArg ((Devissage.mapQ P).map) (CostructuredArrow.w f.right.hom)).trans
      (kernelCommaReflectionArrow_map P A i p)
  · rw [hqeq, ← map_epiAuxiliaryKernelFunctor, ← Functor.map_comp]
    exact (congrArg ((Devissage.mapQ P).map) (CostructuredArrow.w g.right.hom)).trans
      (kernelCommaReflectionArrow_map P A i p)

/-- The constructed unit is a genuine initial object of its structured
comma category, hence supplies the reflection rather than merely an objectwise replacement. -/
def kernelCommaReflectionStructuredIsInitial :
    IsInitial (kernelCommaReflectionStructured P A i p hc) :=
  IsInitial.ofUniqueHom
    (fun V => Classical.choice (kernelCommaReflectionStructured_nonempty_hom P A i p hc V))
    (fun _V f => kernelCommaReflectionStructured_hom_ext P A i p hc f _)

end ReflectionData


/-- Every full kernel-comma object has an actual universal arrow to the
surjective-kernel subcategory. -/
instance surjectiveKernelComma_inclusion_hasInitial (N : C)
    (T : (abelianExactStructure P.FullSubcategory).QCategory) (A : EpiKernelComma
      P N T) :
    HasInitial (StructuredArrow A (surjectiveKernelCommaProperty P N T).ι) := by
  obtain ⟨U, i, p, hi, hp, hc⟩ := QConstruction.exists_cospan ((Devissage.mapQ P).map A.hom)
  exact (kernelCommaReflectionStructuredIsInitial P A i p hc).hasInitial

/-- The actual left adjoint which reflects a kernel Q-arrow to its surjective
cospan after enlarging the extension kernel. -/
def kernelCommaReflector (N : C) (T : (abelianExactStructure P.FullSubcategory).QCategory) :
    EpiKernelComma P N T ⥤ SurjectiveKernelComma P N T :=
  leftAdjointOfStructuredArrowInitials (surjectiveKernelCommaProperty P N T).ι

/-- The reflection is a genuine adjunction with the existing full-subcategory inclusion. -/
def kernelCommaReflectionAdjunction (N : C)
    (T : (abelianExactStructure P.FullSubcategory).QCategory) :
    kernelCommaReflector P N T ⊣ (surjectiveKernelCommaProperty P N T).ι :=
  adjunctionOfStructuredArrowInitials (surjectiveKernelCommaProperty P N T).ι

/-- The full kernel comma has contractible classifying space. The proof
uses the constructed reflection and the proved initial object in its image. -/
theorem epiKernelComma_contractible (N : C)
    (T : (abelianExactStructure P.FullSubcategory).QCategory) :
    ContractibleSpace (ClassifyingSpace (EpiKernelComma P N T)) := by
  let := surjectiveKernelComma_contractible P N T
  exact (adjunctionClassifyingHomotopyEquiv (kernelCommaReflectionAdjunction P N
    T)).contractibleSpace

/-- Quillen's epimorphic auxiliary kernel functor is a homotopy equivalence,
derived from actual contractible commas rather than supplied as an assumption. -/
def epiAuxiliaryKernelClassifyingHomotopyEquiv (N : C) :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (EpiAuxiliaryKernel P N))
      (ClassifyingSpace (abelianExactStructure P.FullSubcategory).QCategory) :=
  TheoremA.contractibleCommaClassifyingHomotopyEquiv (epiAuxiliaryKernelFunctor P N)
    (epiKernelComma_contractible P N)

@[simp]
theorem epiAuxiliaryKernelClassifyingHomotopyEquiv_toFun (N : C) :
    (epiAuxiliaryKernelClassifyingHomotopyEquiv P N).toFun =
      (classifyingSpaceMap (epiAuxiliaryKernelFunctor P N)).hom := rfl

end CategoryTheory.ExactCategory.SerreLocalization
