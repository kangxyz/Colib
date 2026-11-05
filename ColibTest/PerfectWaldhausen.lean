module

import Colib.AlgebraicGeometry.Modules.LocalRepresentativeEquivalence
import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Colib.AlgebraicGeometry.Modules.PerfectWaldhausen
import Colib.CategoryTheory.Waldhausen.EquivalenceStructure

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject

universe u d

namespace PerfectWaldhausenProbe

variable (X : Scheme.{u}) [hD : ∀ U : X.Opens, HasDerivedCategory.{d} U.toScheme.Modules]

-- The old locallyPerfect witness with the old bound and local-basis definitions unfolded.
-- These predicates are private test scaffolding, not new public API.
private def source : ObjectProperty (CochainComplex X.Modules ℤ) := fun K =>
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ P : CochainComplex U.toScheme.Modules ℤ,
    (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (P.X n)) ∧
    (∀ n : ℤ, ∃ q : _root_.SheafOfModules.LocalGeneratorsData.{u} (P.X n),
      q.IsLocallyFreeData ∧ q.IsFiniteType) ∧
    Nonempty ((DerivedCategory.Q (C := U.toScheme.Modules)).obj
        (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      (DerivedCategory.Q (C := U.toScheme.Modules)).obj P)

private def target : ObjectProperty (CochainComplex X.Modules ℤ) :=
  RingedSpace.IsPerfectComplex (X := X.toRingedSpace)

private theorem source_iff_target (K : CochainComplex X.Modules ℤ) :
    source X K ↔ target X K := by
  constructor
  · intro h
    apply (Scheme.Modules.Complex.isPerfectComplex_iff_local_bounded_finiteLocallyFree_models
      X K).mpr
    intro x
    obtain ⟨U, hxU, P, hb, ht, e⟩ := h x
    exact ⟨U, hxU, P, hb, fun n => SheafOfModules.IsFiniteLocallyFree.mk.{u, u, u} (ht n), e⟩
  · intro h x
    obtain ⟨U, hxU, P, hb, ht, e⟩ :=
      (Scheme.Modules.Complex.isPerfectComplex_iff_local_bounded_finiteLocallyFree_models
        X K).mp h x
    exact ⟨U, hxU, P, hb, fun n => (ht n).exists_isFiniteLocallyFreeData, e⟩

private def comparison : (source X).FullSubcategory ≌ (target X).FullSubcategory where
  functor := ObjectProperty.ιOfLE (fun K => (source_iff_target X K).mp)
  inverse := ObjectProperty.ιOfLE (fun K => (source_iff_target X K).mpr)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

example : (comparison X).functor ⋙ (target X).ι = (source X).ι := rfl

example : (comparison X).inverse ⋙ (source X).ι = (target X).ι := rfl

example (K : (source X).FullSubcategory) : ((comparison X).functor.obj K).obj = K.obj := rfl

example (K : (target X).FullSubcategory) : ((comparison X).inverse.obj K).obj = K.obj := rfl

example {K L : (source X).FullSubcategory} (f : K ⟶ L) :
    ((comparison X).functor.map f).hom = f.hom := rfl

example {K L : (target X).FullSubcategory} (f : K ⟶ L) :
    ((comparison X).inverse.map f).hom = f.hom := rfl

example (K : (source X).FullSubcategory) : ((comparison X).unitIso.app K).hom.hom = 𝟙 K.obj := rfl

example (K : (target X).FullSubcategory) :
    ((comparison X).counitIso.app K).hom.hom = 𝟙 K.obj := rfl

example {K L : (source X).FullSubcategory} (f : K ⟶ L) :
    QuasiIso (((comparison X).functor.map f).hom) ↔ QuasiIso f.hom := Iff.rfl

example {K L : (target X).FullSubcategory} (f : K ⟶ L) :
    QuasiIso (((comparison X).inverse.map f).hom) ↔ QuasiIso f.hom := Iff.rfl

example : (comparison X).functor.IsEquivalence := inferInstance

example : (comparison X).inverse.IsEquivalence := inferInstance


private def targetWaldhausen : Waldhausen.Structure (target X).FullSubcategory :=
  RingedSpace.perfectComplexesWaldhausen X.toRingedSpace

private theorem sourceClosed : Waldhausen.CofibrationClosedSubcategory.Closed
    (Waldhausen.complexes X.Modules) (source X) where
  zero_mem := (source_iff_target X _).mpr
    (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace).zero_mem
  pushout_mem {A B D Q} {i f g j} hi h hA hB hD := by
    have : Mono (C := CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace) ℤ) i := hi
    exact (source_iff_target X _).mpr (RingedSpace.isPerfectComplex_of_isPushout h
      ((source_iff_target X _).mp hA) ((source_iff_target X _).mp hB)
      ((source_iff_target X _).mp hD))

private def sourceWaldhausen : Waldhausen.Structure (source X).FullSubcategory :=
  Waldhausen.CofibrationClosedSubcategory.waldhausenStructure
    (Waldhausen.complexes X.Modules) (source X) (sourceClosed X)

-- Exact old inflation witness, after unfolding its abelian conflation and full subcategory.
private def sourceCofibrations : MorphismProperty (source X).FullSubcategory :=
  fun _K L f => ∃ Q : CochainComplex X.Modules ℤ, source X Q ∧
    ∃ (p : L.obj ⟶ Q) (h : f.hom ≫ p = 0), (ShortComplex.mk f.hom p h).ShortExact

private theorem sourceCofibrations_iff_mono {K L : (source X).FullSubcategory} (f : K ⟶ L) :
    sourceCofibrations X f ↔ Mono f.hom := by
  constructor
  · rintro ⟨Q, hQ, p, h, hs⟩
    exact hs.mono_f
  · intro hm
    have : Mono f.hom := hm
    have hs : (ShortComplex.mk f.hom (cokernel.π f.hom) (cokernel.condition f.hom)).ShortExact :=
      { exact := ShortComplex.cokernelSequence_exact f.hom }
    refine ⟨cokernel f.hom, ?_, cokernel.π f.hom, cokernel.condition f.hom, hs⟩
    exact (source_iff_target X _).mpr (RingedSpace.isPerfectComplex_X₃_of_shortExact hs
      ((source_iff_target X _).mp K.property) ((source_iff_target X _).mp L.property))

private theorem sourceCofibrations_eq_inherited :
    sourceCofibrations X = (sourceWaldhausen X).cof := by
  funext K L f
  exact propext (sourceCofibrations_iff_mono X f)

private theorem comparison_exact :
    Waldhausen.IsExact (sourceWaldhausen X).cof (sourceWaldhausen X).weq
      (targetWaldhausen X).cof (targetWaldhausen X).weq (comparison X).functor where
  zero h := IsZero.of_full_of_faithful_of_isZero (comparison X).inverse _
    (h.of_iso ((comparison X).unitIso.app _).symm)
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map (comparison X).functor

private theorem comparison_inverse_exact :
    Waldhausen.IsExact (targetWaldhausen X).cof (targetWaldhausen X).weq
      (sourceWaldhausen X).cof (sourceWaldhausen X).weq (comparison X).inverse where
  zero h := IsZero.of_full_of_faithful_of_isZero (comparison X).functor _
    (h.of_iso ((comparison X).counitIso.app _))
  cofibration _ h := h
  weak _ h := h
  pushout _ h := h.map (comparison X).inverse

example : (sourceWaldhausen X).zero.obj = 0 := rfl

example : (targetWaldhausen X).zero.obj = 0 := rfl

example : (comparison X).functor.obj (sourceWaldhausen X).zero =
    (targetWaldhausen X).zero := rfl

example {K L : (source X).FullSubcategory} (f : K ⟶ L) :
    (sourceWaldhausen X).cof f ↔ sourceCofibrations X f :=
  (sourceCofibrations_iff_mono X f).symm

example {K L : (source X).FullSubcategory} (f : K ⟶ L) :
    (sourceWaldhausen X).weq f ↔ QuasiIso f.hom := Iff.rfl

example {K L : (target X).FullSubcategory} (f : K ⟶ L) :
    (targetWaldhausen X).weq f ↔ QuasiIso f.hom := Iff.rfl

/-- Test-level witness that the reconstructed old-predicate structure has an exact,
identity-underlying equivalence to the native perfect-complex structure. -/
private theorem exact_comparison_exists :
    ∃ e : (source X).FullSubcategory ≌ (target X).FullSubcategory,
      Waldhausen.IsExact (sourceWaldhausen X).cof (sourceWaldhausen X).weq
        (targetWaldhausen X).cof (targetWaldhausen X).weq e.functor ∧
      Waldhausen.IsExact (targetWaldhausen X).cof (targetWaldhausen X).weq
        (sourceWaldhausen X).cof (sourceWaldhausen X).weq e.inverse :=
  ⟨comparison X, comparison_exact X, comparison_inverse_exact X⟩

end PerfectWaldhausenProbe

/-- Native perfect complexes on an arbitrary scheme carry the actual Waldhausen structure. -/
def schemePerfectWaldhausen (X : Scheme.{u}) :
    Waldhausen.Structure (ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :=
  RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
