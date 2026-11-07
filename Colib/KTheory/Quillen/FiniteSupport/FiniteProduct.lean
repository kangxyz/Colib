/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Product
public import Colib.KTheory.Waldhausen.Product.KEquivalence
public import Colib.KTheory.Waldhausen.ExactEquivalence
public import Colib.KTheory.Waldhausen.QuillenComparison.Equivalence
public import Colib.KTheory.Quillen.Map.Functoriality
public import Colib.KTheory.Quillen.Map.NaturalIso
public import Colib.KTheory.Quillen.Equivalence
public import Colib.CategoryTheory.Pi.Exact
public import Mathlib.Data.Fintype.Option

/-!
# Exact-category products on the original Quillen K-maps

The binary equivalence is transported from the proved S-construction product
equivalence through the canonical Q/S comparison. Its forward homomorphism is
the pair of the original exact projection K-maps, with the original canonical
zero rebasing. The chosen product zero objects are compared by exact identity
functors; no definitional identification of these choices is assumed.

For a finite family of abelian categories, `CategoryTheory.Pi.productKEquiv`
uses all original evaluation maps as its forward homomorphism. Its bijectivity
is proved by finite-type induction through actual restriction/splitting exact
equivalences, including a proved trivial-group endpoint for an empty family.
Index universe `u` and object/hom universes `u + 1` are allowed.

Implementation provenance: `Quillen/KTheory/FiniteSupport/FiniteProduct.lean` at Quillen commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual objects, maps, degrees
and universe parameters are retained.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.Product
open CategoryTheory.Waldhausen.QuillenComparison

universe v u

namespace CategoryTheory.ExactCategory.ExactFunctor

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]

/-- The original Q K-map of the actual chosen-zero functor is trivial. -/
@[simp] theorem KMap_zero (E : ExactStructure C) (F : ExactStructure D) (n : ℕ) :
    (ExactFunctor.zero E F).KMap n = 1 := by
  apply MonoidHom.ext
  intro a
  change (ExactFunctor.zero E F).KMap n a = 1
  have h := DFunLike.congr_fun
    (comparisonKEquiv_exactFunctor_naturality E (ExactFunctor.zero E F) n)
    ((comparisonKEquiv E n).symm a)
  have hz : (ExactFunctor.zero E F).waldhausenExact =
      zeroFunctor_isExact (ofExactCategory E) (ofExactCategory F) := Subsingleton.elim _ _
  rw [hz, KMap_zeroFunctor] at h
  change comparisonKEquiv F n 1 = (ExactFunctor.zero E F).KMap n
    (comparisonKEquiv E n ((comparisonKEquiv E n).symm a)) at h
  simpa only [map_one, MulEquiv.apply_symm_apply] using h.symm

end CategoryTheory.ExactCategory.ExactFunctor

namespace CategoryTheory.ExactCategory.ExactStructure

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  (E : ExactStructure C) (F : ExactStructure D)

/-- The identity changes the exact product's Waldhausen presentation to the
componentwise Waldhausen product, preserving the actual category. -/
theorem prodToWaldhausenExact : IsExact
    (ofExactCategory (E.prod F)).cof (ofExactCategory (E.prod F)).weq
    (productStructure (ofExactCategory E) (ofExactCategory F)).cof
    (productStructure (ofExactCategory E) (ofExactCategory F)).weq (𝟭 (C × D)) where
  zero h := h
  cofibration f h := (E.prod_inflation_iff F f).1 h
  weak f h := by
    let : IsIso f := h
    exact ⟨inferInstanceAs (IsIso ((Prod.fst C D).map f)),
      inferInstanceAs (IsIso ((Prod.snd C D).map f))⟩
  pushout _ h := h

/-- The reverse identity is exact as well; admissibility and weak equivalence
are exactly the two component conditions. -/
theorem waldhausenToProdExact : IsExact
    (productStructure (ofExactCategory E) (ofExactCategory F)).cof
    (productStructure (ofExactCategory E) (ofExactCategory F)).weq
    (ofExactCategory (E.prod F)).cof (ofExactCategory (E.prod F)).weq (𝟭 (C × D)) where
  zero h := h
  cofibration f h := (E.prod_inflation_iff F f).2 h
  weak _ h := (isIso_prod_iff C D).mpr h
  pushout _ h := h

/-- The two actual product Waldhausen presentations give the same K-groups
through their exact identity functors. -/
def prodWaldhausenKEquiv (n : ℕ) :
    (ofExactCategory (E.prod F)).K n ≃*
      (productStructure (ofExactCategory E) (ofExactCategory F)).K n :=
  KEquivOfExactEquivalence (CategoryTheory.Equivalence.refl (C := C × D))
    (E.prodToWaldhausenExact F) (E.waldhausenToProdExact F) n

/-- Binary product K-theory for exact categories, constructed from the
original product theorem and the canonical Q/S equivalences. -/
def prodKEquiv (n : ℕ) : (E.prod F).K n ≃* E.K n × F.K n :=
  (comparisonKEquiv (E.prod F) n).symm.trans
    ((E.prodWaldhausenKEquiv F n).trans
      ((CategoryTheory.Waldhausen.Product.KEquiv (ofExactCategory E) (ofExactCategory F) n).trans
        ((comparisonKEquiv E n).prodCongr (comparisonKEquiv F n))))

/-- Each coordinate is the original Q-projection K-map. -/
theorem prodKEquiv_apply (n : ℕ) (a : (E.prod F).K n) :
    E.prodKEquiv F n a = ((E.fstExact F).KMap n a, (E.sndExact F).KMap n a) := by
  let x := (comparisonKEquiv (E.prod F) n).symm a
  have hx : comparisonKEquiv (E.prod F) n x = a := MulEquiv.apply_symm_apply _ a
  apply _root_.Prod.ext
  · change comparisonKEquiv E n
      (KMap (fst_exact (ofExactCategory E) (ofExactCategory F)) n
        (KMap (E.prodToWaldhausenExact F) n x)) = _
    have h := KMap_comp_KMap (E.prodToWaldhausenExact F)
      (fst_exact (ofExactCategory E) (ofExactCategory F)) n
    have h' : (E.prodToWaldhausenExact F).comp
        (fst_exact (ofExactCategory E) (ofExactCategory F)) =
          (E.fstExact F).waldhausenExact := Subsingleton.elim _ _
    rw [← MonoidHom.comp_apply, h, h']
    have hn := DFunLike.congr_fun
      (comparisonKEquiv_exactFunctor_naturality (E.prod F) (E.fstExact F) n) x
    change comparisonKEquiv E n (KMap (E.fstExact F).waldhausenExact n x) =
      (E.fstExact F).KMap n (comparisonKEquiv (E.prod F) n x) at hn
    exact hn.trans (congrArg ((E.fstExact F).KMap n) hx)
  · change comparisonKEquiv F n
      (KMap (snd_exact (ofExactCategory E) (ofExactCategory F)) n
        (KMap (E.prodToWaldhausenExact F) n x)) = _
    have h := KMap_comp_KMap (E.prodToWaldhausenExact F)
      (snd_exact (ofExactCategory E) (ofExactCategory F)) n
    have h' : (E.prodToWaldhausenExact F).comp
        (snd_exact (ofExactCategory E) (ofExactCategory F)) =
          (E.sndExact F).waldhausenExact := Subsingleton.elim _ _
    rw [← MonoidHom.comp_apply, h, h']
    have hn := DFunLike.congr_fun
      (comparisonKEquiv_exactFunctor_naturality (E.prod F) (E.sndExact F) n) x
    change comparisonKEquiv F n (KMap (E.sndExact F).waldhausenExact n x) =
      (E.sndExact F).KMap n (comparisonKEquiv (E.prod F) n x) at hn
    exact hn.trans (congrArg ((E.sndExact F).KMap n) hx)

/-- The underlying homomorphism is exactly the pair of original Q K-maps. -/
@[simp] theorem prodKEquiv_coe (n : ℕ) :
    (↑(E.prodKEquiv F n) : (E.prod F).K n →* E.K n × F.K n) =
      ((E.fstExact F).KMap n).prod ((E.sndExact F).KMap n) := by
  apply MonoidHom.ext
  intro a
  exact E.prodKEquiv_apply F n a

/-- The original first insertion is the inverse image of the first group factor. -/
@[simp] theorem prodKEquiv_inl (n : ℕ) (a : E.K n) :
    E.prodKEquiv F n ((E.inlExact F).KMap n a) = (a, 1) := by
  rw [prodKEquiv_apply]
  apply _root_.Prod.ext
  · have h := DFunLike.congr_fun
      (ExactFunctor.KMap_comp (E.inlExact F) (E.fstExact F) n) a
    simpa only [inlExact_comp_fstExact, ExactFunctor.KMap_id,
      MonoidHom.comp_apply, MonoidHom.id_apply] using h.symm
  · have h := DFunLike.congr_fun
      (ExactFunctor.KMap_comp (E.inlExact F) (E.sndExact F) n) a
    simpa only [inlExact_comp_sndExact, ExactFunctor.KMap_zero,
      MonoidHom.comp_apply, MonoidHom.one_apply] using h.symm

/-- The original second insertion is the inverse image of the second group factor. -/
@[simp] theorem prodKEquiv_inr (n : ℕ) (a : F.K n) :
    E.prodKEquiv F n ((E.inrExact F).KMap n a) = (1, a) := by
  rw [prodKEquiv_apply]
  apply _root_.Prod.ext
  · have h := DFunLike.congr_fun
      (ExactFunctor.KMap_comp (E.inrExact F) (E.fstExact F) n) a
    simpa only [inrExact_comp_fstExact, ExactFunctor.KMap_zero,
      MonoidHom.comp_apply, MonoidHom.one_apply] using h.symm
  · have h := DFunLike.congr_fun
      (ExactFunctor.KMap_comp (E.inrExact F) (E.sndExact F) n) a
    simpa only [inrExact_comp_sndExact, ExactFunctor.KMap_id,
      MonoidHom.comp_apply, MonoidHom.id_apply] using h.symm

/-- The inverse is determined by the two original insertion K-maps. -/
theorem prodKEquiv_symm_apply (n : ℕ) (a : E.K n) (b : F.K n) :
    (E.prodKEquiv F n).symm (a, b) =
      (E.inlExact F).KMap n a * (E.inrExact F).KMap n b := by
  apply (E.prodKEquiv F n).injective
  simp only [MulEquiv.apply_symm_apply, map_mul, prodKEquiv_inl, prodKEquiv_inr,
    _root_.Prod.mk_mul_mk, mul_one, one_mul]

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasFiniteBiproducts T]
  {G : ExactStructure T}

/-- Pairing exact functors agrees with pairing their original Q K-maps. -/
theorem prodKEquiv_pair_apply (f : ExactFunctor G E) (g : ExactFunctor G F)
    (n : ℕ) (a : G.K n) :
    E.prodKEquiv F n ((f.pair g).KMap n a) = (f.KMap n a, g.KMap n a) := by
  rw [prodKEquiv_apply]
  apply _root_.Prod.ext
  · have he : (f.pair g).comp (E.fstExact F) = f := rfl
    have h := DFunLike.congr_fun (ExactFunctor.KMap_comp (f.pair g) (E.fstExact F) n) a
    simpa only [he, MonoidHom.comp_apply] using h.symm
  · have he : (f.pair g).comp (E.sndExact F) = g := rfl
    have h := DFunLike.congr_fun (ExactFunctor.KMap_comp (f.pair g) (E.sndExact F) n) a
    simpa only [he, MonoidHom.comp_apply] using h.symm

/-- An exact category consisting entirely of zero objects has trivial original
Q K-groups in every degree. -/
theorem subsingleton_K_of_all_isZero (hC : ∀ X : C, IsZero X) (n : ℕ) :
    Subsingleton (E.K n) := by
  let e : (ExactFunctor.id E).toFunctor ≅ (ExactFunctor.zero E E).toFunctor :=
    NatIso.ofComponents (fun X => (hC X).iso (isZero_zero C))
      (fun {_ _} _ => (hC _).eq_of_src _ _)
  have h := ExactFunctor.KMap_eq_of_natIso (F := ExactFunctor.id E)
    (G := ExactFunctor.zero E E) e n
  rw [ExactFunctor.KMap_id, ExactFunctor.KMap_zero] at h
  have hone (a : E.K n) : a = 1 := DFunLike.congr_fun h a
  exact ⟨fun a b => (hone a).trans (hone b).symm⟩

end CategoryTheory.ExactCategory.ExactStructure

namespace CategoryTheory.Pi

open CategoryTheory.ExactCategory.ExactStructure

attribute [local instance] Abelian.hasFiniteBiproducts

universe u' v'

variable {I J : Type u} (C : I → Type (max u u'))
  [∀ i, Category.{max u v'} (C i)] [∀ i, Abelian (C i)]

/-- The product homomorphism consists of the original exact evaluations. -/
def productKMap (n : ℕ) :
    (abelianExactStructure (∀ i, C i)).K n →*
      ∀ i, (abelianExactStructure (C i)).K n :=
  MonoidHom.pi (fun i => (exactEvaluation C i).KMap n)

/-- Pullback of an actual family along an index function is exact. -/
private def exactComap (f : J → I) :
    ExactCategory.ExactFunctor (abelianExactStructure (∀ i, C i))
      (abelianExactStructure (∀ j, C (f j))) where
  toFunctor := Pi.comap C f
  additive := { map_add := by intros; rfl }
  map_conflation S h := shortExact_pi_of _ _ (fun j => h.map_of_exact (Pi.eval C (f j)))

/-- Exact evaluation after reindexing is literal evaluation at the reindexed coordinate. -/
@[simp] private theorem exactComap_comp_exactEvaluation (f : J → I) (j : J) :
    (exactComap C f).comp (exactEvaluation (fun j => C (f j)) j) =
      exactEvaluation C (f j) := rfl

private theorem productKMap_exactComap (f : J → I) (n : ℕ)
    (a : (abelianExactStructure (∀ i, C i)).K n) (j : J) :
    productKMap (fun j => C (f j)) n ((exactComap C f).KMap n a) j =
      productKMap C n a (f j) := by
  change (exactEvaluation (fun j => C (f j)) j).KMap n ((exactComap C f).KMap n a) =
    (exactEvaluation C (f j)).KMap n a
  have h := DFunLike.congr_fun (ExactCategory.ExactFunctor.KMap_comp (exactComap C f)
    (exactEvaluation (fun j => C (f j)) j) n) a
  simpa only [exactComap_comp_exactEvaluation, MonoidHom.comp_apply] using h.symm

universe x y

private theorem abelianEquivalence_KMap_bijective
    {A B : Type x} [Category.{y} A] [Category.{y} B]
    [Abelian A] [Preadditive B] [HasFiniteBiproducts B] {E : ExactStructure B}
    (f : ExactCategory.ExactFunctor (abelianExactStructure A) E)
    [f.toFunctor.IsEquivalence] (n : ℕ) :
    Function.Bijective (f.KMap n) := by
  let : f.mapQ.IsEquivalence := f.mapQ_isEquivalence_of_equivalence
    (fun i hi => (abelianExactStructure_inflation_iff A i).2
      (f.toFunctor.mono_of_mono_map (E.mono_of_inflation hi)))
    (fun p hp => (abelianExactStructure_deflation_iff A p).2
      (f.toFunctor.epi_of_epi_map (E.epi_of_deflation hp)))
  exact f.KMap_bijective_of_mapQ_isEquivalence n

variable (C' : Option I → Type (max u u'))
  [∀ i, Category.{max u v'} (C' i)] [∀ i, Abelian (C' i)]

/-- The actual option-indexed family splits into its distinguished coordinate
and the family of remaining coordinates, as an exact functor. -/
private def optionSplitExact : ExactCategory.ExactFunctor (abelianExactStructure (∀ i, C' i))
    ((abelianExactStructure (C' none)).prod
      (abelianExactStructure (∀ i, C' (some i)))) :=
  (exactEvaluation C' none).pair (exactComap C' some)

private theorem optionSplitExact_KMap_bijective (n : ℕ) :
    Function.Bijective ((optionSplitExact C').KMap n) := by
  have : (optionSplitExact C').toFunctor.IsEquivalence := by
    change (Pi.optionEquivalence C').functor.IsEquivalence
    infer_instance
  exact abelianEquivalence_KMap_bijective (optionSplitExact C') n

/-- The family of actual evaluations is bijective for every finite dependent
family, including the empty family. -/
theorem productKMap_bijective [Finite I] (n : ℕ) :
    Function.Bijective (productKMap C n) := by
  classical
  let P : Type u → Prop := fun I =>
    ∀ (C : I → Type (max u u')) [∀ i, Category.{max u v'} (C i)] [∀ i, Abelian (C i)],
      Function.Bijective (productKMap C n)
  have hP : ∀ (I : Type u) [Finite I], P I := by
    intro I _
    apply Finite.induction_empty_option (P := P) ?_ ?_ ?_ I
    · intro A B e h C hCat hAb
      let r := (Equiv.piCongrLeft (fun i => (abelianExactStructure (C i)).K n) e).symm
      have he : (exactComap C e).toFunctor.IsEquivalence := by
        change (Pi.equivalenceOfEquiv C e).inverse.IsEquivalence
        infer_instance
      have hb := (h (fun i => C (e i))).comp
        (abelianEquivalence_KMap_bijective (exactComap C e) n)
      have hc : r ∘ productKMap C n =
          productKMap (fun i => C (e i)) n ∘ (exactComap C e).KMap n := by
        funext a i
        exact (productKMap_exactComap C e n a i).symm
      rw [← hc] at hb
      exact hb.of_comp_left r.injective
    · intro C hCat hAb
      let E := abelianExactStructure (∀ i, C i)
      let : Subsingleton (E.K n) := E.subsingleton_K_of_all_isZero
        (fun M => (isZero_family_iff C M).2 (fun i => isEmptyElim i)) n
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨1, Subsingleton.elim _ b⟩⟩
    · intro A _ h C hCat hAb
      let E := abelianExactStructure (C none)
      let F := abelianExactStructure (∀ i, C (some i))
      let tail := productKMap (fun i => C (some i)) n
      let r : (∀ i, (abelianExactStructure (C i)).K n) ≃
          E.K n × ∀ i, (abelianExactStructure (C (some i))).K n := Equiv.piOptionEquivProd
      let t : E.K n × F.K n → E.K n × ∀ i, (abelianExactStructure (C (some i))).K n :=
        fun p => (p.1, tail p.2)
      have ht : Function.Bijective t :=
        ((Equiv.refl (E.K n)).prodCongr (Equiv.ofBijective tail (h _))).bijective
      have hb := ht.comp ((E.prodKEquiv F n).bijective.comp
        (optionSplitExact_KMap_bijective C n))
      have hc : r ∘ productKMap C n = t ∘ E.prodKEquiv F n ∘
          (optionSplitExact C).KMap n := by
        funext a
        change (productKMap C n a none, fun i => productKMap C n a (some i)) =
          t (E.prodKEquiv F n ((optionSplitExact C).KMap n a))
        rw [optionSplitExact, prodKEquiv_pair_apply]
        apply _root_.Prod.ext
        · rfl
        · funext i
          exact (productKMap_exactComap C some n a i).symm
      rw [← hc] at hb
      exact hb.of_comp_left r.injective
  exact hP I C

/-- Finite dependent product K-theory, whose forward map is the original
coordinate evaluation homomorphism and is independent of an enumeration. -/
def productKEquiv [Finite I] (n : ℕ) :
    (abelianExactStructure (∀ i, C i)).K n ≃*
      ∀ i, (abelianExactStructure (C i)).K n :=
  MulEquiv.ofBijective (productKMap C n) (productKMap_bijective C n)

@[simp] theorem productKEquiv_apply [Finite I] (n : ℕ)
    (a : (abelianExactStructure (∀ i, C i)).K n) (i : I) :
    productKEquiv C n a i = (exactEvaluation C i).KMap n a := rfl

@[simp] theorem productKEquiv_coe [Finite I] (n : ℕ) :
    (↑(productKEquiv C n) : (abelianExactStructure (∀ i, C i)).K n →*
      ∀ i, (abelianExactStructure (C i)).K n) = productKMap C n := rfl

/-- The original evaluations jointly detect equality at a finite stage. -/
theorem productK_ext [Finite I] (n : ℕ)
    {a b : (abelianExactStructure (∀ i, C i)).K n}
    (h : ∀ i, (exactEvaluation C i).KMap n a = (exactEvaluation C i).KMap n b) : a = b :=
  (productKEquiv C n).injective (funext h)

/-- The inverse of the product equivalence has the prescribed original
evaluation K-map at every coordinate. -/
@[simp] theorem productKEquiv_symm_evaluation [Finite I] (n : ℕ)
    (a : ∀ i, (abelianExactStructure (C i)).K n) (i : I) :
    (exactEvaluation C i).KMap n ((productKEquiv C n).symm a) = a i :=
  congrFun ((productKEquiv C n).apply_symm_apply a) i

/-- The empty product endpoint is a proved trivial original Q K-group. -/
theorem productK_subsingleton_of_isEmpty [IsEmpty I] (n : ℕ) :
    Subsingleton ((abelianExactStructure (∀ i, C i)).K n) :=
  (abelianExactStructure (∀ i, C i)).subsingleton_K_of_all_isZero
    (fun M => (isZero_family_iff C M).2 (fun i => isEmptyElim i)) n

end CategoryTheory.Pi
