/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.TheoremA.RealizationSkeleton
public import Colib.CategoryTheory.TheoremA.DiagonalColimits
public import Colib.AlgebraicTopology.SimplexCategory.EpiZero

/-! Source: Quillen/CategoryTheory/TheoremA/SkeletalAttachments.lean at
c561118b7795eb9780be9ed391c3251d6a4d0afd. Native topology lower owners are reused. -/

/-! # Enriched attachments in the base-skeleton filtration -/
@[expose] public section

noncomputable section

open SSet TopCat CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial Topology

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CategoryTheory.TheoremA

/-- An explicit coproduct of bisimplicial sets. -/
def bisimplicialSigma {ι : Type u} (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    SimplexCategoryᵒᵖ ⥤ SSet.{u} where
  obj p := SSet.simplicialSigma fun i ↦ (X i).obj p
  map α := SSet.simplicialSigmaMap fun i ↦ (X i).map α
  map_id p := by ext q x : 4; dsimp [SSet.simplicialSigmaMap]; simp
  map_comp α β := by ext q x : 4; dsimp [SSet.simplicialSigmaMap]; simp

/-- An individual summand of the explicit bisimplicial coproduct. -/
def bisimplicialSigmaι {ι : Type u} (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) (i : ι) :
    X i ⟶ bisimplicialSigma X where
  app p := SSet.simplicialSigmaι (fun i ↦ (X i).obj p) i
  naturality _ _ _ := rfl

/-- The actual coproduct map determined by maps from its summands. -/
def bisimplicialSigmaDesc {ι : Type u} {X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    {Y : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (f : ∀ i, X i ⟶ Y) :
    bisimplicialSigma X ⟶ Y where
  app p := {
    app q := ↾fun x ↦ ((f x.1).app p).app q x.2
    naturality q r β := by
      ext x : 3
      exact ConcreteCategory.congr_hom (((f x.1).app p).naturality β) x.2 }
  naturality p q α := by
    ext r x : 4
    exact ConcreteCategory.congr_hom (NatTrans.congr_app ((f x.1).naturality α) r) x.2

/-- The displayed coproduct has the categorical universal property. -/
def bisimplicialSigmaIsColimit {ι : Type u}
    (X : ι → SimplexCategoryᵒᵖ ⥤ SSet.{u}) :
    IsColimit (Cofan.mk (bisimplicialSigma X) (bisimplicialSigmaι X)) :=
  Cofan.IsColimit.mk _
    (fun s ↦ bisimplicialSigmaDesc fun i ↦ s.inj i)
    (by intro s i; rfl)
    (by
      intro s m hm
      ext p q x : 5
      exact ConcreteCategory.congr_hom
        (NatTrans.congr_app (NatTrans.congr_app (hm x.1) p) q) x.2)

variable {D : Type u} [SmallCategory D] (H : D ⥤ SSet.{u})

/-- All enriched `n`-cells. -/
def replacementCells (n : ℕ) := bisimplicialSigma fun s : (nerve D).nonDegenerate n ↦
  replacementCell H s

/-- All enriched boundaries of the `n`-cells. -/
def replacementCellBoundaries (n : ℕ) :=
  bisimplicialSigma fun s : (nerve D).nonDegenerate n ↦ replacementCellBoundary H s

/-- The coproduct of actual enriched boundary inclusions. -/
def replacementCellsBoundaryι (n : ℕ) :
    replacementCellBoundaries H n ⟶ replacementCells H n :=
  bisimplicialSigmaDesc fun s ↦ replacementCellBoundaryι H s ≫
    bisimplicialSigmaι (fun s ↦ replacementCell H s) s

/-- The attaching map from all boundaries into the previous skeleton. -/
def replacementCellsAttaching (n : ℕ) :
    replacementCellBoundaries H n ⟶ (replacementSkeleton H).obj n :=
  bisimplicialSigmaDesc fun s ↦ replacementCellAttaching H s

/-- The characteristic map from all cells into the next skeleton. -/
def replacementCellsCharacteristic (n : ℕ) :
    replacementCells H n ⟶ (replacementSkeleton H).obj (n + 1) :=
  bisimplicialSigmaDesc fun s ↦ replacementCellCharacteristic H s

/-- The boundary of the family of enriched cells commutes strictly. -/
theorem replacementCells_square (n : ℕ) :
    replacementCellsAttaching H n ≫ (replacementSkeleton H).map (homOfLE (Nat.le_succ n)) =
      replacementCellsBoundaryι H n ≫ replacementCellsCharacteristic H n := rfl

/-- Degeneracy operators transport replacement fibers isomorphically. -/
instance firstVertexEdge_isIso_of_epi {p q : SimplexCategory} (f : p ⟶ q) [Epi f]
    (s : (nerve D).obj (op q)) : IsIso (firstVertexEdge f.op s) := by
  dsimp [firstVertexEdge]
  have h : IsIso (homOfLE (Fin.zero_le (f.toOrderHom 0))) := by
    have heq := SimplexCategory.epi_zero f
    rw [heq]
    change IsIso (𝟙 (0 : Fin (q.len + 1)))
    infer_instance
  exact Functor.map_isIso _ _

/-- The characteristic map meets the previous skeleton exactly on its boundary. -/
theorem replacementBaseCell_mem_iff_boundary {n : ℕ} (s : (nerve D).nonDegenerate n)
    {p : SimplexCategoryᵒᵖ} (a : (Δ[n] : SSet.{u}).obj p) :
    (nerve D).map a.down.op s.1 ∈ ((nerve D).skeleton n).obj p ↔
      a ∈ (∂Δ[n]).obj p := by
  have h := (replacementBaseCell s).preimage_map
  have heq : ((nerve D).skeleton n).preimage (replacementBaseCell s).map = ∂Δ[n] := by
    simpa [SSet.skeletonOfMono] using h
  change a ∈ (((nerve D).skeleton n).preimage (replacementBaseCell s).map).obj p ↔ _
  rw [heq]

instance replacementRestrictionInclusion_app_app_mono
    {A B : (nerve D).Subcomplex} (h : A ≤ B)
    (p q : SimplexCategoryᵒᵖ) :
    Mono (((replacementRestrictionInclusion H h).app p).app q) := by
  apply (mono_iff_injective _).2
  intro x y hxy
  obtain ⟨hbase, hfiber⟩ := Sigma.ext_iff.mp hxy
  exact Sigma.ext (Subtype.ext (congrArg (fun z : B.obj p ↦ z.1) hbase)) hfiber

instance replacementSkeleton_map_app_app_mono {n m : ℕ} (f : n ⟶ m)
    (p q : SimplexCategoryᵒᵖ) : Mono ((((replacementSkeleton H).map f).app p).app q) :=
  replacementRestrictionInclusion_app_app_mono H _ p q

/-- The enriched cell-attachment square is also a pullback at each bidegree. -/
theorem replacementCells_isPullback_app (n : ℕ) (p q : SimplexCategoryᵒᵖ) :
    IsPullback (((replacementCellsAttaching H n).app p).app q)
      (((replacementCellsBoundaryι H n).app p).app q)
      ((((replacementSkeleton H).map (homOfLE (Nat.le_succ n))).app p).app q)
      (((replacementCellsCharacteristic H n).app p).app q) := by
  rw [Types.isPullback_iff]
  refine ⟨rfl, ?_, ?_⟩
  · intro x y h
    rcases x with ⟨s, ⟨⟨a, ha⟩, z⟩⟩
    rcases y with ⟨t, ⟨⟨b, hb⟩, w⟩⟩
    have heq : (⟨s, ⟨a, z⟩⟩ : Σ s : (nerve D).nonDegenerate n,
        Σ _ : (Δ[n] : SSet.{u}).obj p, (H.obj (s.1.obj 0)).obj q) =
      ⟨t, ⟨b, w⟩⟩ := h.2
    obtain ⟨rfl, heq⟩ := Sigma.ext_iff.mp heq
    have heq := eq_of_heq heq
    obtain ⟨rfl, heq⟩ := Sigma.ext_iff.mp heq
    cases eq_of_heq heq
    rfl
  · intro x y h
    have hbase : x.1.1 = (nerve D).map y.2.1.down.op y.1.1 :=
      congrArg (fun z ↦ z.1.1) h
    have ha : y.2.1 ∈ (∂Δ[n]).obj p :=
      (replacementBaseCell_mem_iff_boundary y.1 y.2.1).mp (hbase ▸ x.1.2)
    refine ⟨⟨y.1, ⟨⟨y.2.1, ha⟩, y.2.2⟩⟩, ?_, rfl⟩
    apply (mono_iff_injective
      ((((replacementSkeleton H).map (homOfLE (Nat.le_succ n))).app p).app q)).mp
        inferInstance
    exact h.symm

/-- The old skeleton and the enriched characteristic maps jointly cover the
next skeleton in each bidegree. -/
theorem replacementCells_jointly_surjective (n : ℕ) (p q : SimplexCategoryᵒᵖ) :
    Set.range ((((replacementSkeleton H).map (homOfLE (Nat.le_succ n))).app p).app q) ⊔
      Set.range (((replacementCellsCharacteristic H n).app p).app q) = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro ⟨⟨x, hx⟩, y⟩
  obtain ⟨d, f, _, s, rfl⟩ := (nerve D).exists_nonDegenerate x
  have hs : s.1 ∈ ((nerve D).skeleton (n + 1)).obj (op ⦋d⦌) := by
    rw [← SSet.Subcomplex.ofSimplex_le_iff,
      ← SSet.Subcomplex.ofSimplex_map_of_epi f s.1, SSet.Subcomplex.ofSimplex_le_iff]
    exact hx
  have hd := ((nerve D).mem_skeleton_obj_iff_of_nonDegenerate s (n + 1)).mp hs
  obtain hd | rfl := (Nat.le_of_lt_succ hd).lt_or_eq
  · exact Or.inl ⟨⟨⟨(nerve D).map f.op s.1,
      ((nerve D).skeleton n).map f.op ((nerve D).mem_skeleton s.1 hd)⟩, y⟩, rfl⟩
  · refine Or.inr ⟨⟨s, ⟨SSet.stdSimplex.objEquiv.symm f,
      (inv (H.map (firstVertexEdge f.op s.1))).app q y⟩⟩, ?_⟩
    refine Sigma.ext ?_ ?_
    · exact Subtype.ext rfl
    apply heq_of_eq
    simp [replacementCellsCharacteristic, bisimplicialSigmaDesc,
      replacementCellCharacteristic, SSet.stdSimplex.objEquiv, Equiv.ulift]

/-- Away from the boundary, a cell map is a degeneracy, and therefore
transports the coefficient fiber isomorphically. -/
theorem replacementCells_epi_of_notMem (n : ℕ) (p q : SimplexCategoryᵒᵖ)
    (x : ((replacementCells H n).obj p).obj q)
    (hx : x ∉ Set.range (((replacementCellsBoundaryι H n).app p).app q)) :
    Epi x.2.1.down := by
  have ha : x.2.1 ∉ (∂Δ[n]).obj p :=
    fun ha ↦ hx ⟨⟨x.1, ⟨⟨x.2.1, ha⟩, x.2.2⟩⟩, rfl⟩
  simpa [SimplexCategory.epi_iff_surjective, SSet.boundary, SSet.stdSimplex.asOrderHom] using ha

/-- Distinct cell interiors stay distinct after attachment, including their
coefficient fibers. -/
theorem replacementCells_injective_off_boundary (n : ℕ) (p q : SimplexCategoryᵒᵖ)
    (x y : ((replacementCells H n).obj p).obj q)
    (hx : x ∉ Set.range (((replacementCellsBoundaryι H n).app p).app q))
    (hy : y ∉ Set.range (((replacementCellsBoundaryι H n).app p).app q))
    (h : (((replacementCellsCharacteristic H n).app p).app q) x =
      (((replacementCellsCharacteristic H n).app p).app q) y) : x = y := by
  have := replacementCells_epi_of_notMem H n p q x hx
  have := replacementCells_epi_of_notMem H n p q y hy
  rcases x with ⟨s, ⟨a, z⟩⟩
  rcases y with ⟨t, ⟨b, w⟩⟩
  have hb : (nerve D).map a.down.op s.1 = (nerve D).map b.down.op t.1 :=
    congrArg (fun z ↦ z.1.1) h
  obtain rfl : s = t := (nerve D).unique_nonDegenerate_simplex _ a.down s rfl b.down t hb
  have hab : a.down = b.down :=
    (nerve D).unique_nonDegenerate_map _ a.down s rfl b.down s hb
  obtain rfl : a = b := ULift.ext _ _ hab
  have hf : (H.map (firstVertexEdge a.down.op s.1)).app q z =
      (H.map (firstVertexEdge a.down.op s.1)).app q w :=
    eq_of_heq (Sigma.ext_iff.mp h).2
  have hz : z = w := (mono_iff_injective _).mp inferInstance hf
  subst w
  rfl

/-- The successor attachment is an actual pushout in every bidegree. -/
theorem replacementCells_isPushout_app (n : ℕ) (p q : SimplexCategoryᵒᵖ) :
    IsPushout (((replacementCellsAttaching H n).app p).app q)
      (((replacementCellsBoundaryι H n).app p).app q)
      ((((replacementSkeleton H).map (homOfLE (Nat.le_succ n))).app p).app q)
      (((replacementCellsCharacteristic H n).app p).app q) :=
  Types.isPushout_of_isPullback_of_mono' (replacementCells_isPullback_app H n p q)
    (replacementCells_jointly_surjective H n p q)
    (replacementCells_injective_off_boundary H n p q)

/-- The enriched successor attachment is a genuine pushout of bisimplicial sets. -/
theorem replacementSkeleton_isPushout (n : ℕ) :
    IsPushout (replacementCellsAttaching H n) (replacementCellsBoundaryι H n)
      ((replacementSkeleton H).map (homOfLE (Nat.le_succ n)))
      (replacementCellsCharacteristic H n) where
  w := replacementCells_square H n
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun p ↦ by
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).2 (IsPushout.isColimit ?_)
    exact {
      w := rfl
      isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun q ↦
        (isColimitMapCoconePushoutCoconeEquiv _ _).2
          (replacementCells_isPushout_app H n p q).isColimit)⟩ })⟩

/-- The actual topological tower realizing the base-skeleton restrictions. -/
def realizedReplacementSkeleton : ℕ ⥤ TopCat.{u} :=
  replacementSkeleton H ⋙ diagonalFunctor ⋙ SSet.toTop

/-- The realized full replacement is the colimit of the realized skeletons. -/
def realizedReplacementSkeletonIsColimit :
    IsColimit ((diagonalFunctor ⋙ SSet.toTop).mapCocone (replacementSkeletonCocone H)) :=
  isColimitOfPreserves _ (replacementSkeletonIsColimit H)

/-- Actual geometric realization takes the enriched successor attachment
square to an actual topological pushout. -/
theorem realizedReplacementSkeleton_isPushout (n : ℕ) :
    IsPushout (SSet.toTop.map (diagonalMap (replacementCellsAttaching H n)))
      (SSet.toTop.map (diagonalMap (replacementCellsBoundaryι H n)))
      ((realizedReplacementSkeleton H).map (homOfLE (Nat.le_succ n)))
      (SSet.toTop.map (diagonalMap (replacementCellsCharacteristic H n))) :=
  (replacementSkeleton_isPushout H n).map (diagonalFunctor ⋙ SSet.toTop)

end CategoryTheory.TheoremA
