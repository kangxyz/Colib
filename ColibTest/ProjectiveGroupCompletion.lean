/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveZeroFiberEquivalence
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionComma
public import Colib.Algebra.Category.ModuleCat.FiniteProjectiveExtensionSpanComma
public import Colib.CategoryTheory.GroupCompletion.IteratedCommaAdjunction
public import Colib.CategoryTheory.Subdivision.Initial

/-! # Native projective group-completion maps and their categorical fibers -/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open ModuleCat.FiniteProjective
open scoped MonoidalLeftAction
attribute [local instance] categoryDirectSumMonoidal directSumMonoidal
  extensionFiberDirectSumAction

namespace ColibTest.ProjectiveGroupCompletion

variable (R : Type u) [Ring R]

example : (completionZeroIsoFiberEquivalence R).functor =
    completionZeroIsoFiberEntry R := rfl

example (A B : IsoCategory R) :
    (completionIdentityEntry R).obj (completionPair R A B) =
      localizedExtensionPair R A ((exactStructure R).identityExtension B.of) := rfl

example (A : IsoCategory R) (x : (exactStructure R).ExtensionTotal) :
    (localizedExtensionProjection R).obj (localizedExtensionPair R A x) =
      (exactStructure R).extensionProjectionQObj x := rfl

example (A : IsoCategory R) {x y : (exactStructure R).ExtensionTotal} (f : x ⟶ y) :
    (localizedExtensionProjection R).map (localizedExtensionOriginalHom R A f) =
      (exactStructure R).extensionProjectionQMap f :=
  localizedExtensionProjection_originalHom R A f

example : (completionZeroIsoFiberEntry R).IsEquivalence := inferInstance

example (b : QConstruction (exactStructure R).deflation (exactStructure R).inflation) :
    IsoFiber.toStructured (localizedExtensionProjection R) b ⊣
      localizedExtensionCommaRetraction R b :=
  localizedExtensionFiberCommaAdjunction R b

example {X Y : ModuleCat.FiniteProjective.Category.{u, u} R}
    (s : Span (exactStructure R).deflation (exactStructure R).inflation X Y) :
    localizedExtensionSpanTransport R s ⋙ localizedFixedExtensionEntry R X ⟶
      localizedFixedExtensionEntry R Y ⋙ StructuredArrow.map
        (T := localizedExtensionProjection R)
        (QConstruction.mkHom (exactStructure R).deflation (exactStructure R).inflation s) :=
  localizedFixedExtensionSpanComma R s

example {X Y : GroupCompletionCategory R} (f : X ⟶ Y) :
    completionGrade R X = completionGrade R Y := completionGrade_map R f

end ColibTest.ProjectiveGroupCompletion
