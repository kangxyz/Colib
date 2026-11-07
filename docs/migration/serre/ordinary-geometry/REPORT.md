# Ordinary Serre kernel geometry

Source: Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd, the seven SerreClass modules listed in declaration-map.json. Baseline: serre-kzero-native-a36cec7 (a36cec736).

Implemented all 53 explicitly named source declarations in seven native modules under Colib.CategoryTheory.Abelian.SerreClass, namespace CategoryTheory.Abelian.SerreLocalization. No exact-category, Q-category, Quillen import, adapter package, parallel model, axiom, or sorry is introduced. The image poset is now named SerreImagePoset (and its corresponding top instance), to avoid the Q-specific Auxiliary name. Kernel inclusion and its limiting-fork proof moved from KernelPushout into OverKernel, their natural dependency owner. Object and hom universes are independent throughout, strengthening the source's equal-universe restriction.

## Native API reuse and upstream search

Pinned Mathlib's Comma.Over.Pullback and Limits.Constructions.Over.Connected provide the actual Over.pullback / Over.map functors, adjunction counit, and preserved pullbacks. The kernel remains definitionally pullback along zero followed by Over.forget. No substitute kernel functor or transfer equivalence is used.

Limits.Shapes.Kernels supplies isKernelCompMono and conePointUniqueUpToIso; Abelian.Basic supplies epiIsCokernelOfKernel / monoIsKernelOfCokernel and epiDesc; Abelian.CommSq supplies mono_of_isPullback_of_mono. The pushout object and all comparison maps remain the original native pushout, pushout.desc, inclusions, and universal-property isomorphisms, including their literal projection and kernel formulas.

Subobject.Limits supplies imageSubobject, factorThruImageSubobject, imageSubobject_comp_le, and the Epi instance on its ofLE comparison. Its imageSubobject_iso_comp only covers isomorphism precomposition; the retained epi-precomposition theorem adds the required abelian case. The explicit import replaces a former accidental exact-category transitive import.

Serre membership no longer depends on the canonical quotient or equal universes: overKernel_mem follows immediately from native kernel-fork uniqueness and hX.1. Image support follows from the native epimorphic cokernel.map and hX.2. MorphismProperty supplies isoModSerre base-change stability and epi/mono reductions. These eliminate the source quotient-Abelian instance and annihilation detour outright.

Search included pinned Mathlib Abelian, Comma, Limits, Subobject and pinned Stacks Abelian.CommSq. No existing complete slice-kernel/prescribed-extension comparison API replaced this slice. Stacks' bicartesian helpers are not duplicated.

## Validation

build.sh uses only the shared serial Lean wrapper and existing baseline/package/filtered-realization artifact overlays. Seven modules pass with autoImplicit=false and warningAsError=true. ColibTest/SerreKernelGeometry.lean tests definitional native objects, epimorphism/monomorphism hypotheses, change-of-base isomorphisms, Serre membership, actual kernel formulas, image support, and pullback epimorphisms at independent universes. The four key axiom checks report only propext, Classical.choice, Quot.sound.

No mathematical or dependency blocker remains for this closed ordinary geometry slice. No shared repository or git state was modified, and no dependency caches were copied. Publication/root imports and catalog registration are left to the integrating parent.
