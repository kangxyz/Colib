# Finite-field K₂ on the original groups

## Sources and native objects

At Quillen revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`,
[`Quillen/Aglib/KTheory/MilnorK/K2/FiniteField.lean`](https://github.com/kangxyz/quillen-k-theory/blob/c561118b7795eb9780be9ed391c3251d6a4d0afd/Quillen/Aglib/KTheory/MilnorK/K2/FiniteField.lean)
proves integral Milnor vanishing for every finite field.
`Colib.KTheory.MilnorK.FiniteField` adapts that proof directly to the pinned Stacks
`MilnorKRing` and its homogeneous subgroup `MilnorKTheory F 2`.
No Aglib import, tensor-quotient replacement, or finite-coefficient reduction is used.
Library item COL-0279 records this native result.

The right-projective and upper finite-module clauses of
[`Quillen/KTheory/Field/FiniteFieldKTwo.lean`](https://github.com/kangxyz/quillen-k-theory/blob/c561118b7795eb9780be9ed391c3251d6a4d0afd/Quillen/KTheory/Field/FiniteFieldKTwo.lean)
are implemented in `Colib.KTheory.Quillen.Field.FiniteFieldKTwo` (COL-0280).
For `F : Type u` with `[Field F] [Finite F]`, the targets remain literally:

- `(ModuleCat.FiniteProjective.exactStructure.{u,u} Fᵐᵒᵖ).K 2`;
- `(abelianExactStructure (FGModuleCat.{u} F)).SmallK.{u+1} 2`.

The proof uses surjectivity of the unchanged `MilnorKTheory.toRightProjectiveKTwo`
and `MilnorKTheory.toUpperModuleKTwo`, not a newly chosen comparison or trivial model.
The native stable-fiber and kernel-generation theorems already discharge the
source's former comparison inputs. No such premise is added to finite-field vanishing.

## Proof and scope

Mathlib's finite-unit-group cyclicity reduces every degree-two product to the
square `s` of a generating symbol. Native skew symmetry gives `s + s = 0`.
If `s` were nonzero, consider the finite set of units `a` whose product symbol
with the generator is nonzero. The Steinberg relation makes the complement
`1 - a` have zero product symbol. Multiplication by the generating unit then
defines an injective self-map of that finite set. Surjectivity would force a
unit to equal zero, a contradiction. Native homogeneous-symbol generation
extends vanishing to every element of `MilnorKTheory F 2`.

The argument requires no characteristic restriction or lower bound on field
cardinality. `ColibTest.FiniteFieldKTwo` specializes all three actual groups to
both `ZMod 2` and `ZMod 3`, as well as testing the arbitrary-universe statement.
The source's lower-universe finite-module G₂ and coherent scheme G₂ conclusions
are separate comparison work, not part of these two endpoint modules.
