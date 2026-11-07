# Waldhausen composition triangles

## Implementation source and scope

The three triangle modules adapt the corresponding files in
`Quillen/Waldhausen/SConstruction/` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`:

- `NerveTriangle.lean`: evaluation of `ComposableArrows.mk₂ η θ` at the nerve coordinate,
  the unchanged S-rows, componentwise weakness, independent S/nerve reindexing, all three
  literal cylinder faces, and constancy of a triangle of constant zero diagrams.
- `WeakGridTriangle.lean`: the actual diagonal simplicial triangle of compatible weak-grid
  families, with the actual componentwise composite on its long face. The native
  `SSet.diagonalSSet` replaces the source's earlier `TheoremA.diagonalSSet` owner.
- `WeakNaturalTransformationTriangle.lean`: the actual map
  `sSet V.cof V.weq ⊗ Δ[2] ⟶ sSet W.cof W.weq` for three exact functors and two
  pointwise weak natural transformations. Its faces are exactly `δ₂ ↦ η`, `δ₀ ↦ θ`,
  and `δ₁ ↦ η ≫ θ`, using the existing native cylinders. The simplex formula uses
  the native `TypeCat.Hom.hom` application interface.

All declarations use `CategoryTheory.Waldhausen` and the existing native `Structure`,
`IsExact`, `Grid₂`, `IsSimplex₂`, `sSet`, diagonal isomorphisms and cylinder maps.
No alternate model, object bundle, equality wrapper, or comparison adapter is introduced.
The original copyright, license, author and exact pinned implementation provenance are retained.

`SConstruction/Zero.lean` extracts the unique `zeroSimplex` declaration, with its name,
namespace and body unchanged, from `KTheory/Waldhausen/Basic.lean`. The latter imports
that lower module, preserving existing clients without an alias or duplicate declaration.
The simplicial triangle therefore has no upward dependency on K-theory or realization.
The extracted definition originally derives from `Quillen/Waldhausen/KTheory.lean`
at the same source pin.

## Mathematical correspondence

Thomason–Trobaugh, *Higher algebraic K-theory of schemes and of derived categories*,
Sections 1.5.3–1.5.4, pp. 260–261, supplies background on exact functors and natural weak
equivalences. The explicit simplicial composition triangle here is a concrete refinement,
not a claim that these formulas are a verbatim theorem in that reference.

The native model is the existing unnormalized `IsZero`-diagonal S-grid model.
Neither transformation is assumed invertible. The triangle itself requires no chosen-zero
preservation. Only the fixed-zero theorem assumes all three explicit equalities
`F.obj V.zero = W.zero`, `G.obj V.zero = W.zero` and `H.obj V.zero = W.zero`.
Its conclusion fixes the entire `Δ[2]` family, not merely its vertices or edges;
uniqueness of maps to a zero object supplies constancy without extra assumptions on
transformation components at zero.

No iterated S-construction, strict chosen-zero functor category, spectrum or prespectrum
compatibility theorem is asserted. `IteratedS.Model` is not imported or duplicated.


`COL-0275` records the actual triangle and its three original faces, together with
the full fixed-zero statement. It is a coherent simplicial prerequisite for later
iterated constructions, not a spectrum theorem.
