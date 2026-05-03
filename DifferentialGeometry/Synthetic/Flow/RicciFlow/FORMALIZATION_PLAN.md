# RicciFlow formalization plan

This note compactly records how `RicciFlow/main.tex` maps into the current Lean
source tree. The project is already organized around a synthetic tensor
calculus, so the main implementation path should stay invariant and tensorial.
Local-coordinate calculations from the LaTeX are treated as proof blueprints or
as later realization lemmas, not as the core API.

## Current project shape

The Ricci flow source lives under
`DifferentialGeometry/Synthetic/Flow/RicciFlow/`. The existing core is:

- `Basic.lean`: Ricci flow data, Riemann tensor, Ricci form, Levi-Civita at each
  time.
- `Evolution/Connection.lean`: the Ricci-flow specialization of the Palatini
  connection variation. This is the Lean form of the first variation of
  Christoffel symbols.
- `Evolution/RiemannVariation.lean`, `RiemannLaplacian.lean`,
  `RiemannEvolution.lean`: variation and heat-type evolution of the Riemann
  tensor, including a Hamilton-style quadratic term.
- `Evolution/Ricci.lean`: currently contains the pointwise extraction interface
  for time derivatives of Ricci.
- `Evolution/ScalarCurvature.lean`: proves the partial scalar curvature formula
  `d_t R = 2 |Rc|^2 + tr_g(d_t Rc)`.
- `Calculus.lean`: bundles the common Ricci-flow hypotheses and exposes wrapper
  theorems.

Known gaps are full Ricci evolution, closing the scalar formula with the
contracted Bianchi/trace identity, Ricci norm and trace-free Ricci evolution,
maximum principles, three-dimensional curvature algebra, pinching estimates,
global blow-up/compactness inputs, and the final Hamilton theorem assembly.

## LaTeX-to-Lean roadmap

The first target from `main.tex` is the first variation of Christoffel symbols.
In Lean this should remain the invariant statement already developed through
Palatini:

- generic variation: `DifferentialGeometry/Synthetic/Operator/Variation.lean`;
- Ricci-flow specialization:
  `DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Connection.lean`.

The next tensor-evolution targets are:

- `Evolution/Ricci.lean`: full Ricci evolution as an equation interface, then as
  a theorem once the needed contraction and commutator identities are available.
- `Evolution/Lichnerowicz.lean`: named Lichnerowicz-laplacian interface for
  `(0,2)` tensors.
- `Evolution/ScalarCurvature.lean`: close
  `d_t R = Delta R + 2 |Rc|^2` from the trace identity for `d_t Rc`.
- `Evolution/RicciNorm.lean`: Ricci norm, trace-free Ricci tensor, and evolution
  interfaces for pinching.

The three-dimensional and analytic layers should be separated:

- `DimensionThree/CurvatureAlgebra.lean`: three-dimensional curvature algebra,
  Riemann-from-Ricci formula, sectional/eigenvalue identities, and control of
  `Rm` by `Rc`.
- `DimensionThree/Pinching.lean`: positivity, pinching cones, Hamilton's
  pinching quantity, cubic reaction terms, and improved pinching.
- `Synthetic/Analysis/Parabolic/`: scalar and tensor maximum-principle
  interfaces.
- `Global/`: short-time existence, maximal interval, extension criterion,
  blow-up, noncollapsing, compactness, and Myers-type inputs.
- `HamiltonThreeManifold.lean`: final assembly target for Hamilton's positive
  Ricci theorem in dimension three.

## Coordinate strategy

Mathlib has useful infrastructure for coordinate work:

- charts and tangent coordinates: `extChartAt`, `chartAt`,
  `tangentCoordChange`, `mfderiv`;
- local frames and coefficients: `LocalFrame` and `localFrame_coeff`;
- tangent-bundle trivializations and coordinate changes;
- covariant derivative infrastructure, especially
  `CovariantDerivative.difference`.

Mathlib does not currently provide a ready-made Christoffel/Ricci/Levi-Civita
curvature API matching the coordinate formulas in `main.tex`. Because of this,
the synthetic proof path should not wait for normal coordinates. If raw
coordinates are needed later, place that bridge under
`DifferentialGeometry/Synthetic/Realization/Coordinates/`, define local
connection coefficients in a frame, and model normal coordinates at a point as a
local-frame normalization hypothesis until a stronger manifold-level theorem is
available.

Current status: `Synthetic/Realization/Coordinates/Christoffel.lean` defines a
minimal frame-based Christoffel API for a mathlib `CovariantDerivative`:
pointwise coefficients, the frame-expansion lemma, tensorial
connection-difference coefficients, and a vanishing-at-a-point predicate for
normal-coordinate arguments. Trivialization users should pass `e.localFrame b`
and `e.isLocalFrameOn_localFrame_baseSet I 1 b` to the frame API.

## Implementation discipline

Prefer theorem interfaces or typeclasses for analytic/geometric black boxes.
Avoid `sorry` in new roadmap modules. The implementation can use classes for
short-time existence, maximum principles, compactness, noncollapsing, and Myers
until those analytic proofs are formalized.

Targeted compile checks for each phase:

```text
lake env lean DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/Connection.lean
lake env lean DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/ScalarCurvature.lean
lake env lean DifferentialGeometry/Synthetic/Flow/RicciFlow/Evolution/RiemannEvolution.lean
lake build
```
