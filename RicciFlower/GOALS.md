# Hamilton Positive Ricci Formalization Plan

## Target Theorem

Formalize Hamilton's three-dimensional positive-Ricci route:

```text
If a closed 3-manifold admits a metric with positive Ricci curvature, then it
admits a metric of constant positive sectional curvature.
```

## Current Status

- RicciFlower-local tensor, coordinate, Levi-Civita, Ricci identity, Bochner,
  and scalar calculus layers are now mostly native.
- Section 6 evolution interfaces are largely available; `ricciHeatDataSmooth`
  is checked from the strengthened `IsSmoothSolutionOn` fields, and
  `smoothOfSol` now produces that strengthened package from `IsSolutionOn`.
- Section 7 scalar lower-bound and finite-time consumers are native.
- Section 9 local preservation algebra exists, and the canonical Ricci-flow
  connection/spatial-derivative producers now feed theorem 7.5.  The shifted
  pinching section, its canonical spatial derivatives, and its tensor
  continuity producers are checked.  The strict `0 < delta < 1/3` initial
  selector and shifted-null eigenvalue algebra are checked.  The parabolic,
  tensor-level null, and full barrier-regularity producers remain explicit.
- Section 10.4 has a checked `IsSolutionOn` endpoint.  Section 10.5 has
  checked book-facing wrappers for the positive-region quotient identity and
  the `alpha = 1`, `phi >= 0` side theorem, but the full arbitrary-exponent
  book-facing nonnegative-numerator hypothesis shape is not fully proved.
  Section 10.6 now has a checked raw quotient-evolution setup, a checked
  drift/scalar rewrite to the book RHS, checked actual tensor-square setup for
  `|R ∇Ric - dR ⊗ Ric|^2`, a checked section-level mixed bridge, and checked
  canonical solution-section packaging, and the checked book-facing
  `pinchEvol_book` theorem, whose solution-level core produces quotient
  regularity and `|Ric^o|^2 >= 0` from solution data.
  The live Section 10 work is now the later improved pinching estimates.
- Section 11/12 still contain global analytic and compactness frontiers.

## Main Dependency Ladder

### G0. Realized Foundation

Keep `SolutionOn` as candidate flow data and `IsSolutionOn` /
`IsSmoothSolutionOn` as proof packages.  Do not merge data and proof
predicates.  Interval-aware work should keep ordinary flow times separate from
terminal/maximal ambient times.

### G1. Metric, Operators, And Compact Minimum Calculus

Closed pieces include scalar WMP consumers, scalar regularity from smooth
solutions, metric variation bounds interfaces, scalar lower bound, and
finite-time scalar blow-up consumers.

Remaining work is mostly upstream analytic or global, not basic operator
calculus.

### G2. Levi-Civita Connection And Curvature

Levi-Civita smoothness, torsion/metric compatibility, curvature symmetries,
Riemann/Ricci realization, and local-frame/component bridges are native.

Do not import `DifferentialGeometry/Synthetic` for these endpoints.

### G3. Ricci Identity And Bochner

The covariant `(0,s)` Ricci identity, mixed component algebra, rough Laplacian
interfaces, and scalar Bochner consumers are present.  Future work should
consume invariant tensor/curvature-action APIs rather than unfold low-level
slot algebra.

### G4. Short-Time And Maximal Ricci Flow

Short-time existence, maximality, extension criteria, and nonextension past
`Tmax` remain global analytic frontiers.  Keep them as explicit black boxes
until the project intentionally opens parabolic PDE existence.

### G5. Ricci-Flow Evolution Equations

Native routes exist for inverse metric, Christoffel symbols, Ricci, scalar,
frame Ricci norm, smooth-solution Ricci-norm data, and the `smoothOfSol`
upgrade from `IsSolutionOn` to `IsSmoothSolutionOn`.  The Section 10 Hamilton
quotient specialization now has a raw checked setup, checked scalar rewrite to
the book RHS, checked section-level square/mixed bridge, and canonical
solution-section packaging.  The base-solution theorem now assembles
`PinchEvolOn` and produces the quotient regularity and `|Ric^o|^2 >= 0`
inputs from solution data; the next local target is the pinching estimate layer.

### G6. Maximum Principles

Scalar WMP work is native.  Tensor WMP theorem 7.5 has a section-backed input
package, and Section 9 now produces the canonical Ricci connection and spatial
derivative fields from a Ricci-flow solution candidate.  The shifted pinching
section `Ric - delta R g` now has checked section, spatial-derivative, and
tensor-continuity producers, plus strict `0 < delta < 1/3` initial-selector
wrappers.  The remaining frontiers are application-side parabolic, tensor-level
null, and full barrier-regularity producers for the shifted tensor.

### G7. Positive Ricci Preservation And Pinching

Dimension-three algebra is native.  Section 9 now has checked
`RicciWMPData.toInput`, `ricci_nonneg_sol`, `PinchWMPData.toInput`, and
`PinchWMPData.preserve` for the theorem-7.5 package route.  The shifted
pinching section is checked as `pinchSec`, with `pinchSec_eq`,
`pinchNablaWMP`, `pinchNabla2WMP`, `pinchSpatialWMP`, and the continuity
producers `pinchSecFamilyContinuousOnSet`, `pinchSec_tangentBundle_cont`, and
`pinchSec_tensorQuadCont`.  `PinchFlowWMPData` fills the canonical shifted
section, connection, and spatial derivative fields into the older pinching WMP
package.  The strict selector route is checked through `PinchInitLt`,
`pinch_init_wmp_lt`, and the `strict_pinch_*_lt` wrappers, and the strict
shifted-null eigenvalue algebra is checked through `pinchShiftNull_ge`.  The
remaining Section 9 work is to prove its parabolic, tensor-level null, and full
barrier-regularity inputs from Ricci-flow data.  Lemmas 10.7 and
10.8 now also expose the
Hamilton-ready reaction context: `DimensionThree.PinchEigen3.q_sub_nonneg`
and the flow-facing `cubicQ_pinchOn` show
`Q - epsilon |Ric|^2 |Ric^o|^2 >= 0` from ordered nonnegative eigenvalues,
`delta * R <= l3`, and `epsilon <= 2 * delta^2`.  Lemma 10.5 quotient evolution is native on
the positive region, with checked book-facing wrappers and an `alpha = 1`,
`phi >= 0` side theorem for Hamilton's quotient direction.  The full
arbitrary-exponent nonnegative numerator form is not fully proved.  Lemma 10.6
has a checked raw quotient-evolution setup, a checked conditional book-RHS
rewrite, and checked tensor-square setup using the actual
`ricciGradCoupleSq`.  The mixed-gradient bridge is checked for concrete Ricci
sections via `pinchEvol_sec`, and canonical solution-section packaging is
checked through `pinchEvol_solSec`.  The solution-level theorem
`pinchEvol_sol` now produces the raw quotient setup, quotient regularity, and
`|Ric^o|^2 >= 0` from `IsSolutionOn`; its remaining explicit geometric region
hypothesis is scalar positivity `R > 0`.  The book-facing cleanup theorem
`pinchEvol_book` adds the book range `0 < epsilon < 1`.  The remaining
important local frontier is producing the eigenvalue/pinching context from
Ricci-flow solution data and applying the maximum-principle pinching estimate
following Lemma 10.6.

### G8. Convergence To Constant Positive Curvature

Point-selection, noncollapsing, Hamilton compactness, curvature convergence,
and the topological handoff remain global-scale inputs.

## Black-Box Policy

Black-box only genuinely hard analytic/global facts:

- short-time existence and DeTurck analytic theory;
- maximal interval and extension criteria;
- no-local-collapsing;
- Cheeger-Gromov-Hamilton compactness;
- Myers/topological handoff when outside local RicciFlow goals.

Do not black-box tensor algebra, coordinate projection, curvature symmetry,
Levi-Civita smoothness, or finite-dimensional Ricci algebra.

## Immediate Next Work

1. Produce the remaining Section 9 shifted-pinching application data:
   parabolic inequality, tensor-level reaction-wide null bridge, and full
   barrier/core regularity.
2. Continue from Lemma 10.6 equality to the improved pinching estimates.
3. Keep global Section 11/12 producers explicit and separate from local
   tensor/evolution work.
