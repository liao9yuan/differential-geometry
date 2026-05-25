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
  selector, shifted-null eigenvalue algebra, and shifted-section core
  regularity package are checked.  The WMP null interface now requires
  symmetric bilinear PSD inputs, and the off-diagonal first-null block reaction
  algebra is checked.  The raw-bilinear-to-bundled `(0,2)` tensor bridge,
  invariant `rm04OfRic3At`, canonical `ricciReaction3At` / `shiftNAt`, their
  orthonormal component theorems, and the canonical `shiftNRaw` null condition
  are checked.  The direct shifted parabolic producer is checked as
  `pinchParabolic`, the canonical small-barrier reaction control is checked as
  `pinchSmallLip`, and `PinchFlowWMPData.ofShiftNClosed` now assembles the
  shifted tensor WMP data from smooth Ricci-flow hypotheses.  The
  `delta = 0` endpoint now gives checked Ricci nonnegativity via
  `ricci_nonneg_sol_closed`, and Hamilton's rescaled Ricci nonnegativity
  package is wired through `ham3_rescaled_ric_nonneg`.
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
  The live Section 10 work is now the proof of the native improved pinching
  estimate theorem `pinchEstimate_sol`.
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
wrappers and core WMP regularity from supplied barrier regularity.  The tensor
WMP null predicates now require symmetric bilinear PSD inputs, and raw section
and barrier tensors produce the bilinearity needed by the certificate stack.
The application-side small-barrier reaction-control producer for the shifted
tensor is now checked by `pinchSmallLip`, and the full barrier package is
`pinchBarrierReg`.  The raw-to-bundled bridge is available through
`Tensor02RealizesRawAt`, `tensor02OfRawAt`, and
`Tensor02ReactionAt.toRawSymm`; the canonical raised-contraction reaction core
is now checked through `ricciReaction3At`, `shiftNAt`, `shiftNRaw`, and the
orthonormal component theorems ending in `shiftNRaw_realizes_block`.  The
arbitrary first-null geometry is checked through `NullOrthonormalBasis3At`,
`exists_nullOrthonormalBasis3At`, and `shiftNRaw_null_symm`.
The direct parabolic path is now checked as `pinchParabolic`.
`ricciQuadDeriv_coord` lifts coordinate
Lemma 6.3 to arbitrary quadratic Ricci evaluations, `pinchQuadDeriv_coord`
combines that with scalar evolution and `partial_t g = -2 Ric`, and
`ricciRoughTrace_coord`, `scalarHessTrace_eq_lap`, and `pinchHeat_coord`
identify the explicit zero-drift WMP heat operator with the coordinate rough
trace plus `Delta R` metric term.  The coordinate half of the reaction bridge
is now checked: `ricciActualReactAt` packages the actual zero-order reaction
`-2 Rm04*Ric - 2 Ric^2`, and `ricciCoordReact_eq_actual` proves
`pinchCoordReact`'s Ricci part is that actual tensor reaction on `v,v`.
The checked convention bridge now identifies actual signed `Rm04` contractions
with the `rm04OfRic3At` contraction used by `ricciReaction3At`, and
`shiftNRaw_pinchCoordReact` closes
`shiftNRaw(pinchSec)(v,v) = pinchCoordReact`.  `PinchFlowWMPData.ofShiftNDirect`
feeds the direct parabolic producer into the canonical shifted WMP package.
`PinchFlowWMPData.ofShiftNClosed` further removes the external barrier
regularity input by calling `pinchBarrierReg`.
The old canonical shifted `pinchNabla*` route remains removed;
`PinchFlowWMPData` uses explicit `pinchNablaModel` / `pinchNab2ModelSec`
fields, with `pinchSpatialModel` proving their `TensorSpatialDerivs` input.
The closed Section 9 package is now consumed by solution-level preservation
wrappers and by the Hamilton endpoint layer through `ham3_pinch9` and
`ham3_rescaled_ric_nonneg`.

### G7. Positive Ricci Preservation And Pinching

Dimension-three algebra is native.  Section 9 now has checked
`RicciWMPData.toInput`, `ricci_nonneg_sol`, `PinchWMPData.toInput`, and
`PinchWMPData.preserve` for the theorem-7.5 package route.  The shifted
pinching section is checked as `pinchSec`, with `pinchSec_eq`,
the explicit derivative fields `pinchNablaModel` / `pinchNab2ModelSec`, and
the continuity producers `pinchSecFamilyContinuousOnSet`,
`pinchSec_tangentBundle_cont`, and `pinchSec_tensorQuadCont`.
`PinchFlowWMPData` fills the canonical shifted section, connection, explicit
derivative fields, and checked `TensorSpatialDerivs` proof into the older
pinching WMP package.
The strict selector route is checked through `PinchInitLt`,
  `pinch_init_wmp_lt`, and the `strict_pinch_*_lt` wrappers, and the strict
  shifted-null eigenvalue algebra is checked through `pinchShiftNull_ge` and
  the compact target `shiftReact3_nonneg`.  The off-diagonal first-null block
  target is checked through `stdRmOfRic3`, `shiftBlockS3`,
  `shiftRicBlock3`, `shiftReactBlock3_eq`, and
  `shiftReactBlock3_nonneg`.
  `pinchSecCore` and `PinchFlowWMPData.ofBarrier` now produce the shifted-section
  core WMP regularity package from smooth solution data once
  `TensorBarrierRegularityOn` is supplied.  `PinchFlowWMPData.ofSymmNull`
  also adapts the natural symmetric-input null interface to the legacy raw WMP
  null field when the reaction ignores skew input, and
  `shiftNullSymm_of_block` turns a concrete `ShiftBlockReactRealizes`
  component realization into the symmetric null condition.  `ShiftBlockAt`,
  `raw_null_of_smul`, and `shiftBlockOfNull` now prove the actual shifted
  first-null block shape in any supplied orthonormal basis whose first vector
  is a nonzero normalization of the null direction.  The tensor-backed
  compatibility layer is checked, and `shiftNullSymm_of_block_scaled` now
  records the `r^2` scaling needed for arbitrary WMP null vectors.  The
  basis-local tensor model `shiftNAtBasis` bundles the finite shifted reaction
  components in a supplied orthonormal basis, realizes `shiftReactBlock3` on
  first-null blocks, and has the checked scaled bridge `shiftNBasisScaled` for
  arbitrary null vectors proportional to the adapted first basis vector.  The
  canonical tensor-backed reaction has now been migrated off that local model:
  `ricciReaction3At`, `shiftNAt`, and `shiftNRaw` are checked, and
  `shiftNAt_comp_orthonormal`, `shiftNAt_comp_shiftBlock`,
  `shiftNRaw_realizes_block`, and `shiftNScaled` identify the canonical
  reaction with the shifted first-null block algebra.
  `NullOrthonormalBasis3At`, `exists_nullOrthonormalBasis3At`, and
  `shiftNRaw_null_symm` close the canonical symmetric null condition, and
  `PinchFlowWMPData.ofShiftN` feeds it into the shifted WMP package.  The
  direct parabolic input is checked by `pinchParabolic`.  The barrier
  regularity input is now checked by `pinchBarrierReg`, and
  `PinchFlowWMPData.ofShiftNClosed` packages null condition, direct parabolic
  inequality, spatial derivative realization, and barrier regularity from
  smooth Ricci-flow data.  `pinch_sol_closed`, `pinch_init_sol_lt`, and
  `strict_pinch_sol_lt` consume this package for smooth solutions, and
  `pinch_sol_closed_nonneg` / `ricci_nonneg_sol_closed` consume the
  `delta = 0` endpoint for Ricci nonnegativity.  `ham3_pinch9` and
  `ham3_rescaled_ric_nonneg` wire these Section 9 results into the Hamilton
  positive-Ricci endpoint.
  Lemmas 10.7 and
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
`pinchEvol_book` adds the book range `0 < epsilon < 1`.  The native estimate
interface now lives in `ImprovedPinching/Estimate.lean`: `PinchEstimateOn`
records the domain-aware estimate, carrier-extension helpers provide the
all-real display functions, and `ham3_pinch_imp` consumes this checked display
wrapper.  The remaining important local frontier is the proof of
`pinchEstimate_sol`, which must produce ordered `PinchEigen3` pointwise data
from Section 9 Ricci nonnegativity and shifted pinching, then apply the scalar
maximum principle to the 10.6 drifted subsolution.

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

1. Prove `RicciFlow.pinchEstimate_sol`: first close the tensor/eigenvalue
   bridge to ordered `PinchEigen3`, then feed the 10.6 subsolution inequality
   into the scalar weak maximum principle.
2. Keep global Section 11/12 producers explicit and separate from local
   tensor/evolution work.
