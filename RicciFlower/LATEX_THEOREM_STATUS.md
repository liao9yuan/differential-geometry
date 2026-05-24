# RicciFlow LaTeX Theorem Status

This ledger records theorem-level status for the Hamilton notes.  It should
track current theorem names, status, and next frontiers; it should not preserve
daily work logs.

## Current Dashboard

| Area | Status |
| --- | --- |
| Section 3/14 calculus | Mostly native; no longer the main blocker. |
| Section 6 evolution | Core inverse metric, Christoffel, Ricci, scalar, frame Ricci-norm, smooth-solution Ricci-norm data, and the `smoothOfSol` upgrade are native. |
| Section 7 scalar WMP/lower bound | Native consumer path; scalar regularity from smooth solutions is available. |
| Section 9 Ricci preservation | Local algebra, strict initial selectors, theorem-7.5 consumers, canonical Ricci-flow connection/spatial-derivative producers, and the shifted pinching section with tensor-continuity producers are native; remaining work is the parabolic/full barrier producers and the tensor-level null-condition bridge. |
| Section 10 pinching | Lemma 10.4 is checked; Lemma 10.5 has checked positive-region and `alpha = 1`, `phi >= 0` side forms, but not the full book-facing hypothesis shape. Lemma 10.6 has checked raw quotient setup, book RHS rewrite, actual tensor-square setup, section-level mixed bridge, canonical solution-section packaging, and the book-facing `pinchEvol_book` theorem; the live local frontier is the later pinching estimates. |
| Section 11/12 global flow | Global analytic and compactness black boxes remain. |

## Active Native Frontiers

- Section 9 Ricci-flow application producers for the shifted pinching
  parabolic condition, full barrier/core regularity, and the tensor-level
  null-condition bridge from arbitrary first-null barrier tensors to the
  checked strict-delta eigenvalue algebra.
- Section 10 Hamilton quotient specialization and improved pinching producers.

## Closed Or Stable Native Results

- Inverse metric evolution: `RicciFlow.evol_inverse_metric_inFrame`.
- Smooth solution upgrade: `RicciFlow.smoothOfSol`.
- Christoffel evolution: fixed local-frame component theorem.
- Ricci evolution and Lichnerowicz component consumers.
- Scalar evolution: `scalarEvolOfSmooth`.
- Ricci norm evolution: canonical frame route through `(0,2)` tensor
  Bochner/product rule and `ricci_heat_mc`.
- Scalar WMP and scalar lower bound consumers.
- 3D Riemann-from-Ricci component algebra and Ricci eigenbasis selection.
- Levi-Civita one-form Ricci identity and scalar Bochner producers.
- `(0,s)` and mixed Ricci identity component algebra.

## Detailed Ledger

### Theorem 2.1, `thm:main-hamilton-3d`

Status: theorem-shaped endpoint exists in `HamiltonPositiveRicci.lean`, but it
still consumes global Section 12 producers.

Distance: `4`.

Next target: replace Section 12 endpoint assumptions one producer at a time.

### Assumption 3.1, `ass:riemannian-calculus`

Status: native lookup map.  Local tensor, coordinate, Levi-Civita, curvature,
and Bochner endpoints exist across RicciFlower files.

Distance: `0`.

Next target: maintain this as a map, not as one monolithic theorem.

### Black Boxes 4.2, 5.1

Status: short-time existence and maximal-flow interval remain global analytic
black boxes.

Distance: `5`.

Next target: only open these when DeTurck/parabolic PDE infrastructure is a
goal.

### Lemmas 6.1-6.7

Status: inverse metric, Christoffel, Ricci, scalar, frame Ricci-norm, and
smooth-solution Ricci-norm data routes have native checked consumers.
`ricciHeatDataSmooth` is now a checked assembly from the strengthened
`IsSmoothSolutionOn` fields, and `smoothOfSol` derives those fields from the
minimal metric solution predicate `IsSolutionOn`.

Distance: `0` for the existing endpoints.

Next target: reuse these producers for trace-free Ricci norm instead of
reopening Ricci norm algebra.

### Theorems 7.1-7.4

Status: scalar WMP and scalar lower-bound/finiteness consumers are native.
`scalarRegOfSmooth` supplies the regularity package from smooth solutions.

Distance: `0` for the scalar route.

Next target: optional convenience wrappers only.

### Theorem 7.5 and Black Box 7.6

Status: tensor WMP now has a checked section-backed certificate route in
`MaximumPrinciple/TensorWeak.lean`.  The local first-null scalar signs are
produced from the selected section derivatives by `strictCert_sec`,
`wmp_section_sec` is the abstract producer endpoint, and `tensor_wmp` is the
LaTeX-facing packaged theorem 7.5 entry.  Scalar strong MP remains a global
analytic black box for blow-up limits.

Distance: `0` for theorem 7.5, `5` for black box 7.6.

Next target: keep Ricci-flow application producers separate from theorem 7.5;
feed section regularity, spatial derivatives, parabolic inequality, and null
condition into `wmp_section_sec` from the appropriate application layer.

### Lemmas 8.1, 10.7, 10.8

Status: dimension-three algebra and eigenvalue inequalities are native.
The post-10.6 reaction-sign context is also native:
`DimensionThree.PinchEigen3.q_sub_nonneg` packages Lemma 10.8 as
`Q - epsilon |Ric|^2 |Ric^o|^2 >= 0` under the ordered nonnegative
eigenvalue context, `delta * R <= l3`, and `epsilon <= 2 * delta^2`.
`RicciFlow.cubicQ_pinchOn` translates that sign into the `cubicQAt` notation
used by Hamilton's Lemma 10.6.

Distance: `0`.

Next target: produce the pointwise `EigenPinchCtxOn` package from Ricci-flow
positivity/pinching data and consume the reaction sign in the post-10.6
differential inequality.

### Lemmas 9.1-9.3

Status: conditional native setup exists for preservation and strict positivity
via local algebra and unit-tangent compactness.  Lemma 9.1 and Lemma 9.2 now
have section-backed consumers through `ricci_nonneg_wmp` and
`ricci_pinch_wmp`, both consuming the generic `TensorWMPInput` package.
Corollary 9.3 has a section-backed conditional route through `PinchWMPData`.
The canonical Ricci-flow producers for theorem-7.5 connection and spatial
derivative fields are checked: `ricciCov1`, `ricciCovInf`,
`ricciMetricComp`, `ricciNablaWMP`, `ricciNabla2WMP`, and
`ricciSpatialWMP`.  The shifted pinching section is now checked as
`pinchSec`, with `pinchSec_eq`, `pinchNablaWMP`, `pinchNabla2WMP`,
`pinchSpatialWMP`, and tensor-continuity producers
`pinchSecFamilyContinuousOnSet`, `pinchSec_tangentBundle_cont`, and
`pinchSec_tensorQuadCont`.  The strict selector route is checked through
`PinchInitLt`, `pinchInitLt_*`, `pinch_init_wmp_lt`, and
`strict_pinch_*_lt`.  The strict shifted-null eigenvalue algebra is checked by
`shiftScal3_eq`, `shiftNull3`, and `pinchShiftNull_ge`.  `RicciWMPData.toInput`
builds the Ricci `TensorWMPInput` package, `PinchWMPData.toInput` /
`PinchWMPData.preserve` make the general pinching package reusable, and
`PinchFlowWMPData` fills the canonical shifted section, connection, and spatial
derivative fields.

Distance: `1-2`.

Next target: prove the remaining shifted-pinching WMP application data from
smooth Ricci-flow equations without adding endpoint assumptions: full
barrier/core regularity, the direct tensor parabolic inequality, and the
reaction-wide null-eigenvector condition.  The null-condition work should next
produce the tensor diagonalization/reconstruction bridge for a symmetric
first-null barrier tensor and connect the canonical reaction `N` to the checked
`pinchShiftNull_ge` algebra.

### Lemma 10.4, `lem:evol-tracefree-ricci-norm`

Status: checked consumer stack exists in
`RicciFlow/Evolution/ImprovedPinching.lean`.  `tfHeat_metric_smooth` handles
canonical metric curvature and internal order-one Levi-Civita smoothness.
`tfHeat_book` is the smooth-solution book-facing wrapper, and `tfHeat_sol`
is the base `IsSolutionOn` endpoint via `smoothOfSol`.

Distance: `0`.

Remaining frontier: none for Lemma 10.4 itself.  The next Section 10 work is
the Hamilton quotient specialization and pinching producer layer.

### Lemmas 10.5-10.9

Status: Lemma 10.5 now has native book-facing wrappers in
`RicciFlow/Evolution/ImprovedPinching.lean`.  `quotHeat_book` packages the
general positive-region quotient identity, `quotHeat1_book` packages the
Hamilton-ready `alpha = 1`, `0 <= phi`, `0 < psi` side theorem, and
`quotHeatDiv` gives the `/ psi^beta` display RHS on the positive-denominator
region.  The old local-pinching `PAlphaOverQBetaFormulaOn` surface remains only
a side consumer, not a home for general theorem content.  Q-factorization and
lower-bound eigenvalue algebra are native.

Lemma 10.6 has a checked raw quotient-evolution setup and a checked conditional
book-RHS rewrite.  `tfHeatTerm`, `scalarHeatTerm`, `PinchEvolOn`, and
`pinchEvol_setup` specialize the quotient identity to
`|Ric0|^2 / R^(2 - epsilon)` using Lemma 10.4 and scalar evolution inputs.
`pinchDrift_exp` proves the drift expansion, and `pinchRHS_eq_book` /
`pinchEvol_book_of_couple` rewrite the raw RHS to Hamilton's book RHS once the
tensor-square expansion for `|R ∇Ric - dR ⊗ Ric|^2` is supplied.  The actual
tensor-square setup is now partially checked: `ricciGradCoupleSq_exp_inner`
expands the square to the raw mixed contraction, `ricciGradCoupleSq_exp_mixed`
rewrites it under the mixed-gradient bridge, and `pinchEvol_book_of_mixed`
uses the real `ricciGradCoupleSq` term rather than an arbitrary supplied square
function.  The mixed bridge itself is now checked at the section-realization
level through `ricciMixed_eq_gradNorm`, `ricciMixed_eq_tfGrad`, and
`pinchEvol_sec`.  The canonical section packaging is also checked:
`ricciNablaSec`, `ricciNormDuSec`, `pinchCoupleSol`, and
`pinchEvol_solSec` remove the manual Ricci section, `nabla Ric`,
`du |Ric|^2`, inverse-basis, and norm-identification inputs.  The
base-solution theorem `pinchEvol_sol` also assembles `PinchEvolOn` from
`tfHeat_sol`, `scalarEvolOfSol`, and `pinchEvol_setup`, and produces
`|Ric^o|^2 >= 0`, spatial differentiability of `|Ric^o|^2` and `R`, and the
needed gradient-field differentiability inputs.  Its only remaining explicit
geometric region hypothesis is `R > 0`.  The cleanup theorem `pinchEvol_book`
adds the book assumptions `0 < epsilon < 1` and forwards to `pinchEvol_sol`.

Distance: `0-1`.

The 10.7/10.8 reaction-sign input for the 10.6 reaction term is now checked
through `DimensionThree.PinchEigen3.q_sub_nonneg` and `cubicQ_pinchOn`.

Next target: continue from the Lemma 10.6 equality to the later pinching
estimates and maximum-principle application by producing the needed
eigenvalue/pinching context from flow data.
The full arbitrary-exponent book-facing 10.5 statement under only nonnegative
numerator hypotheses remains unproved and should not be claimed.

### Lemmas 11.1-11.6

Status: finite-time scalar blow-up consumers are native.  Point selection and
rescaling packages still depend on global producer assumptions.

Distance: `1-4`.

Next target: keep global point-selection/rescaling separate from local
evolution identities.

### Black Boxes 11.8, 11.10, 11.12, 11.14

Status: no-local-collapsing, CGH convergence/compactness, and Myers remain
global inputs.

Distance: `5`.

Next target: do not open unless the project explicitly shifts to global
geometry/compactness.

### Appendix Section 14

Status: tensor calculus and local-coordinate appendix statements are mostly
closed natively.  Remaining work is presentation wrappers, not foundational
tensor calculus.

Next target: only package book-facing wrappers when they simplify downstream
Hamilton proofs.

## Near-Term Work Queue

1. Finish the remaining Section 9 pinching application producers: parabolic
   inequality, tensor-level null-condition bridge, and full barrier/core
   regularity for the shifted section.
2. Continue from Hamilton quotient equality to the pinching estimates.
3. Leave global analytic/compactness assumptions explicit.
