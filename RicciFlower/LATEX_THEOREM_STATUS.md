# RicciFlow LaTeX Theorem Status

This ledger records theorem-level status for the Hamilton notes.  It should
track current theorem names, status, and next frontiers; it should not preserve
daily work logs.

## Current Dashboard

| Area | Status |
| --- | --- |
| Section 3/14 calculus | Mostly native; no longer the main blocker. |
| Section 6 evolution | Core inverse metric, Christoffel, Ricci, scalar, and frame Ricci-norm routes are native; intrinsic smooth-solution Ricci-norm component data is the lower frontier. |
| Section 7 scalar WMP/lower bound | Native consumer path; scalar regularity from smooth solutions is available. |
| Section 9 Ricci preservation | Local algebra and selectors are native; tensor-WMP regularity remains analytic. |
| Section 10 pinching | Active frontier is now lower producer work in `Evolution/RicciNorm.lean`, then quotient and pinching producers. |
| Section 11/12 global flow | Global analytic and compactness black boxes remain. |

## Active Native Frontiers

- `ricciHeatDataSmooth`: lower Section 6 producer for canonical Ricci-norm
  component data from `IsSmoothSolutionOn`.
- Tensor WMP first-null scalar-sign/product-rule bridge.
- Section 10 quotient evolution and improved pinching producers.

## Closed Or Stable Native Results

- Inverse metric evolution: `RicciFlow.evol_inverse_metric_inFrame`.
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

Status: inverse metric, Christoffel, Ricci, scalar, and frame Ricci-norm
evolution have native routes.  `ricciHeatSmooth` is now a checked algebraic
consumer of `RicciHeatData`; `ricciHeatDataSmooth` is the named lower frontier
for deriving canonical Ricci-norm component data from `IsSmoothSolutionOn`.

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

Distance: `1`/`5`.

Next target: keep Ricci-flow application producers separate from theorem 7.5;
feed section regularity, spatial derivatives, parabolic inequality, and null
condition into `wmp_section_sec` from the appropriate application layer.

### Lemmas 8.1, 10.7, 10.8

Status: dimension-three algebra and eigenvalue inequalities are native.

Distance: `0`.

Next target: consume these through Section 10 producer packages.

### Lemmas 9.1-9.3

Status: conditional native setup exists for preservation and strict positivity
via local algebra and unit-tangent compactness.  Lemma 9.1 and Lemma 9.2 now
have section-backed consumers through `ricci_nonneg_wmp` and
`ricci_pinch_wmp`, both consuming the generic `TensorWMPInput` package.
Remaining dependencies are Ricci-flow application producers that feed it, not
low-level Ricci algebra.

Distance: `1-2`.

Next target: build application-layer section regularity, spatial derivative,
parabolic, and null-condition packages without adding new endpoint assumptions.

### Lemma 10.4, `lem:evol-tracefree-ricci-norm`

Status: checked consumer stack exists in
`RicciFlow/Evolution/ImprovedPinching.lean`.  `tfHeat_metric_smooth` handles
canonical metric curvature and internal order-one Levi-Civita smoothness.
`tfHeat_book` is the book-facing wrapper.

Distance: `1`.

Remaining frontier: lower producer work in
`RicciFlow/Evolution/RicciNorm.lean`.  The Section 10 wrapper now consumes
`tfLapCore`; `tfLapReg` is closed from the scalar/Ricci regularity packages,
and `ricciHeatDataSmooth` is still the canonical Ricci-norm component-data
producer from `IsSmoothSolutionOn`.

### Lemmas 10.5-10.9

Status: quotient algebra and improved pinching are not yet native in the final
book-facing form.  Q-factorization and lower-bound eigenvalue algebra are
native.

Distance: `2-4`.

Next target: after `ricciHeatDataSmooth`, port quotient evolution and assemble
the pinching estimate.

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

1. Prove `ricciHeatDataSmooth` in `RicciFlow/Evolution/RicciNorm.lean`.
2. Continue to quotient evolution and pinching estimates.
3. Keep tensor WMP first-null scalar-sign work separate from Ricci-flow
   endpoint wrappers.
4. Leave global analytic/compactness assumptions explicit.
