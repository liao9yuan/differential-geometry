# RicciFlow LaTeX Theorem Status

Source: `RicciFlow/main.tex`.

Numbering note: the LaTeX file uses one shared theorem counter per section for
theorems, lemmas, propositions, corollaries, definitions, assumptions,
black boxes, and remarks.  This is why the Bochner statements in the appendix
are numbered `14.18`, `14.19`, and `14.22`: earlier definitions and remarks in
Section 14 also increment the counter.

Distance scale:

- `0`: native `RicciFlower` theorem is closed.
- `1`: essentially done; needs a presentation wrapper or small compatibility theorem.
- `2`: finite-sum/component consumer work remains.
- `3`: real geometric producer remains, such as Ricci identity, Bianchi,
  curvature construction, or metric-compatibility product rule.
- `4`: major analytic/global Ricci-flow infrastructure remains, or only the
  old synthetic route exists.
- `5`: deliberate black box or external-scale theorem for now.

## 2026-05-11 Post-Refactor Update

The refactor moved reusable math out of `RicciFlower/Realized` and into
ordinary `RicciFlower/*` modules. In particular, the main theorem consumers now
live in `Operators.lean`, `RoughLaplacian.lean`, `Tensor/RicciIdentity.lean`,
`Curvature/Components.lean`, `Bianchi.lean`, `ScalarBochner.lean`,
`Bochner.lean`, and `LeviCivita/*.lean`.

This makes several LaTeX targets closer: the remaining work is now mostly
producer proofs, not realization-folder organization. The closest targets are
the scalar Bochner formula, the one-form Ricci identity endpoint,
Levi-Civita Hessian symmetry, the inverse-metric evolution lemma, quotient
evolution algebra, and finite-dimensional curvature algebra.

Detailed closure order and acceptance checks are recorded in
`RicciFlower/LATEX_THEOREM_CLOSURE_PLAN.md`.

## 2026-05-12 Local Closure Update

The scalar weak maximum-principle core is farther along than the earlier status
recorded: `strict_barrier_nonnegative`, the operator Laplacian-minimum input,
the Hessian-trace bridge, and the uniform/weighted value-set Lipschitz cores are
now native. The remaining scalar WMP work is presentation/interface packaging
for the exact LaTeX locally-Lipschitz phrasing.

The dimension-three algebra file now also closes the native eigenvalue form of
Lemma 10.8, `lem:Q-lower-bound`.  New scalar and volume evolution files are
present in the checkout.  The volume-evolution path has now been focused
checked and is recorded in the 2026-05-13 update below.

## 2026-05-13 Volume Evolution Update

The local RicciFlower volume stack now proves the measure/density route needed
for Ricci-flow volume evolution.  The checked native pieces include:

- `Analysis.Volume.FunctionRegularAt_const` and
  `Analysis.Volume.FunctionRegularAt_one`;
- `Analysis.Volume.MetricFamilyRegularAt.of_chartGram_timeDeriv`, the
  explicit `C^1_t C^0_x` chart-Gram bridge;
- `Realized.scalarCurvatureFromRicciTraceInFrame_realizes`;
- `RicciFlow.Evolution.Volume.volume_variation_ricciFlow_at_of_metricDeriv_canonicalScalar`;
- `RicciFlow.Evolution.Volume.total_volume_variation_ricciFlow_at_of_metricDeriv`.

Thus the formal statement

```text
d/dt int_M 1 dmu_g(t) = - int_M R dmu_g(t)
```

is native, assuming the supplied metric family satisfies the classical
Ricci-flow metric derivative equation and `MetricFamilyRegularAt`.  The latter
can now be produced from explicit continuous time derivatives of chart Gram
entries, so short-time existence and Ricci-flow analytic improvement are not
part of this volume bridge.

Remaining volume-side work is an optional convenience theorem deriving the
explicit chart-Gram derivative hypothesis from a stronger spacetime `C^1`,
smooth, or analytic metric-family predicate, plus separate maximal-interval
and extinction infrastructure.

## 2026-05-13 One-Form Ricci Identity Update

The Levi-Civita one-form Ricci identity endpoint is now closed natively.  The
checked path is:

- `Connection.oneFormRicciIdentity_algebra`, the RicciFlower-local algebraic
  bracket-form identity;
- `LeviCivita.oneFormThirdCovDerivCommAt_of_leviCivita`, the intrinsic
  Levi-Civita endpoint used by scalar Bochner;
- `Tensor.oneForm_ricci_trace_comm_of_third_comm`, the trace bridge consumed by
  the rough-Laplacian/Bochner interface.

The proof does not import external `DifferentialGeometry` or synthetic modules.
It uses smooth vector-field extensions, the realized moving-slot formula for
one-forms, Levi-Civita torsion-freeness, curvature realization, and one-form
linearity through `cotangentToDual`.

This closes the one-form Ricci identity producer for the Levi-Civita scalar
Bochner path.  The separate Ricci-tensor contracted commutator/Bianchi package
needed for Chapter 6.1 Ricci evolution remains a different frontier.

## Main Body

### Theorem 2.1, `thm:main-hamilton-3d`

Statement:

```text
If M^3 is closed, connected, and smooth, and M admits a Riemannian metric
g0 with Ric(g0) > 0, then M admits a metric of constant positive sectional
curvature. Equivalently, M is diffeomorphic to a spherical space form.
```

Status: old synthetic assembly exists as `wordly_latex_thm_main_hamilton_3d`.
There is no native unconditional `RicciFlower` theorem yet.

Distance: `5`.

Next target: replace the typed synthetic assembly by concrete Ricci-flow
solution data, analytic inputs, realized curvature, and pinching/convergence
theorems.

### Assumption 3.1, `ass:riemannian-calculus`

Statement:

```text
Assume standard smooth Riemannian tensor calculus: Levi-Civita connection,
extension of nabla to tensors, torsion-free and metric-compatible properties,
Rm from commutators, Ricci and scalar curvature as contractions, Rm symmetries,
Bianchi identities, tensor commutator identities, norms, traces, divergences,
contractions, and rough Laplacian Delta T = g^{ij} nabla_i nabla_j T.
```

Status: partially native.  Relevant files include
`RicciFlower/Realized/Connection.lean`,
`RicciFlower/Realized/Curvature.lean`,
`RicciFlower/Realized/CurvatureTensor.lean`,
`RicciFlower/Realized/CurvatureComponents.lean`,
`RicciFlower/Tensor/RSTensor/NablaOnTensors.lean`, and tensor metric files.

Distance: `3`.

Next target: close tensor Ricci identity, Bianchi/contracted Bianchi, curvature
section producers, and intrinsic tensor rough Laplacian.

### Black Box 4.2, `bb:strictly-parabolic-short-time`

Statement:

```text
A smooth strictly parabolic system on a closed manifold with smooth initial
data has a smooth short-time solution, unique in the appropriate parabolic
class.
```

Status: explicit analytic black box in the old synthetic route.

Distance: `5`.

Next target: keep as black box unless the project expands to parabolic PDE
existence.

### Theorem 4.3, `thm:rf-short-time-existence`

Statement:

```text
For every smooth Riemannian metric g0 on a closed manifold M, there exists
T > 0 and a smooth Ricci flow g(t) on [0,T) with g(0) = g0.
```

Status: old synthetic wrapper `wordly_latex_thm_rf_short_time_existence`;
native `RicciFlower/Realized/RicciFlow.lean` has solution interfaces, not the
DeTurck existence theorem.

Distance: `5`.

Next target: build a concrete DeTurck wrapper around the analytic black box and
the realized Ricci-flow solution structure.

### Black Box 5.1, `bb:maximal-rf-interval`

Statement:

```text
Starting from any smooth metric on a closed manifold, there is a unique maximal
Ricci flow g(t), t in [0,Tmax), agreeing with every other flow on common
domains and admitting no smooth extension past Tmax.
```

Status: old synthetic maximal-flow interfaces only.

Distance: `5`.

Next target: concrete maximal-interval construction, uniqueness, and terminal
time API.

### Lemma 6.1, `lem:evol-inverse-metric`

Statement:

```text
Along Ricci flow, partial_t g^{ij} = 2 Ric^{ij}.
```

Status: closed natively as `RicciFlow.evol_inverse_metric_inFrame` in
`RicciFlower/RicciFlow/Evolution/Metric.lean`, using the existing
inverse-identity differentiation theorem.

Distance: `0`.

Next target: use this theorem as the inverse-metric input for later Ricci-norm
and raised-index evolution identities.

### Lemma 6.2, `lem:evol-christoffel`

Statement:

```text
Along Ricci flow,
partial_t Gamma^k_ij =
- g^{kl} (nabla_i Ric_jl + nabla_j Ric_il - nabla_l Ric_ij).
```

Status: closed in native fixed-frame component form by
`RicciFlow.evol_christoffel_inFrame`, which projects the checked
spacetime-smooth Christoffel evolution producer to the displayed Ricci-flow RHS.

Distance: `0`.

Next target: use this as the Christoffel-variation input for Ricci and
curvature evolution identities.

### Lemma 6.3, `lem:evol-ricci`

Statement:

```text
Along Ricci flow,
partial_t Ric_ij = Delta Ric_ij + 2 R_ikjl Ric^{kl}
  - 2 Ric_i^k Ric_kj.
Equivalently,
(partial_t - Delta) Ric_ij = 2 R_ikjl Ric^{kl} - 2 Ric_i^k Ric_kj.
```

Status: native algebraic core and display projection are proved in
`RicciFlower/RicciFlow/Evolution/Ricci.lean` by
`RicciFlow.evol_ricci_inFrame_of_variation_commutators`.  The local
coordinate-frame Ricci variation producer from Christoffel evolution is checked
by `RicciFlow.ricciVariationFormulaInCoordFrameAt_of_christoffelEvolution`.
The remaining producer inputs are the substitution
`nabla A = nablaGammaDtFromNabla2RicInFrame` and the contracted
commutator/Bianchi reduction.

Distance: `2`.

Next target: prove the component substitution
`nabla A = nablaGammaDtFromNabla2RicInFrame`, then prove the contracted
commutator/Bianchi reduction.

### Corollary 6.5, `cor:ricci-lichnerowicz`

Statement:

```text
Along Ricci flow, partial_t Ric = Delta_L Ric.
```

Status: component consumer/interface in `RicciFlower/RicciFlow/Evolution/Ricci.lean`.

Distance: `3`.

Next target: package Lemma 6.3 through the Lichnerowicz definition.

### Lemma 6.6, `lem:evol-scalar`

Statement:

```text
Along Ricci flow, partial_t R = Delta R + 2 |Ric|^2.
Equivalently, (partial_t - Delta) R = 2 |Ric|^2.
```

Status: interface/consumer in `RicciFlower/RicciFlow/Basic.lean`.

Distance: `3`.

Next target: prove contraction of Ricci evolution plus inverse-metric variation
in the realized layer.

### Lemma 6.7, `lem:evol-ricci-norm`

Statement:

```text
Along Ricci flow,
(partial_t - Delta) |Ric|^2 =
-2 |nabla Ric|^2 + 4 R_ikjl Ric^{ij} Ric^{kl}.
```

Status: finite-sum consumer theorem exists as
`RicciFlower.Realized.ricci_norm_heat_eq_of_bochner_components` in
`RicciFlower/Realized/Bochner.lean`.

Distance: `3`.

Next target: supply the real Ricci time-derivative producer and the tensor
Bochner/Laplacian producer.

### Theorem 7.1, `thm:scalar-wmp-super`

Statement:

```text
For a scalar supersolution
partial_t u >= Delta_g(t) u + <X, grad u> + F(u,t),
with F locally Lipschitz and nondecreasing in u, comparison with the ODE
c' = F(c,t) preserves u >= c.
```

Status: closed natively as
`Realized.scalar_wmp_super_theorem_7_1` in
`RicciFlower/MaximumPrinciple/ScalarWeak.lean`.  The theorem uses the compact
value-set Lipschitz formulation; the book's monotonicity hypothesis is retained
as a book-facing input.  The pointwise calculus identities, compact
strict-barrier argument, operator Laplacian-minimum input, Hessian-trace
bridge, and uniform/weighted value-set Lipschitz variants are proved.

Distance: `0`.

Next target: optional interface refinement from pointwise locally-Lipschitz
time slices to a compact-value or weighted Lipschitz hypothesis.  No active
closure work remains for the proved compact-value theorem.

### Theorem 7.2, `thm:scalar-wmp-sub`

Statement:

```text
For the corresponding subsolution inequality
partial_t u <= Delta_g(t) u + <X, grad u> + F(u,t),
comparison with c' = F(c,t) preserves u <= c.
```

Status: partially native in `RicciFlower/MaximumPrinciple/ScalarWeak.lean`;
old synthetic wrapper exists.

Distance: `3`.

Next target: derive cleanly from the supersolution theorem or duplicate the
barrier proof.

### Corollary 7.3, `cor:scalar-lower-bound`

Statement:

```text
For Ricci flow on a closed n-manifold, if c0 = inf_M R(.,0), then
R(x,t) >= c0 / (1 - (2/n)c0 t)
while the denominator is positive. In particular, positive initial scalar
curvature remains positive.
```

Status: not native; synthetic/GOALS route only.

Distance: `4`.

Next target: combine scalar evolution, |Ric|^2 >= R^2/n, and scalar WMP.

### Corollary 7.4, `cor:positive-scalar-finite-time`

Statement:

```text
If R(g(0)) > 0 on a closed n-manifold, then the maximal existence time
satisfies Tmax <= n / (2 min_M R(g(0))) < infinity.
```

Status: synthetic wrapper `wordly_latex_cor_positive_scalar_finite_time`.

Distance: `4`.

Next target: port the finite-time ODE comparison and positive-Ricci-to-positive
scalar bridge.

### Theorem 7.5, `thm:hamilton-tensor-wmp`

Statement:

```text
For a symmetric 2-tensor S satisfying
(partial_t - Delta) S_ij >= X^k nabla_k S_ij + N_ij(S,g,t),
if the null-eigenvector condition holds and S(0) >= 0, then S(t) >= 0.
```

Status: synthetic `TensorWeakMaximumPrinciple` interface.

Distance: `5`.

Next target: keep as analytic tensor maximum-principle input until scalar and
evolution layers are stable.

### Black Box 7.6, `bb:scalar-strong-mp`

Statement:

```text
For a complete connected Ricci-flow background with the needed bounded geometry,
a nonnegative scalar supersolution that is not identically zero becomes
strictly positive at later times.
```

Status: synthetic strong maximum-principle interface.

Distance: `5`.

Next target: keep as analytic black box for blow-up limits.

### Lemma 7.7, `lem:limit-scalar-positive`

Statement:

```text
For a complete connected 3D blow-up limit with Ric >= 0, R >= 0, and
R(x0,0) = 1, one has R > 0 on N x (alpha,0].
```

Status: synthetic consumer of scalar strong MP.

Distance: `4`.

Next target: port after the complete-limit Ricci-flow setting and strong MP
interface exist natively.

### Lemma 8.1, `lem:3d-curvature-identities`

Statement:

```text
In dimension 3,
R_ijkl =
  g_ik Ric_jl - g_il Ric_jk
  - g_jk Ric_il + g_jl Ric_ik
  - (R/2)(g_ik g_jl - g_il g_jk).
If Ric has eigenvalues lambda_1, lambda_2, lambda_3, then
K_ij = (lambda_i + lambda_j - lambda_k)/2.
```

Status: native dimension-three component algebra is closed in
`DimensionThree.CurvatureAlgebra`, and the realized Levi-Civita component
wrapper is closed in `DimensionThree.RiemannFromRicci` as
`rm04Comp_displayedRiemannFromRicci3D_at_of_leviCivita_realizes`.

Distance: `0` for the Riemann-from-Ricci component identity.  The sectional
curvature eigenvalue presentation is still a separate wrapper/API task.

Next target: add the sectional-curvature/eigenvalue wrapper if needed by the
pinching chapter.

### Lemma 9.1, `lem:preserve-ricci-nonnegative`

Statement:

```text
For a closed 3D Ricci flow, Ric(g(0)) >= 0 implies Ric(g(t)) >= 0.
```

Status: synthetic tensor-WMP consumer.

Distance: `4`.

Next target: combine native Ricci evolution, 3D curvature algebra, and tensor
WMP.

### Lemma 9.2, `lem:preserve-ricci-pinching`

Statement:

```text
For 0 <= delta <= 1/3, if Ric(g(0)) >= delta R(g(0)) g(0), then
Ric(g(t)) >= delta R(g(t)) g(t).
```

Status: synthetic tensor-WMP consumer.

Distance: `4`.

Next target: prove shifted tensor reaction algebra and feed tensor WMP.

### Corollary 9.3, `cor:strict-positive-gives-pinching`

Statement:

```text
If M^3 is closed and Ric(g0) > 0, then there exists delta > 0, depending only
on g0, such that Ric(g0) >= delta R(g0) g0. Consequently the same pinching
holds along the Ricci flow from g0.
```

Status: not native.

Distance: `4`.

Next target: compactness of the unit tangent bundle/continuous eigenvalue
minimum plus Lemma 9.2.

### Lemma 10.4, `lem:evol-tracefree-ricci-norm`

Statement:

```text
In dimension 3, along Ricci flow and wherever R > 0,
(partial_t - Delta)|Ric^o|^2 =
  -2 |nabla Ric|^2 + (2/3)|nabla R|^2
  + (4 |Ric|^2 |Ric^o|^2 - 2 Q) / R.
```

Status: synthetic P3/P4 route.

Distance: `4`.

Next target: port trace-free decomposition, scalar evolution, Ricci norm
evolution, and the algebraic reaction reduction.

### Lemma 10.5, `lem:quotient-evolution`

Statement:

```text
For smooth spacetime functions phi >= 0 and psi > 0,
(partial_t - Delta)(phi^alpha / psi^beta)
equals the displayed product/chain-rule expression with gradient-square and
cross-gradient terms.
```

Status: synthetic algebra exists.

Distance: `2`.

Next target: port the pure scalar quotient algebra to `RicciFlower` if needed
by native pinching.

### Lemma 10.6, `lem:evol-pinching-P`

Statement:

```text
For P = |Ric^o|^2 / R^{2-eps}, 0 < eps < 1,
partial_t P =
Delta P + (2(1-eps)/R)<nabla R,nabla P>
- 2 R^{eps-4}|R nabla Ric - nabla R tensor Ric|^2
- eps(1-eps) R^{eps-4}|Ric^o|^2 |nabla R|^2
+ 2 R^{eps-3}(eps |Ric|^2 |Ric^o|^2 - Q).
```

Status: synthetic improved-pinching producer/interface.

Distance: `4`.

Next target: native trace-free Ricci evolution, quotient algebra, and
gradient-square rearrangement.

### Lemma 10.7, `lem:Q-factorization`

Statement:

```text
For Ricci eigenvalues lambda_1, lambda_2, lambda_3 and
R = lambda_1 + lambda_2 + lambda_3,
Q = sum_{i<j} (lambda_i - lambda_j)^2 (R - 2 lambda_k)^2.
```

Status: closed natively as
`DimensionThree.hamiltonCubicQ3_factorized` in
`RicciFlower/DimensionThree/PinchingAlgebra.lean`.

Distance: `0`.

Next target: port the ordered-eigenvalue lower-bound algebra for Lemma 10.8.

### Lemma 10.8, `lem:Q-lower-bound`

Statement:

```text
If R > 0 and Ric >= delta R g with delta > 0, then
Q >= 2 delta^2 |Ric|^2 |Ric^o|^2.
```

Status: closed natively in eigenvalue form as
`DimensionThree.hamiltonCubicQ3_lower_bound_ordered_nonnegative_eigenvalues`
in `RicciFlower/DimensionThree/PinchingAlgebra.lean`.

Distance: `0`.

Next target: add the geometric bridge from a Ricci eigenframe and
`Ric >= delta R g` to the ordered-eigenvalue hypotheses, when the downstream
pinching package needs the geometric statement.

### Corollary 10.9, `cor:improved-ricci-pinching`

Statement:

```text
For a closed 3D Ricci flow with Ric(g0) > 0, there exist eps > 0 and C < infinity
depending only on g0 such that |Ric^o|^2 / R^2 <= C R^{-eps}.
```

Status: synthetic P4 wrapper.

Distance: `4`.

Next target: native scalar WMP, pinching evolution, and Q lower bound.

### Lemma 11.1, `lem:finite-time`

Statement:

```text
The maximal Ricci flow starting from a closed 3-manifold with R(g0) > 0 has
finite maximal time, bounded by data from g0.
```

Status: synthetic finite-time wrapper.

Distance: `4`.

Next target: follows natively after Corollary 7.4 and maximal interval API.

### Black Box 11.2, `bb:rf-extension-criterion`

Statement:

```text
If a closed-manifold Ricci flow on [0,T) has sup_{M x [0,T)} |Rm| < infinity,
then it extends smoothly to [0,T+eta).
```

Status: synthetic/global interface.

Distance: `5`.

Next target: keep as global analytic black box.

### Lemma 11.3, `lem:finite-time-curvature-blow-up`

Statement:

```text
For a maximal Ricci flow with finite maximal time Tmax,
sup_{M x [0,Tmax)} |Rm| = infinity.
```

Status: synthetic wrapper around extension criterion.

Distance: `4`.

Next target: native wrapper once maximal interval and extension criterion APIs
are concrete.

### Corollary 11.4, `cor:ricci-controls-rm`

Statement:

```text
There exists a universal constant C3 such that on any 3D Riemannian manifold
with Ric >= 0, |Rm| <= C3 R.
```

Status: synthetic curvature algebra route.

Distance: `3`.

Next target: port 3D sectional-curvature algebra and norm comparison.

### Lemma 11.6, `lem:point-selection-rescaling`

Statement:

```text
For the maximal Ricci flow from a closed 3-manifold with Ric(g0) > 0, there
exist points/times (x_i,t_i), t_i -> Tmax, and R_i = R(x_i,t_i) -> infinity,
such that the parabolically rescaled flows satisfy
R(g^{R_i})(x_i,0) = max_{M x [-R_i t_i,0]} R(g^{R_i}) = 1.
```

Status: synthetic Section 12 interface.

Distance: `4`.

Next target: finite-time scalar blow-up plus concrete point-selection/rescaling.

### Black Box 11.8, `bb:no-local-collapsing`

Statement:

```text
Perelman's no local collapsing theorem: for a closed Ricci flow on [0,T),
there is kappa > 0 such that the flow is kappa-noncollapsed at all scales
controlled by curvature, invariant under parabolic rescaling.
```

Status: black box.

Distance: `5`.

Next target: keep as global analytic/geometric black box.

### Lemma 11.10, `lem:cgh-curvature-convergence`

Statement:

```text
Under smooth pointed Cheeger-Gromov-Hamilton convergence, pulled-back Rm, Ric,
R, |Rm|^2, |Ric|^2, and |Ric^o|^2 converge smoothly on compact subdomains and
compact time subintervals.
```

Status: synthetic convergence interface.

Distance: `5`.

Next target: requires a concrete smooth CGH convergence theory; likely remains
black-box level.

### Corollary 11.11, `cor:cgh-curvature-ratio-convergence`

Statement:

```text
If the CGH limit has R > 0 on a compact spacetime set, then the pulled-back
ratios |Ric^o|^2 / R^2 converge smoothly to the limit ratio there.
```

Status: synthetic wrapper.

Distance: `4`.

Next target: prove as consumer of CGH curvature convergence and positivity of
the scalar limit.

### Black Box 11.12, `bb:cgh-compactness`

Statement:

```text
Hamilton compactness theorem for pointed Ricci flows with uniform local
curvature bounds and basepoint noncollapsing.
```

Status: black box.

Distance: `5`.

Next target: keep as global compactness input.

### Black Box 11.14, `bb:myers`

Statement:

```text
If a complete Riemannian manifold has Ric >= (n-1)k g for k > 0, then it is
compact and has diameter at most pi / sqrt(k).
```

Status: black box in the LaTeX spine.

Distance: `5`.

Next target: possibly use mathlib if available, otherwise keep as global input.

### Lemma 11.15, `lem:3d-einstein-space-form`

Statement:

```text
If (N^3,h) is connected, Ric^o(h) = 0, and R(h) is positive somewhere, then
R(h) is a positive constant and h has constant positive sectional curvature.
```

Status: synthetic algebra route; partial realized curvature objects exist.

Distance: `3`.

Next target: native contracted Bianchi plus 3D Riemann-from-Ricci formula and
sectional-curvature API.

## Appendix Calculus Statements

### Lemma 14.2, `lem:3D Riem as Ricci and R`

Statement:

```text
If n = 3, then
R_ijkl = R_il g_jk - R_jl g_ik - R_ik g_jl + R_jk g_il
  - (1/2) R (g_il g_jk - g_jl g_ik).
```

Status: closed in native component form.  The algebraic heart is
`DimensionThree.displayedRiemannFromRicci3D_of_algebraic_curvature_symmetries`;
the realized Levi-Civita wrapper is
`DimensionThree.rm04Comp_displayedRiemannFromRicci3D_at_of_leviCivita_realizes`.

Distance: `0` for the pointwise Levi-Civita component statement.

Next target: only presentation wrappers remain, such as replacing the canonical
trace terms by separately supplied Ricci/scalar realization data in a chosen
frame if a downstream theorem needs that exact interface.

### Lemma 14.10, `lem:curvature_on_1forms`

Statement:

```text
(nabla_X nabla_Y omega)(Z) - (nabla_Y nabla_X omega)(Z)
  - (nabla_[X,Y] omega)(Z) = - omega(R(X,Y)Z).
```

Status: closed for the Levi-Civita/RicciFlower scalar-Bochner path by
`LeviCivita.oneFormThirdCovDerivCommAt_of_leviCivita`, backed by the local
algebraic identity `Connection.oneFormRicciIdentity_algebra`.

Distance: `0` for the Levi-Civita endpoint.

Next target: if needed, generalize the closed Levi-Civita moving-slot proof to
a public smooth-connection theorem with the same explicit
`ContMDiffCovariantDerivativeLocally` hypothesis.

### Theorem 14.12, `thm:ricci_identity`

Statement:

```text
nabla_i nabla_j alpha_{k_1 ... k_s}
- nabla_j nabla_i alpha_{k_1 ... k_s}
= - sum_{q=1}^s sum_m R_{i j k_q}^m
    alpha_{k_1 ... k_{q-1} m k_{q+1} ... k_s}.
```

Status: invariant interface now stated in `RicciFlower/Tensor/RicciIdentity.lean`.
The file exposes the slot-freezing one-form `oneFormAtSlot0S`, the slotwise
curvature action `curvatureAction0SAt`, the pointwise theorem shape
`Tensor0SRicciIdentityAt`, and the torsion-corrected frontier
`tensor0S_ricciIdentity_with_torsion`.  The `s = 1` specialization is checked by
`tensor0S_ricciIdentity_one`, which is equivalent to the closed one-form
identity `OneFormThirdCovDerivCommAt`.

The Levi-Civita-facing wrapper
`LeviCivita.tensor0S_ricciIdentity_of_leviCivita` is also present; it removes the
torsion term using `leviCivitaConnectionOfMetric_isTorsionFree`.

The coordinate component specialization following the displayed proof is now
stated and checked as
`Realized.tensor0S_ricciIdentity_coordFrame_of_christoffelCurv` in
`RicciFlower/Curvature/Components.lean`.  It evaluates the invariant identity
on the coordinate frame and expands each curvature action by the existing
Christoffel curvature coefficient theorem.

Distance: `1`.

Next target: prove `tensor0S_ricciIdentity_with_torsion` by the invariant
moving-slot expansion.  Do not switch to a coordinate-Christoffel proof for this
producer.

### Lemma 14.18, `ex:laplace_u_squared`

Statement:

```text
(1/2) Delta(u^2) = div(u grad u) = u Delta u + |grad u|^2.
```

Status: native theorem `half_laplacian_mul_self` in
`RicciFlower/Realized/Operators.lean`, under explicit differentiability
hypotheses.

Distance: `0`.

Next target: none for the algebraic identity; only improve presentation if
needed.

### Lemma 14.19, `lem:laplace_d_commutator`

Statement:

```text
Delta(du) = d(Delta u) + Ric(du),
where Ric acts on 1-forms by (Ric(alpha))(W) = alpha(Ric(W)).
```

Status: the one-form Ricci identity producer behind this calculation is closed
for the Levi-Civita path by
`LeviCivita.oneFormThirdCovDerivCommAt_of_leviCivita`.  The generic consumer
interface still exists as `OneFormCommutatorEvalAt`,
`oneForm_commutator_pair_of_eval`, and `roughLap_du_eq_d_lap_add_ric`; the
generic theorem `oneForm_ricci_identity_components` remains a broader
connection-level wrapper.

Distance: `1`.

Next target: connect the closed Levi-Civita endpoint directly to the exact
rough-Laplacian commutator wrapper needed by the final public Bochner theorem,
or generalize the proof to close `oneForm_ricci_identity_components`.

### Proposition 14.22, `prop:FundBochnerFormNormSq`

Statement:

```text
For any smooth function u on a Riemannian manifold,
(1/2) Delta |du|^2 =
  <du, d(Delta u)> + |nabla du|^2 + Ric(grad u, grad u).

Equivalently,
(1/2) Delta |grad u|^2 =
  <grad u, grad(Delta u)> + |nabla^(2) u|^2 + Ric(grad u, grad u).
```

Status: native consumer theorem exists:
`fundamental_bochner`, with stronger wrappers
`fundamental_bochner_of_terms` and `fundamental_bochner_of_components` in
`RicciFlower/ScalarBochner.lean`.  The Levi-Civita scalar-Bochner wrappers now
consume the closed endpoint
`LeviCivita.oneFormThirdCovDerivCommAt_of_leviCivita`.

Distance: `1`.

Next target: discharge the remaining top-level scalar Bochner wrapper frontier
in `LeviCivita/ScalarBochner.lean`, then mark the Levi-Civita Bochner theorem
as closed.

### Lemma 14.23, `lem:christoffel_evolution`

Statement:

```text
For a smooth metric family g(t) with h = partial_t g,
partial_t Gamma^k_ij =
  (1/2) g^{kl} (nabla_i h_jl + nabla_j h_il - nabla_l h_ij).
```

Status: coordinate consumers exist; full native producer is not closed.

Distance: `3`.

Next target: prove the metric variation formula in realized coordinates.

### Corollary 14.24, `cor:christoffel_evolution_RF`

Statement:

```text
Under Ricci flow,
partial_t Gamma^k_ij =
- g^{kl} (nabla_i R_jl + nabla_j R_il - nabla_l R_ij).
```

Status: consumer/interface exists via
`ricciFlow_christoffelSymbolEvolution_from_equation`.

Distance: `2`.

Next target: once Lemma 14.23 is proved, specialize with `h_ij = -2 R_ij`.

### Lemma 14.27, `lem: sing time iff max time`

Statement:

```text
A finite-endpoint Ricci flow forms a singularity at the endpoint if and only
if it is maximal.
```

Status: synthetic terminal-time interfaces.

Distance: `4`.

Next target: native maximal interval, smooth extension criterion, and terminal
singularity definitions.

### Lemma 14.29, `lem: vol extinct implies max`

Statement:

```text
If a closed connected Ricci flow becomes volume extinct at a finite time omega,
then the flow is maximal.
```

Status: no native target yet.

Distance: `4`.

Next target: maximal interval infrastructure plus a bridge from the real-valued
`int_M 1 dmu_g(t)` volume evolution theorem to the book's volume-extinction
predicate.

### Lemma 14.30, unlabeled

Statement:

```text
If a Ricci flow becomes volume extinct at finite time omega, then
sup_{M x [alpha,omega)} R = infinity. In particular, it forms a singularity.
```

Status: no native target yet.

Distance: `4`.

Next target: scalar curvature bounds, the volume-extinction-to-blow-up
argument, and the singular/maximal bridge.  The basic total-volume evolution
identity is now native.

## Immediate Native Priority

The nearest high-value theorem remains Proposition 14.22.  The one-form Ricci
identity producer for the Levi-Civita route is now closed, so the remaining
work is no longer Lemma 14.10 itself but the final scalar-Bochner wrapper and
any desired genericization from the Levi-Civita endpoint to
`oneForm_ricci_identity_components`.

Concrete next order:

1. Finish the remaining `LeviCivita/ScalarBochner.lean` wrapper frontier.
2. Decide whether to generalize the closed Levi-Civita one-form Ricci identity
   proof into `oneForm_ricci_identity_components`.
3. Promote rough Laplacian from basis-level trace predicates to an intrinsic
   tensor operation.
4. Then mark Proposition 14.22 as distance `0`.
