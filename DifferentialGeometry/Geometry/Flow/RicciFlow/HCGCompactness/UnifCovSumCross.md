# UnifCovSumCross — item-6 statement S0 design note

Session 1 (2026-07-24, LANE C item-6 S0 executor, Opus) in worktree
`C:/Users/liao9/.codex/worktrees/e87b/...`, branch `codex/analytic-producers-e87b`.
Spec = `ShortTime/UNIF_ITEM6_RECON.md` §S0 (statement `covsum_cross_unif`) + §3 (route
table).  This leaf is the `HCGCompactness`-homed S0 (NOT the recon §5 `Analysis/Sobolev/
CrossMetric/` home — corrected by Finding C of `UnifCurvatureJetBound.md`: S0's hypotheses
use `MetricCovDerivOrderBoundOn`, which lives in `HCGCompactness/AllTimesBounds.lean`,
DOWNSTREAM of `Analysis/`, so S0 cannot live in `Analysis/`).

## Target (S0, order-generic; the derivative order `n` is the parameter)

For `Λ`-comparable `g₀, gBase` with `MetricCovDerivOrderBoundOn` jets `≤ Λ`, the two-sided
covariant-derivative-sum equivalence at derivative order `n`:
```
∑_{j≤n} ‖∇^{g₀,j} T‖_{L²(g₀)}  ≍_{C(Λ,n)}  ∑_{j≤n} ‖∇^{gBase,j} T‖_{L²(gBase)}
```
where `‖∇^{g,j}T‖_{L²(g)} = ‖iteratedCovGrad g 0 s j T‖` (RS L² norm, base valence `(0,s)`;
consumers use `s=2`), and `‖·‖² = ∫ riemannianFiberNormSq g 0 (s+j) x (·.toSection x)
d(riemannianVolumeMeasure g)`.  Two theorems `covsumCross_le` / `covsumCross_ge`.

## Comparability predicate (REUSE — do not re-define)

`HCGCompactness.MetricUniformEquivalentOn K gRef h C` (`AllTimesBounds.lean:601`):
`1 ≤ C ∧ ∀ x∈K, ∀ v, C⁻¹·gRef(v,v) ≤ h(v,v) ∧ h(v,v) ≤ C·gRef(v,v)`.  This IS Λ-comparability
with `C = Λ`, `gRef = gBase`, `h = g₀`.  Symmetry helper `metricUniformEquivalentOn_symm`;
any two metrics on compact `M` are equivalent (`metricUniformEquivalentOn_of_compact`).

## Route (three levels, per recon §3) — and where each stands

| level | content | status |
|---|---|---|
| **fiber** | `\|·\|_{g₀} ≍_{√Λ per slot} \|·\|_{gBase}` (Λ^s for a `(0,s)` tensor) | **EXISTS** (0S currency) |
| **volume** | `dV_{g₀} ≍_{Λ^{n/2}} dV_{gBase}` | **MISSING** (Loewner→det gap) |
| **derivative** | `∇^{g₀,j}T = ∇^{gBase,j}T + (Γ-diff insertions)`, iterated | **MISSING** (main frontier) |
| (currency) | RS `riemannianFiberNormSq g 0 s` ↔ 0S `normSq0S g x s` | **other lane** (`normBridge`) |

### Fiber level — EXISTS (0S currency), constant `Λ^s`
- `normSq0S_upper_le_of_equiv g h x s (1≤C) (hcomp) A : normSq0S h x s A ≤ C^s·normSq0S g x s A`
  (`Tensor/RSTensor/Tensor0SRiemannian/Comparison.lean:633`); `_lower_le_of_equiv:651`;
  two-sided `normSq0S_le_of_metric_equiv:672`; `sqrt_normSq0S_le_of_metric_equiv:699`.
- HCG wrappers keyed on `MetricUniformEquivalentOn` already exist at order 3:
  `sqrt_normSq0S_three_le_of_metricUniformEquivalentOn`, plus
  `exists_diagInv_of_metricUniformEquivalentOn` (simultaneous diagonalization) — `AllTimesBounds`.
- Constant per slot = `√Λ`; a `(0,s)` tensor pays `Λ^{s/2}` on the norm, `Λ^s` on the square.

### Volume level — MISSING, explicit `Λ^{n/2}`.  Located but NOT built.
`riemannianVolumeMeasure g = riemannianMeasure g (chartAtlasPOU)` (`Invariance.lean:423`);
`chartDensity g x₀ x = √det(chartGramMatrix g x₀ x)` (`ChartDensity.lean:75`);
`chartGramMatrix_apply g x₀ x i j = g.inner x (chartBasisVecFiber i)(chartBasisVecFiber j)`
(`Geometry/Metric/ChartGram.lean:224`, `rfl`); `chartGramMatrix_posDef`.
The integrate step is committed: `chart_lintegral_le q h α C hC (hdensity: chartDensity h α x
≤ C·chartDensity q α x) hF` (`CompactVolumeEquiv.lean:195`) + the POU-sum lift pattern of
`volume_uniform_equiv:342`.
The ONE genuinely-missing piece: **Loewner→determinant** `chartGram g₀ ≤ Λ·chartGram gBase
(as quad forms) ⟹ det(chartGram g₀) ≤ Λ^n·det(chartGram gBase)`, hence `chartDensity g₀ ≤
Λ^{n/2}·chartDensity gBase`.  `CompactVolumeEquiv.lean:9` explicitly records that the existing
`volume_uniform_equiv` was built to AVOID this ("no matrix Loewner-to-determinant estimate
is needed") — so it is a real linear-algebra gap.  Mathlib `Matrix/PosDef.lean` has
`det_nonneg`/`det_pos` (via `det_eq_prod_eigenvalues`) but no `A ≤ B ⟹ det A ≤ det B`.
Proof route (next session): `B := Λ·chartGram gBase` PosDef, sqrt `S := B.sqrt`, congruence
`S⁻¹ A S⁻¹ ≤ I`, `det(S⁻¹AS⁻¹) = det A/det B ≤ 1` (PSD with eigenvalues ≤ 1); OR reuse the
`exists_diagInv_of_metricUniformEquivalentOn` eigen-data and `Matrix.det_eq_prod_eigenvalues`.

### Derivative level — MISSING, the MAIN frontier (recon §4: medium, the connDiff assembly).
`∇^{g₀}T = ∇^{gBase}T + A⋆T`, `A = connectionDifferenceTensorAt (LeviCivita g₀)(LeviCivita
gBase) x` (Christoffel difference, `(1,2)`), controlled by `‖A‖_{gBase} ≤ metricDerivNorm 1
g₀ gBase gBase` (Koszul).  ONE-derivative machinery EXISTS and is assembled for the scalar
Hessian in `Analysis/Spectral/Intrinsic/Garding/CrossMetricEnergy.lean` `cross_point_le`:
`hess_sub_conn` (change of connection), `connOut_norm_le` (‖A⋆u‖ ≤ ‖A‖·‖u‖), `lcDiff_norm_le`
(‖A‖ ≤ metricDerivNorm).  ITERATED (`j ≥ 2`, generic order): the telescoping
`∇^{g₀,j}T = ∑_{k≤j} (∇^{gBase,·}A products)⋆∇^{gBase,k}T`, each `A`-insertion costing one jet
`metricCovDeriv g₀ gBase (m+1) ≤ Λ` — this is the from-scratch induction.  connDiff atoms:
`connDiffSection`/`connDiffContrInsertionField` (`Sobolev/TensorHilbert/ConnDiffJetL2Summed`),
`ChristoffelDifferenceKoszul.lean` (`connDiff_koszul`), `CovDerivConnDiffQuadraticBound.lean`
(order-1 covGrad connDiff bound) — but these are tuned to the metric-DIFFERENCE tensor (item-2
DeTurck remainder), NOT a generic `T`, so the generic-`T` iteration is an assembly, not a reuse.

## Constant shape (state BEFORE proving, per protocol)
Pointwise (gBase-fiber currency): `|∇^{g₀,j}T|_{gBase} ≤ D_j·∑_{k≤j}|∇^{gBase,k}T|_{gBase}` with
`D_j = D_j(Λ,n)` a length-`j` product of Γ-difference jets (`≤ P(Λ)` each) times slot/index
combinatorics — polynomial in `Λ`, `n=finrank`.  Then fiber `Λ^{(s+j)/2}` + volume `Λ^{n/4}` +
Cauchy–Schwarz over the `(j+1)`-term inner sum + sum over `j≤n`:
```
C(Λ,n) = Λ^{n/4} · ∑_{j≤n} Λ^{(s+j)/2}·D_j(Λ,n)·√(j+1)   (each direction; gBase↔g₀ symmetric)
```
`s` = base valence (=2 for consumers).  No R-type / class-datum quantities — only `Λ`, `n`,
`s`, and fixed `gBase` data (folded into `D_j` via the jets ≤ Λ).

## HOME
`HCGCompactness/UnifCovSumCross.lean` (this leaf).  May import `AllTimesBounds`
(comparability + fiber wrappers), `Comparison.lean` (fiber atoms), `CrossMetricEnergy`
route pattern, and the connDiff/measure layers (all upstream of HCG).

## Session-1 deliverable (this session)
The **green fiber-level layer** (mission-sanctioned session-1 boundary) in 0S currency,
sorry-free: general-order class-hypothesis fiber comparison `covSumCross_fiber0S_le/ge`
(+ `√` form) keyed on `MetricUniformEquivalentOn`, and the covariant-SUM fiber shell
`covSumCross_fiberSum_le` (term-by-term over a derivative-indexed family).  The L² S0 pair
is NOT stated sorry-free in Lean this session (blocked on the volume + currency-bridge +
connection-change bricks above); its full statement + 3-brick decomposition live in this note.

## Status
- 2026-07-24 (session 1): recon COMPLETE; comparability predicate + fiber atoms located and
  REUSED; three missing bricks isolated (Loewner→det volume, RS↔0S currency bridge [other
  lane], iterated connection change [main frontier]).  Green fiber engine (0S currency) is
  this session's Lean deliverable.  S0 L² pair remains multi-session (recon §4 medium, 2–3
  sessions confirmed).
