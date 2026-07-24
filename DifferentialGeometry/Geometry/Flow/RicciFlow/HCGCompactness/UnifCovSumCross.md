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

## Session 2 (2026-07-24) — VOLUME brick (V) core + routes

Planner dispatch: (V) the volume brick (Loewner→det), then (T) start the connection-change
telescoping (j=1 verified if the full induction is large, skeleton in `.md` either way).

### V — MATERIAL FINDING: Loewner→det is a genuine matrix brick, not "generic matrix analysis"
Mathlib has **no** matrix square root as a plain `Matrix` op, **no** Weyl/min-max eigenvalue
monotonicity, **no** Loewner `≤`→`det` lemma, and **no** Hadamard determinant inequality.
`Measure/CompactVolumeEquiv.lean:9` explicitly records the existing `volume_uniform_equiv` was
built to AVOID this estimate.  So the explicit-`Λ` volume comparison genuinely requires building
Loewner→det.  Located building material: `JacobianBounds.lean` `MatrixBounds`
(`eigenvalues_ge_of_rayleigh`, `sqrt_pow_le_sqrt_det`) is single-matrix (eigenvalue→det), NOT the
two-matrix Loewner→det; Mathlib `Analysis/Matrix/PosDef.lean` has `det_eq_prod_eigenvalues`,
`PosSemidef.eigenvalues_nonneg`.  **BUT** `Analysis/Matrix/Order.lean` provides a CFC matrix sqrt
(`CFC.sqrt`, `CFC.sqrt_mul_sqrt_self`, `PosSemidef.det_sqrt`, `nonneg_iff_posSemidef`) and
`Analysis/CStarAlgebra/…` the factorization `CStarAlgebra.nonneg_iff_eq_star_mul_self` — so the
brick is FEASIBLE (no missing math), just a ~50-line matrix proof.

### V — LANDED (sorry-free, verified; axioms `[propext, Classical.choice, Quot.sound]`)
The reusable Loewner→det core, in `UnifCovSumCross.lean` §MatrixDet (private; hoist candidate =
`JacobianBounds.lean` `MatrixBounds`):
- `eigenvalues_le_of_rayleigh` — Rayleigh **upper** bound ⟹ every eigenvalue `≤ a` (upper companion
  of the existing `eigenvalues_ge_of_rayleigh`).
- `det_le_one_of_rayleigh` — `A.PosSemidef` + Rayleigh `≤ 1` (i.e. `A ≤ I`) ⟹ `det A ≤ 1`
  (eigenvalues `∈ [0,1]`, `det = ∏ ≤ 1` via `Finset.prod_le_one`).  This is the `B = I` core.

### V — REMAINING (fully-worked route; next session is mechanical)
1. **`det_le_of_posSemidef_le`** (general Loewner→det): `A.PosSemidef`, `B.PosDef`,
   `∀ v:ι→ℝ, v ⬝ᵥ A*ᵥv ≤ v ⬝ᵥ B*ᵥv` ⟹ `A.det ≤ B.det`.  Proof (worked): `M := CFC.sqrt B`
   (PosDef, symmetric `Mᴴ=M` via `IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg _)`, `M*M=B` via
   `CFC.sqrt_mul_sqrt_self`, `det M = √(det B)` via `PosSemidef.det_sqrt`).  Set
   `C := M⁻¹*A*M⁻¹`; `C.PosSemidef` (via `PosSemidef.conjTranspose_mul_mul_same` + `Mᴴ=M`).
   Rayleigh: for `‖v‖=1`, put `u := M⁻¹*ᵥv`; then `v ⬝ᵥ C*ᵥv = u ⬝ᵥ A*ᵥu ≤ u ⬝ᵥ B*ᵥu = (M*ᵥu)⬝ᵥ(M*ᵥu)
   = v⬝ᵥv = 1` (uses `M` symmetric + `M*ᵥu = v`), so `det_le_one_of_rayleigh` gives `det C ≤ 1`.
   Finally `A = M*C*M` ⟹ `det A = (det M)²·det C = det B·det C ≤ det B` (`det B>0`).  Coercion
   care: `EuclideanSpace ℝ ι ↔ ι→ℝ`, `star=id`/`RCLike.re=id` over ℝ, `dotProduct_mulVec` with
   `M`/`M⁻¹` symmetric (`transpose_nonsing_inv`), `⇑v ⬝ᵥ ⇑v = ‖v‖²` via `EuclideanSpace` inner.
2. **`chartGram_quad_le_of_equiv`** (gap-free): from `MetricUniformEquivalentOn univ gBase g₀ Λ`,
   `∀ v:Fin n→ℝ, v ⬝ᵥ (chartGram g₀ x₀ x)*ᵥv ≤ Λ·(v ⬝ᵥ (chartGram gBase x₀ x)*ᵥv)`.  Route:
   `chartGramMatrix_apply` (`= g.inner x (cbf i)(cbf j)`, `Geometry/Metric/ChartGram.lean:224`) +
   bilinear expansion `v ⬝ᵥ Gram *ᵥ v = g.inner x V V`, `V=∑ vᵢ·cbf i` (tooling:
   `chartBasisVecFiber_eq_sum_chartModelBasis`, `g_inner_bilinear_expand`) + comparability.
3. **`chartDensity_cross_le`**: from (1)+(2) with `A=chartGram g₀`, `B=Λ•chartGram gBase`
   (`det(Λ•G)=Λⁿ det G`), `√`: `chartDensity g₀ x₀ x ≤ Λ^{n/2}·chartDensity gBase x₀ x`.
4. **`volumeMeasure_cross_le`**: lift (3) to `riemannianVolumeMeasure g₀ ≤ (Λ^{n/2})•riemannianVolumeMeasure
   gBase` (both directions) via `chart_lintegral_le` (`CompactVolumeEquiv.lean:195`) + the POU-sum
   pattern of `volume_uniform_equiv:342` (with explicit `C=Λ^{n/2}` instead of the existential).
Constant: volume factor `Λ^{n/2}` (`n=finrank`), matching recon §3.

### T — connection-change telescoping (skeleton, per planner "state the skeleton either way")
Target (pointwise, gBase-fibre currency): `|∇^{g₀,j}T|_{gBase} ≤ D_j·∑_{k≤j}|∇^{gBase,k}T|_{gBase}`,
`D_j=D_j(Λ,n)`.  **j=1 template** = the scalar-Hessian assembly in
`Garding/CrossMetricEnergy.lean` `cross_point_le`: `∇^{cov}−∇^{cov'}` on a covector `α` is the
connection-difference tensor `A=connectionDifferenceTensorAt (LeviCivita g₀)(LeviCivita gBase) x`
contracted, i.e. `hess_sub_conn` (`HessianTraceRealization.lean:333`,
`Hess_{cov}u−Hess_{cov'}u = −connectionDifferenceOutput(diff)(du)`) + `connOut_norm_le`
(`ConnectionDifferenceNorm.lean:29`, `‖A⋆α‖_g ≤ ‖A‖_g·‖α‖_g`) + the g-norm triangle.  Class
uniformity: bound `‖A‖_{gBase}=√normSqRS(connectionDifferenceTensorAt)` by the order-1 jet via
`lcDiff_norm_le` (`MetricLapDiff.lean:164`, `‖ΔLC‖ ≤ Ce·metricDerivNorm 1 …`) then
`metricDerivNorm ↔ MetricCovDerivOrderBoundOn`.  **GAP for the actual `(0,2)` base**:
`connectionDifferenceOutput` is single-covector (`(0,1)→(0,2)`); the `(0,s)`-tensor difference is
the multi-slot Leibniz sum `∑_{slot} A⋆(slot)` — the generic multi-slot connection difference is
the real j=1-for-`(0,2)` content (not yet a committed lemma; `MetricDiffCovGradKoszul`/
`RicciDeTurckSectionDifference` are metric-difference-specific).  **Induction j→j+1**: differentiate
`∇^{g₀,j}T = ∇^{gBase,j}T + (Γ-diff insertions)` once more with `∇^{gBase}`, convert the extra
`∇^{g₀}`→`∇^{gBase}` via the same connection-difference, and re-index — each step adds one
`A`-insertion (cost one jet) and one fibre-slot (cost `√Λ`).  Then integrate with the volume
comparison (V) and sum over `j≤n` (Cauchy–Schwarz over the `(j+1)`-term inner sum) → `C(Λ,n)`.

## Status
- 2026-07-24 (session 2, V): LANDED the Loewner→det reusable CORE sorry-free + verified
  (`eigenvalues_le_of_rayleigh`, `det_le_one_of_rayleigh`; `lake` EXIT=0; axioms standard triple).
  MATERIAL FINDING: the full Loewner→det is a genuine ~50-line matrix brick (Mathlib lacks matrix
  sqrt-as-`Matrix`-op / Weyl / Hadamard / det-order), NOT "generic matrix analysis available" — but
  FEASIBLE (CFC sqrt in `Analysis/Matrix/Order.lean`).  General lemma + chart-Gram + density + measure
  lift fully-worked above (mechanical next session).  T skeleton recorded; j=1 for the `(0,2)` base
  needs the generic multi-slot connection difference (beyond single-covector `connectionDifferenceOutput`).
  No general-lemma `.lean` written (coercion-heavy; banked the core rather than risk a long
  unverified cycle).
- 2026-07-24 (session 1): recon COMPLETE; comparability predicate + fiber atoms located and
  REUSED; three missing bricks isolated (Loewner→det volume, RS↔0S currency bridge [other
  lane], iterated connection change [main frontier]).  Green fiber engine (0S currency) is
  this session's Lean deliverable.  S0 L² pair remains multi-session (recon §4 medium, 2–3
  sessions confirmed).
