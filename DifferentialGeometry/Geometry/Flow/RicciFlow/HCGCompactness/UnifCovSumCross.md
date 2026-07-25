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

### V — SESSION 3 (2026-07-24): steps 1–3 LANDED sorry-free + verified; step 4 BLOCKED
`lake build +…UnifCovSumCross` EXIT=0 (3903 jobs); `#print axioms` = `[propext, Classical.choice,
Quot.sound]` on each new public theorem (then stripped).
- **(1) `det_le_of_posSemidef_le`** (general Loewner→det) — DONE, private in §MatrixDet, via the CFC
  matrix sqrt per the worked route below.  Simplification vs the plan: `PosSemidef.det_sqrt` was NOT
  needed — `IsUnit M.det` came directly from `M.det*M.det=B.det` being a unit; `A = M·C·M` via
  `simp only [mul_assoc]` reassociation.  Helper split out: **`det_le_one_of_dotProduct`** (plain
  `ι→ℝ` form of the committed `det_le_one_of_rayleigh`) isolates ALL `EuclideanSpace`/`star`/`RCLike.re`
  coercion so the general lemma stays in `ι→ℝ` currency.  LESSONS: the `EuclideanSpace` inner↔dotProduct
  bridge is `EuclideanSpace.inner_eq_star_dotProduct` (namespaced!) + `real_inner_self_eq_norm_sq`, and
  must be composed via **`exact` (defeq), NOT `rw`** — `rw` on `inner ℝ v v` fails to match (`inner ?m
  ?x ?y` pattern misses the instance).  `dotProduct_smul`/`smul_dotProduct` are ROOT namespace (NOT
  `Matrix.`); `smul_mulVec`/`dotProduct_mulVec`/`mulVec_mulVec`/`mulVec_transpose` ARE `Matrix.`.
- **(2) `chartGram_quad_le_of_equiv`** — DONE (public).  `chartGramMatrix_dotProduct_mulVec` already
  gives the quad-form = fibre inner product of `V=∑ vᵢ•cbf i`; `← …_dotProduct_mulVec` + `star_trivial`
  turns `v ⬝ᵥ Gram *ᵥ v` into `g.inner x V V`, then `(hEq.2 x (mem_univ x) V).2`.
- **(3) `chartDensity_cross_le`** — DONE (public), on the trivialization base set.  `A=chartGram g₀` PSD,
  `B=Λ•chartGram gBase` PosDef (`PosDef.smul`), `det_le_of_posSemidef_le` + `det_smul`/`Fintype.card_fin`
  ⟹ `det g₀ ≤ Λⁿ det gBase`; `√` via `Real.sqrt_mul (pow_nonneg …)` + `Real.sqrt_le_sqrt`.  Constant
  `√(Λ^n)` (`n=finrank`).  Use `change` not `show` to unfold `chartDensity` (linter).
- **(4) `volumeMeasure_cross_le`** — **DONE (public), sorry-free + verified** (planner-authorized the
  scope-limited CompactVolumeEquiv repair, session 3b).  `dV_{g₀} ≤ √(Λ^n)·dV_{gBase}` and reverse,
  both directions, via `chart_lintegral_le` + the POU lower-integral decomposition (`vsum`, re-derived
  from PUBLIC `riemannianMeasure_lintegral_eq`+`tsum_eq_sum`+`chartAtlasPOU_weight_zero_of_notMem`),
  `hbase` tsupport⊆baseSet (`chartAtlasPOU_isSubordinate`+`trivializationAt_baseSet_eq_chartAt_source`),
  reverse via `metricUniformEquivalentOn_symm`, and `Measure.le_iff`+indicator to read off the measure
  inequality.  The measure-conversion tail uses `Set.indicator s (1 : M → ℝ≥0∞)` (exact `s.indicator 1`
  shape) + explicit `rw [lintegral_indicator_one hs, lintegral_indicator_one hs] at h` then
  `rwa [Measure.smul_apply, smul_eq_mul]` — NOT `simpa`, which no longer fires against pinned Mathlib.
  **Unblocked by** a latent-break repair of `CompactVolumeEquiv.lean` (`volume_uniform_equiv` tail was
  bit-rotted the same way; its olean was silently missing) — the identical two-line fix at
  `CompactVolumeEquiv.lean:366/:371`, statement-preserving, recorded in `CompactVolumeEquiv.md`.  Lift
  section needs the compact-closed-manifold measure instances (`[T2Space] [SigmaCompactSpace]
  [CompactSpace]` + local `borel E/M`), added in a dedicated `section VolumeMeasure`.  The verbatim proof
  is also preserved at the bottom of this note.

### V — ORIGINAL fully-worked route (from session 2; realized by steps 1–3 above)
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

## Session 4 (2026-07-24) — T recon: the IDENTITY layer is already built (false wall dissolved)

Planner dispatch (brick T executor e87b): CHECK the two-`abstractDerivEval_aux` subtraction route
first; decide r1 vs r2; state induction shape + `D_{j+1}=f(D_j,Λ)` + jet budget; if the generic
slot identity needs > ~100 lines new plumbing, STOP and propose.

### VERDICT — r1 CONFIRMED and the generic slot identity is PRE-BUILT (not > 100 lines; it is 0)
The recon-§T "generic multi-slot connection difference `∇^{g₀}A − ∇^{gBase}A = ∑_slot Γdiff ⋆ A`
for `(0,s)` A is not yet a committed lemma" claim is a **FALSE WALL**.  It exists, sorry-free, in
the connection layer, proved by *exactly* the subtraction route the planner flagged (the two
Leibniz forms' `∂`-terms cancel, leaving the `CovariantDerivative.difference` slot-sum):

- **`nabla0SFun_sub_cov`** (`Tensor/RSTensor/NablaOnTensors/HigherOrder.lean:659`), generic `(0,s)`,
  directional:  `(nabla0SFun s cov X α − nabla0SFun s cov' X α) x (V·) =
  −∑ₐ α x (update (V·) a ((difference cov cov' x)(Vₐ x))(X x))`.  Proof =
  `nabla0SFun_eval_smooth_slots` (both connections) + `IsCovariantDerivativeOn.difference_apply` +
  `(α x).map_update_sub`.  This IS route r1 realized at the `nabla0SFun` (chart) level; the abstract
  `abstractDerivEval_aux` subtraction would give the same thing one layer up — no need, this is done.
  `nabla0SFun_sub_cov_two` (`:742`) is the `(0,2)` specialization.
- **`covStep` / `iterCov` / `iterCov_succ` / `diffStep` / `telescAccum` / `iterCov_telescoping`**
  (`HCGCompactness/MetricCovDerivLinear.lean:212–344`): the GENERIC-`(0,s)` iterated tower and the
  **full telescoping IDENTITY** `iterCov g₁ r T N = iterCov g₂ r T N + telescAccum g₁ g₂ r T N`,
  with `diffStep g₁ g₂ s S = covStep g₁ s S − covStep g₂ s S` (the generic-T single-step connection
  difference) and `telescAccum (N+1) = covStep g₁ (telescAccum N) + diffStep g₁ g₂ (iterCov g₂ N)`.
  ALL sorry-free (a 6-line induction).  These have NO consumers yet — they are the built-but-unused
  identity layer awaiting the norm brick (= T).

So the derivative-level *identity* frontier the recon called "the main frontier / from-scratch
induction" is DONE.  What brick T actually needs is the **NORM layer** on top of it.

### CURRENCY — `normSq0S` / `iterCov` (chart/model), NOT `iteratedCovGrad`
The mission's j=1 template `cross_point_le` (`Garding/CrossMetricEnergy.lean:88`) works ENTIRELY in
`normSq0S` (it never touches `iteratedCovGrad`); the fibre atoms `covsumCross_fib*` are `normSq0S`;
the jet hypothesis `MetricCovDerivOrderBoundOn` is `normSq0S`/`metricCovDeriv`.  So the telescoping
lives in `normSq0S`/`iterCov`, self-contained, needing NO RS↔0S bridge internally (the sibling
`MetricCovDerivBridge` `normBridge` bridges to the `iteratedCovGrad` endpoint at ASSEMBLY, later).
`iterCov gRef r A0 a : Tensor0SField (r+a)` is the generic `∇^a` tower (`covDerivOfField = iterCov`
for `(0,2)`); `MetricCovDerivOrderBoundOn` bounds jets of the *metric* g₀ (via `metricCovDeriv h
gRef`), from which iterated `∇^{gBase,a}A` bounds come by Koszul (`connDiff_koszul`).

### REMAINING NORM-LAYER sub-bricks (both located; the frontier is much narrower than §T thought)
- **(T-A) `diffStep_norm_le` — the generic single-step connection-difference norm.**  The direct
  generalization of `connOut_norm_le` from `s=1` to `s`:
  `√normSq0S gBase x (s+1) (diffStep g₁ g₂ s S x) ≤ s · √normSqRS gBase x 1 2
  (connectionDifferenceTensorAt (LC g₁)(LC g₂) x) · √normSq0S gBase x s (S x)`.
  Route: lift `nabla0SFun_sub_cov` to the full `(0,s+1)` tensor via `totalNabla0SFun_apply_section`
  (`diffStep x = −∑ₐ Insₐ`); `√normSq0S` triangle (it is a genuine fibre norm — `normSq0S_eq_inner`
  + `Bundle.instInnerProductSpaceReal`); per-slot `√normSq0S(Insₐ) ≤ |A|·|S|` by the component
  Cauchy–Schwarz (expand `normSq0S = ∑_φ (·)²` via `normSq0S_identity_eq_sum_sq`, insert
  `A_map(eⱼ)(eᵢ)=∑ₖ A^k_{ij} eₖ`, C-S in the contracted index k is SHARP → constant exactly `s`,
  no dimension factor).  **No existing general slot-contraction HS-norm lemma** (grep-confirmed;
  `sqrt_normSqRS_apply` is Hom-apply only, and the per-slot mixed tensor `Mₐ` has `|Mₐ|_HS =
  |A|·n^{(s−1)/2}` — HS overestimates, so the sharp route is the component C-S, not `Mₐ`+apply).
  Estimated ~100–150 lines of structural Finset work.  **HOME: deserves a connection-layer public
  home next to `connOut_norm_le` (`FiberMetric/ConnectionDifferenceNorm.lean`)** — per the mission's
  "if the generic slot identity deserves a connection-layer home, stop and propose".  Since that
  file is outside this session's editable set, build it PRIVATE in `UnifCovSumCross.lean` (hoist
  candidate, mirroring the `MatrixDet` section) or propose the hoist.
- **(T-B) the full norm telescoping** `|iterCov g₁ r T N|_{gBase} ≤ D_N·∑_{k≤N}|iterCov g₂ r T k|_{gBase}`.
  NOT pointwise-closable from the identity + (T-A) alone: `telescAccum` carries OUTER `covStep g₁`
  (g₁-derivatives), and `|∇₁ W|` is not bounded by `|W|` pointwise.  Needs the **base-Leibniz rule
  for the insertion** `covStep g₂ (diffStep …) = (∇₂A)⋆S + A⋆(∇₂S)` to re-expand `telescAccum` into
  the all-`∇₂` schematic `∑ (∇₂^{a₁}A)⋆…⋆(∇₂^{aₘ}A)⋆∇₂^{k}T` (`a₁+…+aₘ+k ≤ N`, `k ≤ N`), then
  `∇₂^{a}A` bounds from Koszul + `MetricCovDerivOrderBoundOn`.  This is the genuine multi-session
  frontier (the base-Leibniz for the connection-difference contraction is a new lemma family).

### INDUCTION SHAPE + CONSTANT RECURSION (state-before-prove)
j=1 (verified boundary this brick): `iterCov_telescoping` at N=1 gives `iterCov g₁ r T 1 =
iterCov g₂ r T 1 + diffStep g₁ g₂ r T` (since `telescAccum 1 = diffStep g₁ g₂ r T`); triangle +
(T-A):
`|iterCov g₁ r T 1|_{gBase} ≤ |iterCov g₂ r T 1|_{gBase} + D₁·|T|_{gBase}`, `D₁ = s·|A|_{gBase} ≤
s·(3/2)·√(Λ³)·metricCovDerivNorm 1 g₀ gBase` (via `lcDiff_norm_le`), `≤ s·(3/2)Λ^{3/2}·Λ` by the
order-1 jet.  Induction `D_{N+1} = f(D_N,Λ,n)`: each telescoping level adds one `A`-insertion (one
jet `∇₂^{m}A ≤ P(Λ)` via Koszul, `m ≤ N−1`) and one outer `∇₂`; schematically `D_{N} =
∑_{compositions} ∏ (jet factors)` = polynomial in `Λ` and `n=finrank` of degree ~`N` in the jets.
Jet-order budget: order-`N` telescoping needs `∇₂^{a}A` for `a ≤ N−1`, i.e. metric jets
`MetricCovDerivOrderBoundOn … a … Λ` up to `a ≤ N` (Koszul: `A ~ ∇₂ g₀`, so `∇₂^{a}A ~ ∇₂^{a+1}g₀`).
For the S0 orders `s ≤ a+2 = 4n+12`, the class hypothesis must reach order `≈ a+2`.

### SESSION-4 OUTCOME
- **LANDED sorry-free + verified** in `UnifCovSumCross.lean` `section DiffStepNorm` (`lake build
  +…UnifCovSumCross` EXIT=0, 3906 jobs, 27s; `#print axioms` = `[propext, Classical.choice,
  Quot.sound]` on both, stripped): `covStep_zero'` (`covStep gRef s 0 = 0`, `R`-linearity) and
  **`iterCov_one_eq`** (`iterCov g₁ r T 1 = iterCov g₂ r T 1 + diffStep g₁ g₂ r T`) — the order-1
  telescoping reduction and the FIRST consumers of the previously-consumer-less `iterCov_telescoping`.
  Added `import …MetricCovDerivLinear`.  This is the verified j=1 IDENTITY boundary.
- **NEW BLOCKER for the j=1 NORM atom `diffStep_norm_le` — the tensor-bundle instance diamond at
  GENERIC rank.**  Bounding `normSq0S(diffStep … x)` needs `diffStep_eval` (evaluate the generic-rank
  tensor field on inputs to reach `nabla0SFun_sub_cov`), which forces `totalNabla0SFun_apply_section`
  at VARIABLE rank `s+1`.  The model/bundle instances `NormedSpace ℝ (Tensor0SModel (s+1) ℝ E)` and
  `FiberBundle (Tensor0SModel (s+1) ℝ E) (fun x => Tensor0SSpace (s+1) I x)` **do not synthesize for a
  universally-quantified `s`** — not slowness (fails at 1.6M synthInstance heartbeats), and not the
  documented `attribute [-instance]` fix (that removal set `…mixed_instNormedAddCommGroup` is an unknown
  constant in this import scope, and is tuned for the `RiemannianBundle`-on-`TensorRSSpace` norm, not a
  generic-rank `totalNabla0SFun` eval).  Grep-confirmed: NO existing lemma evaluates
  `totalNabla0SFun_apply_section` at generic rank — `iterCov_metric_zero`/`Lemma45Engine` only do it at
  the CONCRETE rank 2.  This is why the whole `covStep`/`iterCov`/`diffStep`/`telescAccum` layer was
  built via `rfl`/additivity (`covStep_add`/`covStep_zero`) and left consumer-less: evaluation was never
  crossed.  **This generic-rank tensor-bundle EVAL instance problem is the true gate of brick T's norm
  layer**, ahead of the component Cauchy–Schwarz (which is straightforward once eval works) and the
  base-Leibniz induction (T-B).
- **Route options for the eval gate (for planner):** (i) find/build the correct `attribute [-instance]`
  removal set for the 0S model at generic rank (the sibling `MetricCovDerivBridge` lane fights the same
  diamond — coordinate the removal set), plus a `letI`/`haveI` supplying `tensor0SModel_normedSpace
  (s+1)` (`Defs.lean:384`, a genuine global instance) and `tensor0SSpace_fiberBundle (s+1)`
  (`Tensor0SInnerSectionContinuity.lean:484`); (ii) prove a generic-rank `totalNabla0S_apply` /
  `diffStep_apply` eval lemma ONCE in the connection layer (where the instances are in scope), exporting
  a clean `diffStep g₁ g₂ s S x (cons v slots) = −∑ₐ …` that downstream files reuse without touching the
  instances; (iii) evaluate via `nabla0SFun`-only currency avoiding `totalNabla0SFun_apply_section`
  entirely (needs a direct `covStep_apply`-to-`nabla0SFun` bridge that sidesteps the section-eval
  instance).  Option (ii) is the cleanest and belongs in `MetricCovDerivLinear.lean` (or a new
  `MetricCovDerivEval.lean`) — recommend proposing it.  Once eval lands, `diffStep_norm_le` = the
  component route above (sharp constant `s`, or dimension-tolerant `s·n^{(s+1)/2}`), then the T-B
  base-Leibniz induction remains the multi-session frontier.

### SESSION-4 PLAN (superseded by OUTCOME above)
Recon → build (T-A) `diffStep_norm_le` (verified j=1 boundary, private hoist-candidate) → j=1
telescoping norm corollary → report (T-B) base-Leibniz as the remaining frontier.

## Session 5 (2026-07-24) — the eval gate is CROSSED (Session-4 blocker DISSOLVED)

The Session-4 "generic-rank tensor-bundle EVAL instance diamond" was NOT an
`attribute [-instance]` problem: it was simply that `UnifCovSumCross.lean` lacks
`set_option backward.isDefEq.respectTransparency false`.  Route (ii) (prove the eval ONCE in
`MetricCovDerivLinear.lean`, which carries that option) worked on the FIRST attempt.  **LANDED
sorry-free + verified in `MetricCovDerivLinear.lean`** (`lake build +…MetricCovDerivLinear`
EXIT=0, 3633 jobs; axioms `[propext, Classical.choice, Quot.sound]` on both, stripped):

- **`diffStep_apply`** — section form:
  `diffStep g₁ g₂ s S x (Fin.cons (X x) (V·x)) = −∑ₐ (S x)(update (V·x) a ((Γ₁−Γ₂)(V a x))(X x))`.
  Generic-`(0,s)` lift of `nabla0SFun_sub_cov`; ~15-line r1 proof (`covStep_apply` +
  `totalNabla0SFun_apply_section` + `nabla0SFun_sub_cov`, fibre sub-apply by `change`).
- **`diffStep_eval`** — pointwise form on ARBITRARY `v, slots` (the form the norm route needs,
  since `component0S basis (diffStep x) φ` is an eval on basis vectors).  Via
  `Geometry.Riemannian.exists_contMDiff_vectorField_eq` (`[T2Space M]`) + `ContMDiffSection.mk`.
  New import `…Geometry.Metric.SmoothVectorFieldExtGlobal`.

Instance recipe (in `MetricCovDerivLinear.md` §2026-07-24): the haveIs `IsManifold I {1,2,(1+1),∞+1} M`
+ `TangentBundle.contMDiffVectorBundle (n := 1)` for the `[ContMDiffVectorBundle 1 …]` that
`nabla0SFun_sub_cov` demands.  `IsManifold I (1+1) M` is NOT the `IsManifold I 2 M` haveI (both
needed).

### Remaining T-A norm atom `diffStep_norm_le` (now unblocked; two sub-frontiers)
With `diffStep_eval` in hand, `diffStep_norm_le` still needs, in `UnifCovSumCross.lean`:
1. **`gBase`-orthonormal frame at `x`** — a `Module.Basis Idx ℝ (TangentSpace I x)` with
   `hON : gBase.inner x (basis i)(basis j) = δᵢⱼ` (and its `MetricInverseInBasis_gen` witness),
   to feed `normSq0S_identity_eq_sum_sq` / `abs_apply_le_sqrt_normSq0S`
   (`Tensor0SRiemannian/Comparison.lean`).  Build from the finite-dim inner-product structure of
   `(TangentSpace I x, gBase.inner x)`.
2. **Raw connection-difference component C-S** — bound `|(Γ₁−Γ₂)(u)(w)|_{gBase}` by
   `√normSqRS gBase x 1 2 (connectionDifferenceTensorAt (LC g₁)(LC g₂) x) · |u|·|w|` (sharp
   constant `s`; the `connectionDifferenceOutput` component route, ~100 lines Finset).  This is
   the vector-output analogue of `connOut_norm_le` (which is covector-output only).
Then assemble: `√normSq0S(diffStep x) ≤ s·√normSqRS(connectionDifferenceTensorAt)·√normSq0S(S x)`,
compose with `lcDiff_norm_le` (jet side) + `MetricCovDerivOrderBoundOn`.  T-B base-Leibniz
(`covStep g₂ (diffStep …)` re-expansion into all-`∇₂` schematic) remains the multi-session frontier.

## Session 6 (2026-07-24) — T-A assembly `diffStep_norm_le` LANDED (fibre form)

Planner dispatch: assemble the j=1 fibre-norm atom (`diffStep_eval` + `connDiffVec_norm_le` +
`abs_apply_le_sqrt_normSq0S` over an internal g-ON frame), explicit constant.

**LANDED sorry-free + verified** in `UnifCovSumCross.lean` `section DiffStepNorm` (`lake build
+…UnifCovSumCross` EXIT=0, 3909 jobs; `#print axioms diffStep_norm_le` = `[propext,
Classical.choice, Quot.sound]`, stripped; added `import …FiberMetric.ConnectionDifferenceNorm`):

- **`diffStep_norm_le`** (public):
  `√normSq0S(g₂, s+1, diffStep g₁ g₂ s S x) ≤ (s)·√((finrank ℝ E)^{s+1})·√normSqRS(g₂, 1, 2, connectionDifferenceTensorAt (LC g₁)(LC g₂) x)·√normSq0S(g₂, s, S x)`.
  **Constant `s·n^{(s+1)/2}`** (`n = finrank ℝ E`), NOT sharp `s`:
  `normSq0S_le_card_of_component_bound` bounds each of the `n^{s+1}` frame components uniformly by
  `B = s·√normSqRS·√normSq0S(S x)` ⟹ `normSq0S ≤ n^{s+1}·B²` ⟹ the `√(n^{s+1})` card factor; sharp
  `s` would need per-component Parseval.

Proof (~150 lines, passed on the FIRST authoritative build): internal `g₂`-ON frame; per-component
`hcomp` via `component0S_apply` → `Fin.cons` rewrite (`Fin.cases`) → `diffStep_eval` → `abs_neg` +
`Finset.abs_sum_le_sum_abs`; per-slot `hterm` via `abs_apply_le_sqrt_normSq0S` on `S x`, slot
product collapsed to `‖insertion‖` (`Finset.prod_eq_single` + `update_self`/`update_of_ne` + ON
`hbnorm = 1`), `connDiffVec_norm_le` bounding `‖insertion‖ ≤ √normSqRS`; sum over `s`;
`normSq0S_le_card_of_component_bound`; `√` + card (`Fintype.card_fun`/`card_fin`, `finrank
(TangentSpace I x) = finrank E` by rfl, `Real.sqrt_mul`/`sqrt_sq`).

USEFUL FACTS: `finrank ℝ (TangentSpace I x) = finrank ℝ E` is `rfl`; `SmoothRiemannianMetric =
SmoothMetric = SmoothMetric_gen`; `Fintype.card_fun : card (α→β) = card β ^ card α`; update lemmas
are `Function.update_self` / `Function.update_of_ne`.

### REMAINING for the L² S0 endpoint
1. **Jet composition** of `diffStep_norm_le` into `MetricCovDerivOrderBoundOn` currency — two
   bridges, BOTH not-yet-available (grep-checked):
   - **antisymmetry** `normSqRS(connectionDifferenceTensorAt (LC g₁)(LC g₂)) =
     normSqRS(connectionDifferenceTensorAt (LC g₂)(LC g₁))` (`diffStep_eval` gives order `(LC g₁)(LC
     g₂)`; `lcDiff_norm_le` is `(LC h)(LC g) = (LC g₂)(LC g₁)`).  `difference cov cov' = −difference
     cov' cov` ⟹ `normSqRS` equal; needs a `difference`-antisymmetry + `normSqRS_neg` lemma (neither
     found; `difference_symm_at` in `KoszulDifference.lean` is the SLOT symmetry, not this).
   - **`metricDerivNorm` ↔ `metricCovDerivNorm`**: `lcDiff_norm_le` outputs `metricDerivNorm 1 g₂ g₁
     g₁ x`; `MetricCovDerivOrderBoundOn K 1 g₂ g₁ C` bounds `metricCovDerivNorm 1 g₂ g₁ x ≤ C`.
     Distinct signatures, no found equality.  Needs a `metricDerivNorm ≤ metricCovDerivNorm` lemma.
   Endpoint: `√normSq0S(diffStep) ≤ s·n^{(s+1)/2}·(3/2)·√(Λ³)·Λ'·√normSq0S(S x)` under
   `MetricUniformEquivalentOn K g₁ g₂ Λ` + `MetricCovDerivOrderBoundOn K 1 g₂ g₁ Λ'`.
2. **T-B base-Leibniz** (`j ≥ 2`) — the genuine multi-session frontier.

## Step-4 proof, preserved for drop-in (BLOCKED on CompactVolumeEquiv — see V-session-3)

Add `import DifferentialGeometry.Analysis.Integration.Measure.CompactVolumeEquiv` and this section
(after `chartDensity_cross_le`, before `end RicciFlow`) once CompactVolumeEquiv.lean compiles again
(fix its `lintegral_indicator_one` `simpa` at :366/:371 with the `Set.indicator s 1` form + explicit
`rw`).  Verified up to the CompactVolumeEquiv build wall; the tail was reformulated to the
`Set.indicator s (1 : M → ℝ≥0∞)` shape precisely to dodge the same `lintegral_indicator_one` drift.

```lean
section VolumeMeasure
open MeasureTheory
open scoped ENNReal
variable [T2Space M] [SigmaCompactSpace M] [CompactSpace M]
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem volumeMeasure_cross_le
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ}
    (hEq : MetricUniformEquivalentOn (I := I) Set.univ gBase g₀ Λ) :
    riemannianVolumeMeasure (I := I) (M := M) g₀ ≤
        ENNReal.ofReal (Real.sqrt (Λ ^ Module.finrank ℝ E)) •
          riemannianVolumeMeasure (I := I) (M := M) gBase ∧
      riemannianVolumeMeasure (I := I) (M := M) gBase ≤
        ENNReal.ofReal (Real.sqrt (Λ ^ Module.finrank ℝ E)) •
          riemannianVolumeMeasure (I := I) (M := M) g₀ := by
  classical
  have vsum : ∀ (g : SmoothRiemannianMetric I M) (F : M → ℝ≥0∞), Measurable F →
      ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        ∑ α ∈ chartAtlasPOU_finset (I := I) (M := M), ∫⁻ x,
          ENNReal.ofReal ((chartAtlasPOU I M α : M → ℝ) x) * F x
            ∂(chartLocalMeasure (I := I) g α) := by
    intro g F hF
    rw [riemannianVolumeMeasure_def,
      riemannianMeasure_lintegral_eq (I := I) g (chartAtlasPOU I M) hF]
    refine tsum_eq_sum (fun α hα => ?_)
    have hz : ∀ x : M, (chartAtlasPOU I M α : M → ℝ) x = 0 :=
      fun x => chartAtlasPOU_weight_zero_of_notMem (I := I) (M := M) hα x
    simp only [hz, ENNReal.ofReal_zero, zero_mul, lintegral_zero]
  have hbase : ∀ (α : M), ∀ x ∈ tsupport (fun y : M => (chartAtlasPOU I M α : M → ℝ) y),
      x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro α x hx
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact (chartAtlasPOU_isSubordinate I M) α hx
  have lintComp : ∀ (q h : SmoothRiemannianMetric I M),
      (∀ (α : M), ∀ x ∈ tsupport (fun y : M => (chartAtlasPOU I M α : M → ℝ) y),
        chartDensity (I := I) h α x ≤
          Real.sqrt (Λ ^ Module.finrank ℝ E) * chartDensity (I := I) q α x) →
      ∀ (F : M → ℝ≥0∞), Measurable F →
        ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) h) ≤
          ENNReal.ofReal (Real.sqrt (Λ ^ Module.finrank ℝ E)) *
            ∫⁻ x, F x ∂(riemannianVolumeMeasure (I := I) (M := M) q) := by
    intro q h hdens F hF
    rw [vsum h F hF, vsum q F hF, Finset.mul_sum]
    refine Finset.sum_le_sum (fun α _ => ?_)
    exact chart_lintegral_le (I := I) (M := M) q h α
      (Real.sqrt (Λ ^ Module.finrank ℝ E)) (Real.sqrt_nonneg _) (hdens α) hF
  have hdens_fwd : ∀ (α : M), ∀ x ∈ tsupport (fun y : M => (chartAtlasPOU I M α : M → ℝ) y),
      chartDensity (I := I) g₀ α x ≤
        Real.sqrt (Λ ^ Module.finrank ℝ E) * chartDensity (I := I) gBase α x :=
    fun α _ hx => chartDensity_cross_le (I := I) gBase g₀ hEq α (hbase α _ hx)
  have hdens_rev : ∀ (α : M), ∀ x ∈ tsupport (fun y : M => (chartAtlasPOU I M α : M → ℝ) y),
      chartDensity (I := I) gBase α x ≤
        Real.sqrt (Λ ^ Module.finrank ℝ E) * chartDensity (I := I) g₀ α x :=
    fun α _ hx =>
      chartDensity_cross_le (I := I) g₀ gBase
        (metricUniformEquivalentOn_symm (I := I) hEq) α (hbase α _ hx)
  refine ⟨?_, ?_⟩
  · rw [Measure.le_iff]
    intro s hs
    have h := lintComp gBase g₀ hdens_fwd (Set.indicator s (1 : M → ℝ≥0∞))
      (measurable_const.indicator hs)
    rw [lintegral_indicator_one hs, lintegral_indicator_one hs] at h
    rwa [Measure.smul_apply, smul_eq_mul]
  · rw [Measure.le_iff]
    intro s hs
    have h := lintComp g₀ gBase hdens_rev (Set.indicator s (1 : M → ℝ≥0∞))
      (measurable_const.indicator hs)
    rw [lintegral_indicator_one hs, lintegral_indicator_one hs] at h
    rwa [Measure.smul_apply, smul_eq_mul]
end VolumeMeasure
```

## Status
- 2026-07-24 (session 6, T-A assembly): **`diffStep_norm_le` LANDED (fibre form)** sorry-free +
  verified in `UnifCovSumCross.lean` (`lake build +…UnifCovSumCross` EXIT=0, 3909 jobs; axioms
  standard triple; added `import …FiberMetric.ConnectionDifferenceNorm`).  Constant `s·n^{(s+1)/2}`
  (`n = finrank ℝ E`), via `diffStep_eval` + `connDiffVec_norm_le` + `abs_apply_le_sqrt_normSq0S`
  over an internal g₂-ON frame, summed over `s` slots (`normSq0S_le_card_of_component_bound`).
  Passed on the FIRST authoritative build.  REMAINING (see §"Session 6"): (i) jet composition into
  `MetricCovDerivOrderBoundOn` currency — blocked on a `connectionDifferenceTensorAt` argument-order
  antisymmetry lemma + a `metricDerivNorm`↔`metricCovDerivNorm` bridge; (ii) T-B base-Leibniz.
- 2026-07-24 (session 5, T eval gate): **eval gate CROSSED** — `diffStep_apply` (section) +
  `diffStep_eval` (pointwise, arbitrary vectors) LANDED sorry-free + verified in
  `MetricCovDerivLinear.lean` (`lake build +…MetricCovDerivLinear` EXIT=0, 3633 jobs; axioms
  standard triple).  Session-4 "instance diamond" was just the missing
  `backward.isDefEq.respectTransparency false` in `UnifCovSumCross.lean`; route (ii) worked
  first try in `MetricCovDerivLinear.lean` (which sets it).  Norm atom `diffStep_norm_le` now
  unblocked but has two sub-frontiers (gBase-orthonormal frame + raw connection-difference
  component C-S) → see §"Session 5".  T-B base-Leibniz still multi-session.
- 2026-07-24 (session 4, T recon + identity activation): **route r1 CONFIRMED; identity layer is a
  FALSE WALL (already built)**.  `nabla0SFun_sub_cov` (generic multi-slot connection difference) +
  `diffStep`/`iterCov`/`iterCov_telescoping` (full telescoping identity) all exist sorry-free upstream.
  Currency = `normSq0S`/`iterCov` (chart/model, NOT `iteratedCovGrad`).  **LANDED sorry-free + verified**
  (`lake build +…UnifCovSumCross` EXIT=0, 3906 jobs; axioms `[propext, Classical.choice, Quot.sound]`):
  `covStep_zero'` + `iterCov_one_eq` (order-1 telescoping reduction `iterCov g₁ 1 = iterCov g₂ 1 +
  diffStep`, first consumers of `iterCov_telescoping`; `import …MetricCovDerivLinear` added).  **The j=1
  NORM atom `diffStep_norm_le` is BLOCKED on the generic-rank tensor-bundle EVAL instance diamond** —
  `totalNabla0SFun_apply_section` will not synthesize `NormedSpace ℝ (Tensor0SModel (s+1) ℝ E)` /
  `FiberBundle …` at variable rank `s+1` (no existing lemma evaluates it at generic rank; concrete-rank
  only).  Full analysis + route options in §"Session 4 — OUTCOME".  T-A eval gate + T-B base-Leibniz
  remain (multi-session).
- 2026-07-24 (session 3b, V step 4): **`volumeMeasure_cross_le` LANDED sorry-free + verified**
  (public, `HCGCompactness/UnifCovSumCross.lean` `section VolumeMeasure`).  Planner authorized the
  scope-limited `CompactVolumeEquiv.lean:366/:371` latent-break repair (indicator `Set.indicator s 1`
  + explicit `rw`, statement-preserving; recorded in `CompactVolumeEquiv.md`).  `lake build
  +…CompactVolumeEquiv` EXIT=0 (2873 jobs); then step-4 drop-in `lake build +…UnifCovSumCross` EXIT=0
  (3904 jobs); `#print axioms volumeMeasure_cross_le` = `[propext, Classical.choice, Quot.sound]`.
  **ALL FOUR V steps now done** (fibre + steps 1–3 + step 4 measure lift).  T (connection-change
  telescoping) not started — separate next dispatch.
- 2026-07-24 (session 3, V steps 1–3): **LANDED sorry-free + verified** — `det_le_of_posSemidef_le`
  (general Loewner→det, private), `det_le_one_of_dotProduct` (plain-form bridge, private),
  `chartGram_quad_le_of_equiv` (public), `chartDensity_cross_le` (public).  `lake build
  +…UnifCovSumCross` EXIT=0 (3903 jobs); axioms `[propext, Classical.choice, Quot.sound]` on all new
  public/private theorems.  **Step 4 `volumeMeasure_cross_le` proof is complete but BLOCKED and NOT in
  the .lean**: its dep `CompactVolumeEquiv.lean` does not compile against the current Mathlib
  (`volume_uniform_equiv` :366/:371 — `lintegral_indicator_one` `simpa` drift), so `chart_lintegral_le`
  is unimportable.  Fix is one two-line change in CompactVolumeEquiv (non-editable this session); proof
  preserved above for drop-in.  T (connection-change) not started this session.
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
