# ComponentConvTower.lean — covariant-tower component convergence (P3 Gap B)

Target: `componentConv_covDeriv_of_chartCInf` — the `a ≥ 1` covariant tower of the
metric-component convergence (general-`a` analogue of `componentConv_covDeriv_zero`).

## Status (2026-06-13)

**Directional crux DONE + verified** (all axiom-clean, targeted build green).
The hard analytic half of the induction step is complete; the remaining work is
the correction split, the all-tuples induction wrapper, the base, and pointwise
extraction — substantial but well-specified assembly.

### Landed (this file)
- `chartRep_towerScalar_contDiffOn` — chart rep of `s_p^V(w) = (∇^p_gRef A0) w (V·w)`
  is `ContDiffOn` the extended-chart target (via `covDerivOfField_eval_contMDiff`
  + `contDiffAt_chartRep`).
- `bumpTowerScalar_contDiff` — bump-extended `s_p^V` chart rep is globally
  `ContDiff` on `E` (`bumpMul_contDiff`).  The global-smoothness prerequisite for
  B2/mulLeft/sum.
- `bumpFderiv_eq_chartTowerStep` — on open `U` with `χ ≡ 1` and `symm '' U ⊆ Kc`,
  `fderiv (bump-carrier) z v = χ z · chartRep(towerStep) z` (χ=1 ⇒ bump-fderiv =
  unbump-fderiv via `EventuallyEq.fderiv_eq`; then `fderiv_chartRep_eq_towerStep`
  germ, `eq_of_nhds`).
- `bumpTowerStep_chartConv` — **directional step**: bump-`s_p^V` C∞-conv on `U` ⇒
  bump-`towerStep` C∞-conv on `U`.  `fderivApply` (B2) + `congr` via the bridge.

### Key existing machinery reused (MetricPreconv.lean — the A2 layer)
- `towerStep gRef A0 p V σ` (def): `s_{p+1}^{cons σ V} + Σ_a s_p^{update V a (∇_{V a}σ)}`.
- `fderiv_chartRep_eq_towerStep` — `(fun z => fderiv (chartRep s_p^V) z v) =ᶠ[𝓝]
  chartRep(towerStep ... σ)`, `σ = tangentConstInChart x₀ v` near `Kc`. **The germ
  identity; THE reason no new directional API was needed.**
- `extDerivFun_tower_step`, `covDerivOfField_eval_contMDiff`, `bumpMul_contDiff`,
  `covDerivOfField_eval_mdiffAt`.
- B2 `MapCInfConvOnCompacts.fderivApply`, producer 3 `.add/.mulLeft/.sum`,
  locality `.congr` (MapConvergenceDeriv.lean).

## Remaining assembly (precise)

**Induction carrier (the right invariant):** for ALL section tuples
`V : Fin (p+2) → ContMDiffSection`, the bump-extended chart rep
`fun z => χ z · writtenInExtChartAt x₀ (fun w => covDerivOfField gRef A0 p w (V·w)) z`
converges `C∞`-on-compacts on the open chart patch `U`, along ONE `φ`.  Carrier is
parameterised by `A0` so `A0Seq k = metricTensorField (gSeq (φ k))`,
`A0inf = metricTensorField gInf`.

**Step `p → p+1`** for a tuple `W = Fin.cons w₀ V'` (`V' : Fin (p+2) → …`):
1. **Leading-slot frame expansion.**  `Φ_{p+1}^W = Σ_i c_i · Φ_{p+1}^{cons frame_i V'}`
   where `frame_i = tangentConstInChart x₀ (finBasis i)` (chart-constant), `c_i =`
   `frame.coeff i w₀` (smooth, `k`-independent); covDerivOfField is multilinear in
   the leading (derivative) slot ⇒ `mulLeft + sum`.  (Needed because
   `bumpTowerStep_chartConv` requires the leading slot `σ = tangentConstInChart`.)
2. For each chart-constant `frame_i`: `towerStep^{V', frame_i}` converges by
   `bumpTowerStep_chartConv` (needs IH at `V'`).  And
   `towerStep = Φ_{p+1}^{cons frame_i V'} + Σ_a correction_a`, so
   `Φ_{p+1}^{cons frame_i V'} = towerStep − Σ_a correction_a`.
3. **Corrections need NO frame expansion** (key simplification of the all-tuples
   carrier): `correction_a(q) = covDerivOfField gRef A0 p q (update (V'·q) a
   ((∇ (V' a)) q (frame_i q)))` `= s_p^{V'_a}` where `V'_a` is `V'` with slot `a`
   replaced by the section `w_a := fun q => (leviCivita gRef (V' a)) q (frame_i q)`
   (a `ContMDiffSection`).  So `correction_a` converges by **IH at tuple `V'_a`**.
4. Combine: `Φ_{p+1}^{cons frame_i V'} = towerStep − Σ correction_a` via
   `MapCInfConvOnCompacts.add` (with negation / `.sub`).  Smoothness of every
   carrier from `bumpTowerScalar_contDiff`.

**Base `p = 0`:** B0 `exists_engine_frameCInfConv` gives frame-PAIR convergence.
For an arbitrary tuple `V : Fin 2 → sections`, frame-expand BOTH slots:
`s_0^V = A0(V_0)(V_1) = Σ_{ij} c_i^0 c_j^1 · A0(frame_i)(frame_j) = Σ c_i^0 c_j^1 ·
(frame-pair carrier)` ⇒ `mulLeft + sum` over the n² frame pairs (B0).

**Single `φ` / diagonal:** B0 gives a per-`(i,j)` subsequence; diagonalise over the
n² frame pairs once (finite `exists_refine_allComponents`-style fold keeping the
`MapCInfConvOnCompacts`, or `exists_diag_subseq`).  Because every higher carrier is
a fixed `gRef`-operator (`fderiv` + fixed-smooth-coeff `mulLeft` + `sum`) of the
order-0 frame components, that ONE `φ` serves all `p` and all tuples.

**Extraction:** order-0 of the C∞-on-compacts conv on a small compact ⊆ `U`
containing `extChartAt x₀ x` gives pointwise `Tendsto` of `s_a^V(x)`; choose
sections `σ_q` with `σ_q x = b (I0 q)` to land the `component0S b (metricCovDeriv
g gRef a x) I0` shape that `metricDerivNorm_le_compSq_uniform` / `hnorm` consume.

**Smallest next lemma:** the multilinear frame-expansion convergence
`s_p^{update V a (Σ_i c_i • frame_i)} = Σ_i (chartRep c_i) · s_p^{update V a frame_i}`
lifted to `MapCInfConvOnCompacts` via `mulLeft + sum` — used for both the
leading-slot expansion (step 1) and the base.  Then the `Nat.rec` induction wrapper.
