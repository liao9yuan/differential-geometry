# ComponentConvTower.lean — covariant-tower component convergence (P3 Gap B)

Target: `componentConv_covDeriv_of_chartCInf` — the `a ≥ 1` covariant tower of the
metric-component convergence (general-`a` analogue of `componentConv_covDeriv_zero`).

## Status (2026-06-13)

**THE FULL COVARIANT-TOWER CONVERGENCE INDUCTION IS DONE + verified** (every lemma
axiom-clean, builds green): `bumpTowerCarrier_all` — from the order-`0` base, the
bump carriers of EVERY section tuple at EVERY covariant order `a` converge
`C^∞`-on-compacts on `U`, along one subsequence.  Chain (all committed):
`bumpTowerStep_chartConv` (directional) → `bumpTowerStep_split` (towerStep =
`s_{p+1}` + Σ corrections) + `.sub` → `bumpTowerCons_conv` (frame-leading step
core) → `bumpTower_slotExpand_conv` (leading-slot frame expansion) →
`bumpTowerCarrier_step` (IH(p) ⇒ IH(p+1)) → `bumpTowerCarrier_all` (`Nat.rec`).
Supporting: `chartRep_contDiffOn`, `bumpTowerScalar_contDiff`,
`bumpTowerStepScalar_contDiff`.

**REMAINING = the three INPUTS to `bumpTowerCarrier_all`** (each well-specified):
1. **base `hbase`** (order-0, all section pairs): from B0 `exists_engine_frameCInfConv`
   (frame-pair convergence) + `bumpTower_slotExpand_conv` applied to BOTH slots.
2. **frame data** `(frame, vbasis, hframeσ, hspan)`: global sections `= frameVec`
   on `Kc` (`exists_section_eqOn_compact`), `hframeσ` from
   `frameVec = tangentConstInChart`, and `hspan` = coordinate-frame coefficient
   smoothness (`exists_frameVec_basis` + frame-coeff smoothness on the chart domain).
3. **extraction**: order-0 of the `C^∞`-on-compacts conv at `extChartAt x₀ x` ⇒
   pointwise `Tendsto` of `s_a^V(x)`; then a fixed (`k`-independent) multilinear
   expansion of the basis vectors `b (I0 q)` in the frame at `x` lands the
   `component0S b (metricCovDeriv g gRef a x) I0` shape (the
   `componentConv_covDeriv_of_chartCInf` statement, general-`a` analogue of
   `componentConv_covDeriv_zero`).  Then finite-cover `hnorm` → `metricPreconvInf`.

### Landed (this file + MapConvergenceDeriv.lean)
- `chartRep_towerScalar_contDiffOn` / `chartRep_contDiffOn` — chart rep of a
  chart-source-smooth function is `ContDiffOn` the extended-chart target.
- `bumpTowerScalar_contDiff` — bump-extended `s_p^V` chart rep is globally
  `ContDiff` on `E`.  Global-smoothness prerequisite for B2/mulLeft/sum.
- `bumpFderiv_eq_chartTowerStep` + `bumpTowerStep_chartConv` — **directional step**:
  bump-`s_p^V` C∞-conv on `U` ⇒ bump-`towerStep` C∞-conv on `U` (`fderivApply` +
  `congr` + `fderiv_chartRep_eq_towerStep` germ).
- `bumpTower_slotExpand_conv` — **multilinear frame expansion**: if slot `j` of `V`
  is `∑ᵢ cᵢ • frameᵢ` on the chart source, the carrier of `V` converges from the
  carriers of `update V j frameᵢ` (`map_update_sum`/`smul` + `mulLeft`/`sum` + `congr`).
- `bumpTowerStep_split` — **`towerStep` split**: bump-`s_{p+1}^{cons σ V'}` (value
  form) `= bump-towerStep − ∑_a bump-correctionₐ`, each correction a level-`p`
  carrier for `update V' a (covSection … σ (V' a))` (the `∇_σ V'ₐ` slot as a
  `covSection`, via `leviCivitaConnectionOfMetric_contMDiffCovariantDerivative`).
- `MapCInfConvOnCompacts.sub` (MapConvergenceDeriv.lean) — subtraction closure, to
  extract `s_{p+1} = towerStep − ∑ corrections`.

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

**Smallest next lemma DONE** = `bumpTower_slotExpand_conv` (frame-expansion conv).

**All step primitives now committed.**  The `Nat.rec` step (IH at level `p`, all
section tuples ⇒ same at `p+1`) is pure assembly of committed pieces:
- leading-slot expansion: `bumpTower_slotExpand_conv` (j = 0, `frameᵢ`, coeffs `cᵢ`);
- per `frameᵢ`: `bumpTowerStep_chartConv` (towerStep conv from IH at `tail W`)
  + `bumpTowerStep_split` (= `s_{p+1}` + Σ corrections) + `.sub` + `.sum` over the
  correction carriers (IH at `update (tail W) a (covSection … frameᵢ (tail W)ₐ)`);
- bridge `update W 0 frameᵢ` ↔ value-form `Fin.cons frameᵢ (tail W)` (`funext`/`Fin.cases`).
Context threaded as hypotheses: `frame : Fin n → ContMDiffSection` with
`hframeσ i : frame i =ᶠ[𝓝ˢ Kc] tangentConstInChart x₀ (finBasis i)` and a
`frame-spans-on-source` producer (from `exists_frameVec_basis`); plus
`χ/U/Kc/hUKc/hUtarget`.  Then base (B0 + slotExpand over the n² pairs) + `φ`-diagonal
+ extraction give `componentConv_covDeriv_of_chartCInf`.
