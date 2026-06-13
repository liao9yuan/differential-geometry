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

**INPUT 2 (frame data) DONE** = `exists_frameData` (axiom-clean): for compact `Kc`
in a chart, global sections `frame i = tangentConstInChart x₀ (finBasis i)` near
`Kc` (via `exists_section_eqOn_compact`) + `hspan` (coordinate-frame coefficient
smoothness) — built from the **Mathlib local-frame API**: `c_i = e.localFrame_coeff`,
smooth via `contMDiffOn_baseSet_localFrame_coeff`, expansion via
`eq_sum_localFrame_coeff_smul`, bridged `e.localFrame i = tangentConstInChart` via
`basisAt`/`symmL` (both `= e.symm w (b i)`).  **NO missing local-frame theorem.**

**INPUT 1 (base) — algebraic half DONE** = `hbase_of_framePairs` (axiom-clean):
double `bumpTower_slotExpand_conv` reduces the order-0 carrier of any `Fin 2`
section pair to the frame-pair carriers, given the diagonalised frame-pair
convergence `hpairs`.

**χ-SHARING RESOLVED (2026-06-13, `exists_chart_engineInput_family`, axiom-clean):**
the bump `χ` of `exists_chart_engineInput` is provably `V`-independent (built from
`x₀`/`K₀` only), so ONE `χ` serves the whole `n²` frame-pair family with per-member
`ContDiff` + uniform iterated-derivative bounds.  **The first stop condition (B0
outputs cannot share `χ/U/Kc`) is NOT hit.**

**REMAINING (no missing API; all well-specified):**
1. **diagonal → one `φ`**: feed `exists_chart_engineInput_family`'s per-member
   bounds through `exists_diag_subseq` (`hsub = MapCInfConvOnCompacts.comp_subseq`,
   `hextend` = subsequence-shift, `hstep` = `exists_cInf_subseq` on the φ-composed
   member sequence) — OR bundle into `F = (Fin n × Fin n) → ℝ` and one
   `exists_cInf_subseq` (needs a Σ-of-components Pi-`iteratedFDeriv` bound +
   projection `comp_clm`).  Gives one `φ`, all pairs converge to some `Φinf_{ij}`.
2. **limit-pinning**: `Φinf_{ij} = χ · chartRep(gInf.inner (frameᵢ)(frameⱼ))` by
   pointwise-limit uniqueness (order-0 of the `C^∞` conv vs the pointwise metric
   limit `hconv` from `metricPreconv_gInf`).  Yields `hpairs` with
   `A0Seq k = metricTensorField (gSeq (φ k))`, `A0inf = metricTensorField gInf`.
   `U` = open subset of `{χ=1} ∩ tgt` with `symm U ⊆ Kc`; `Kc = symm '' (tsupport χ)`.
3. **feed**: `hpairs` → `hbase_of_framePairs` → `bumpTowerCarrier_all` (with
   `exists_frameData`'s frame as the engine `Vfam`).
4. **extraction**: order-0 of the resulting `C^∞` conv at `extChartAt x₀ x` ⇒
   pointwise `Tendsto`; fixed multilinear expansion of `b (I0 q)` in the frame at
   `x` ⇒ `component0S b (metricCovDeriv g gRef a x) I0` shape ⇒
   `componentConv_covDeriv_of_chartCInf`.  Then finite-cover `hnorm` → `metricPreconvInf`.

Planner acceptance note: `bumpTower_slotExpand_conv` intentionally keeps the
uniform chart-patch hypothesis `hUtarget` even though this declaration does not use
it directly; a declaration-local linter option now records that choice without
changing the public theorem shape.  Verification still passed.

Planner acceptance cleanup: replaced the style-only `show` step in
`exists_frameData` with `change`; focused verification still passed.

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

## FINAL ASSEMBLY — in progress (new file `ComponentConvAssembly.lean`)

The 4 REMAINING steps are being assembled in a NEW top file
`ComponentConvAssembly.lean` (imports `ComponentConvTower` + `MetricPreconvBridge`,
which transitively pulls `MetricPreconvDiag`/`MetricPreconv`/`WindowPreconv`; no
import cycle — `ComponentConvTower` and `MetricPreconvBridge` are siblings).
`metricPreconvInf` is stated fresh here (`MetricCInfConvOnCompacts` lives in
`PointedConvergence.lean`).

**Verified signatures dovetail (step-0 scout, confirms "no missing API"):**
`exists_frameData` supplies `frame/vbasis/hframeσ/hspan`; `hbase_of_framePairs`
consumes `hpairs` (frame-pair order-0 carrier conv for the tuple
`update (fun _ => frame i) 1 (frame j)`) and produces exactly the `hbase` argument
(`∀ V : Fin 2 → …`) of `bumpTowerCarrier_all`.  `hbase_of_framePairs` and
`bumpTowerCarrier_all` share one `χ/U/Kc/frame/s = Finset.univ : Finset (Fin n)`.
The shared `χ` for the `n²` pairs comes from `exists_chart_engineInput_family`
(NOT the per-pair `exists_engine_frameCInfConv_eq_gm`, whose `χ_{ij}/ψ_{ij}` differ
per pair); the per-pair limit pinning then mirrors
`exists_engine_frameCInfConv_eq_gm`'s `tendsto_nhds_unique` against `hconv`.

**DONE + verified (focused checks green; committed):**
- `exists_cInf_subseq_finiteFamily` — finite-family `C∞`-on-compacts diagonal
  (`Finset.induction` over `exists_cInf_subseq` + `comp_subseq`; `revert hΦ hbdd`).
- **Step 1-rest** `exists_framePairs_diag` — `Vfam (i,j) = update (fun _ => frame i)
  1 (frame j)`; `exists_chart_engineInput_family` (shared `χ`) →
  `exists_cInf_subseq_finiteFamily` over `univ : Finset (Fin n × Fin n)` → one `ψ`,
  each pair `MapCInfConvOnCompacts`-converges (to some `Φinf`).  Carrier order
  `(gSeq ∘ φ)(ψ k) = gSeq (φ (ψ k))` matched by defeq.
- **Step 2** `framePairs_pinned` — pins each `Φinf` to the `gInf` carrier
  (`tendsto_of_cInf` + `hconv ∘ ψ` + continuous fibre eval + `tendsto_nhds_unique`,
  then `funext`/rw of the limit) ⇒ `hpairs`.  KEY: `covDerivOfField_zero` is `rfl`
  so `rw` chokes — fold it with `show (metricTensorField g) w … = …` then
  `metricTensorField_apply` + `simp [Function.update_of_ne, Function.update_self]`.
- **Step 3** `exists_tower_conv` — `exists_frameData` + `framePairs_pinned` +
  `hbase_of_framePairs` + `bumpTowerCarrier_all` → all-orders `C∞` tower-carrier
  convergence on `U = target ∩ symm⁻¹(interior K₀)` (open via
  `(continuousOn_extChartAt_symm).isOpen_inter_preimage`; `χ = 1` on `U` from the
  pointwise `hχ1` + `right_inv`; `extChartAt '' interior K₀ ⊆ U`).  `s = Finset.univ`.
  `hpairs` restricted `univ → U` by `fun K hK hKU p => hpairs K hK (subset_univ K) p`.

**DONE — Step 4a (committed `6c8e5e12`, focused check green):**
- `componentConv_covDeriv_of_chartCInf` POINTWISE (general order `a`, frame-general
  `Basis b`, `I0 : Fin (a+2) → Fin n`).  chart `x₀ = x`; `K₀` via
  `exists_compact_subset (chartAt H x).open_source (mem_chart_source H x)` (needs
  `LocallyCompactSpace H/M` haveI); `exists_tower_conv`; `extChartAt x x ∈ U` from
  `hImg`; `V_q := (ContMDiffSection.exists_eq_at_gen (n := (⊤ : ℕ∞)) x (b (I0 q))).choose`
  (note `n : ℕ∞` NOT `WithTop ℕ∞`!); `tendsto_of_cInf (htower a V) hxU`; carrier value
  `= component0S b (metricCovDeriv g gRef a x) I0` via `hχU hxU` + `Pi.one_apply` +
  `writtenInExtChartAt_real_apply` + `left_inv` + `simp [hVval]` + `rfl`
  (`component0S_apply`/`metricCovDeriv_eq_covDerivOfField` are rfl).  `htend.congr`.

**DONE — Step 4b-ii algebraic core (committed `78a119b0`, focused checks green):**
- `tangentConst_basis_expand` — `tangentConstInChart x (basisE i) p = Σ_j (finBasis.repr
  (basisE i) j) • tangentConstInChart x (finBasis j) p` (`Basis.sum_repr` + `map_sum`/
  `map_smul` on the linear `symmL`).  The CONSTANT-`M` (z-independent) expansion.
- `bz_eq_tangentConst` — `(trivAt x).localFrame(basisE).toBasisAt hz i =
  tangentConstInChart x (basisE i) z` (`IsLocalFrameOn.toBasisAt_coe` +
  `localFrame_apply_of_mem_baseSet` + `simp [basisAt, tangentConstInChart_apply]`).
  So the norm-bridge basis `bz` IS the chart-constant frame.

**REMAINING — Step 4b (wiring, the endpoint `metricPreconvInf`):**  Two parts:
- *(4b-ii rest)* per-slot bridge `bz(I0 q) = V^{I0}_q(z')` (`bz_eq_tangentConst` +
  `tangentConst_basis_expand` + `hframeσ` frame bridge near `Kc`; `V^{I0}_q :=
  Σ_j (finBasis.repr (basisE (I0 q)) j) • frame_j`, a constant-combo `ContMDiffSection`)
  ⇒ `component0S bz (metricCovDeriv g gRef a z') I0 = [exists_tower_conv carrier for
  V^{I0}] (extChartAt z')` (`component0S_apply`) ⇒ uniform-on-patch convergence from the
  tower's `MapCInfConvOnCompacts` order-0 slice (`tendstoUniformlyOn_of_cPConv`) ⇒
  `metricDerivNorm < ε` uniform on the patch (`metricDerivNorm_le_compSq_uniform`).
  Domain bookkeeping: patch ⊆ `baseSet ∩ {frame-bridge holds} ∩ interior K₀`
  (so `extChartAt z' ∈ U`); call `metricDerivNorm_le_compSq_uniform` and
  `exists_tower_conv` at the SAME center `x_p` (so `bz`/tower share `trivAt x_p`).
- *(4b-i global diagonal)* `exists_chart_cover` (countable charts/compacts) +
  `exists_diag_subseq` over the cover, `hstep` = per-chart `exists_tower_conv`
  C∞-data extraction (refines any subsequence), `hsub` = `MapCInfConvOnCompacts.comp_subseq`,
  `hextend` = tail shift → ONE `φ` carrying the tower data on every chart.
- *(4b-ii hnorm)* finite good-frame cover of each compact `K` + `metricDerivNorm_le_compSq_uniform`.
  **KEY (de-risks the apparent point-dependence):** its component basis
  `bz = (trivAt x).localFrame(basisE).toBasisAt hz` satisfies
  `bz_i(z) = (trivAt x).symmL z (basisE i) = Σ_j M_{ij}·frame_j(z)`, where
  `frame_j = tangentConstInChart x (finBasis j)` is the `exists_tower_conv` frame and
  `M` is the **CONSTANT** (`z`-independent) `basisE`-in-`finBasis` change-of-basis in `E`.
  So `component0S bz (Δtower) I0` is a constant-coefficient multilinear combination of
  the coordinate-frame components `component0S frame (Δtower) (…)`, which converge
  **uniformly on compacts** from the `exists_tower_conv` tower (`MapCInfConvOnCompacts`,
  order-0 slice = `tendstoUniformlyOn_of_cPConv`).  Hence `bz`-components → 0 uniformly
  (constant transition, NO point-dependent obstruction) ⇒ `metricDerivNorm < ε`
  uniform on `K` ⇒ `hnorm` ⇒ `metricCInfConvOnCompacts_of_normConv`.
  This is real work (the constant-transition multilinear expansion + the uniform
  extraction from the tower per good-frame patch + the finite cover), but API-complete.

~~NOTE (real subtlety for step 4)~~ — **PLANNER RULING 2026-06-13: this note is
WRONG; do NOT carry uniformity through the multilinear expansion.**  Verified
against the actual signatures (workflow trace, high confidence):
`metricDerivNorm_le_compSq_uniform` (MetricPreconvBridge.lean:76-107) uses the
component basis `bz = (…).isLocalFrameOn_localFrame_baseSet I 1 basisE).toBasisAt hz`
(line 102-103), which is **POINT-DEPENDENT** (re-derived at each `z ∈ u'`, under
`∀ z ∈ u', ∀ hz`).  So `z ↦ component0S bz (…) I0` lands in a `z`-varying fibre
basis — a `TendstoUniformlyOn` of it over the patch is **ill-typed**, not merely
unnecessary.  Build no such conversion lemma.
**CORRECT thread:** state `componentConv_covDeriv_of_chartCInf` POINTWISE,
mirroring `componentConv_covDeriv_zero` exactly (fixed `x`, frame-general `Basis b`,
fixed `I0`, conclusion `Filter.Tendsto … (𝓝 …)`).  Extraction = `tendsto_of_cInf`
(MapConvergence.lean:124-135) at `extChartAt x₀ x` on `bumpTowerCarrier_all`'s
order-0 carrier, then the finite multilinear `b (I0 q)`-expansion (preserves
pointwise `Tendsto`).  The uniform-on-`K` of `hnorm` is assembled SEPARATELY by a
finite good-frame cover of `K` via `metricDerivNorm_le_compSq_uniform` — the same
finite-cover pattern as `ric_bound`, already the plan of record (line 196,
MetricPreconvBridge.md:154-160).  No uniform-vs-pointwise conversion lemma is
missing.
