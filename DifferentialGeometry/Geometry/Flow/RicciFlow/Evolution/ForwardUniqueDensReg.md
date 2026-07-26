# ForwardUniqueDensReg — the `hdens` joint-regularity tower (brick TOWER)

Companion note for `ForwardUniqueDensReg.lean`.  Status **2026-07-26**: outcome **(B) strong**
— deliverables 1 and 2 landed green and sorry-free; deliverables 3–5 landed *conditional on
one precisely-named missing producer*, which the recon **located** (contrary to the Dispatch
№6 debt entry, which recorded it as nonexistent).

Verification: focused check GREEN, warning-free; targeted module build GREEN.  No `sorry`, no
new instances, axioms or notation.

---

## 1. Recon result — the "chart-Gram → Γ → Rm joint tower does NOT exist" debt is WRONG

Dispatch №6 recorded the `hdens` debt as: *"the chart-Gram → Γ → Rm joint tower does NOT
exist"*.  That is **false**.  A complete, **generic** joint tower already exists in

`Analysis/Parabolic/RicciLinearization/RicciDifferenceMeanValue.lean`

quantified over an arbitrary family `gfam : ℝ → SmoothRiemannianMetric I M`:

| decl | line | gives |
|---|---|---|
| `GenJointGram` | 401 | the hypothesis bundle (joint chart-Gram `C∞` on `ℝ × E` + Gram det positivity) |
| `genGram_of_family` | 417 | `MetricFamilySmoothOn` ⟹ `GenJointGram` (the `ℝ × M → ℝ × E` transport, reusable verbatim) |
| `gen_joint_invGram` | 476 | joint `C∞` of `chartInvGramOnE` |
| `gen_joint_gramBracket` | 600 | joint `C∞` of the Koszul bracket |
| `gen_joint_christoffel` | 619 | **joint `C∞` of `chartChristoffel`** |
| `gen_joint_partial_christoffel` | 673 | one more spatial derivative |
| `gen_joint_riemann` | 683 | **joint `C∞` of the chart Riemann coefficients** |
| `christ_of_family` | 640 | the same, transported back to `M × ℝ` (template for the transport direction) |

Plus the **intrinsic** bridge, which is the piece that actually matters:

* `LeviCivita_chartBasisVec_alpha_basis_apply` —
  `(LC g) ∂_k (∂_l) (b) = ∑_m chartChristoffel g α l k m (extChartAt I α b) • ∂_m b`,
  valid on `chartLeviCivitaGoodSet α`
  (used at `Analysis/Elliptic/ConnectionLaplacian/ChartCoordinateExpansion/RawConnLapMinusInvGramPrincipalSmoothCoeff.lean:377`).

This is the **fourth** confirmed false wall in this project (cf. the memory entries on
BBS/Bochner over-counting, the A0′ L1 wall, and the P1.3 iterated-tangent-bundle wall).
Rule reconfirmed: grep for a *generic* producer before recording a layer as missing.

Other inventory used:

* `ExtendedSolutionRegularity.lean:53` `metricCLMSection_jointContMDiffOn_of_chartGram_Ioo`
  and `:687` `metricFrameComp_jointContMDiffOn_of_chartGram` — joint `C∞` of the metric's
  local-frame components on `Ioo a b ×ˢ u`.  Consumed directly.
* `Geometry/Operator/Gradient.lean:252` `chartInvGramMatrix_entry_contMDiffOn` — the *spatial*
  Cramer proof.  Transcribed to the product source (see §2).
* `Tensor/RSTensor/MetricTrace/Connection.lean:~700` `normSq0S_smooth` — the *spatial* fibre-norm
  smoothness, general valence.  Its coordinate expansion is the model for the joint brick.
* `Analysis/Spectral/Intrinsic/DeTurck/MovingEdgeEnergy.lean:~330` — a joint *continuity*
  version of the same expansion (`chartInvGram_inverse` + `normSq0S_eq_coord`).  Reference only:
  that file is un-compilable (Unicode bug recorded in Dispatch №6) and has no olean.
* `ShortTime/DeTurckChartRegularityFromJoint.lean` — a full joint Christoffel/Riemann/Ricci
  tower, but every rung is `private` and it is specialised to the DeTurck family.  Reference
  only; the generic public copy is the `RicciDifferenceMeanValue` one above.
* `Analysis/Integration/Measure/Properties.lean` `riemannianVolumeMeasure_isFiniteMeasureOnCompacts`
  — the integrability producer.

## 2. What was proved

**The structural brick.**  `normSq0S_jointContMDiffOn`: for a metric family `g` with jointly
`C∞` chart-Gram entries and a `(0,s)`-tensor family `A` with jointly `C∞` chart-frame
components, `(t, x) ↦ |A t x|²_{g t}` is jointly `C∞` on `J ×ˢ univ` (`J` open).  This is the
joint-in-time upgrade of `normSq0S_smooth`, proved by the same `normSq0S_eq_coord` expansion
against `chartBasisFamily` but with `chartInvGramMatrix` (not the flat-model chart inverse)
supplying the inverse metric, so that `chartInvGram_inverse` applies verbatim.

Supporting it, the **joint Cramer chain** on the product source `ℝ × M`:
`chartGramDet_jointContMDiffOn` → `chartGramAdj_jointContMDiffOn` →
`chartInvGram_jointContMDiffOn`.  This is a line-by-line transcription of the spatial
`chartInvGramMatrix_entry_contMDiffOn`, with `chartGramMatrix_entry_contMDiffOn` replaced by
the `hgram` hypothesis.  Deliberately **not** routed through `gen_joint_invGram`: that one
lives on `ℝ × E`, needs `interior (extChartAt).target` membership and a transport back, and
would drag the whole `Analysis/Parabolic/RicciLinearization` subtree into `Evolution/`.  The
direct route is shorter and import-clean.  (If deliverable 3 is built later and *does* need the
`Analysis/Parabolic` import for Christoffels, `chartInvGram_jointContMDiffOn` can be retired in
favour of `gen_joint_invGram` — but not before.)

**Deliverable 1 — `metricDiffSq_jointContMDiffOn`, unconditional.**  The chart-frame
components of `h₀₂` are literally differences of chart-frame metric components
(`metricDiffAt_apply`), so `metricFrameComp_jointContMDiffOn_of_chartGram` applied to `g₁` and
`g₂` discharges the brick's component hypothesis outright.  The only inputs are the two
chart-Gram packages, which K5 already carries for `g₁` (`hgram`) — the `g₂` copy is new but is
the same honest shape.

**Deliverable 2 — integrability.**  `integrable_of_continuous`: on a compact `M` every
continuous scalar is integrable against `riemannianMeasureFamily g t`.  Then, via the new
`inner0S_smooth` (polarization off `normSq0S_smooth` through `normSq0S_add`), **four of K5's
eight `Integrable` slots are discharged with no hypothesis at all**: `hilap`, `hidiv`,
`hinab`, `hidis`.  The reason is a typing fact worth recording: `metricNabla0S`,
`covDiv0SField` and `roughLap0SField` (`ForwardUniqueRmDiff.lean:110/181/192`) all return
`Tensor0SField … ∞`, i.e. they are **smooth by type**, so `normSq0S_smooth` applies to them
directly.  The other four slots (`hipair`, `hirem`, `hirest`, `hidens`) pair a *bare pointwise*
family (`Sdot`, `rem`, `Adot`) or the density carriers, and cannot be discharged without an
input.

**Deliverables 3–5 — conditional.**  `connDiffSq_jointContMDiffOn`, `rmDiffSq_jointContMDiffOn`
and `dens_jointContMDiffOn` (= K5's `hdens`) are stated and proved from the brick, consuming
the joint `C∞` of the **chart-frame scalar components** of `A₀₃` and `S₀₄`.  This is a genuine
reduction, not a restatement: the intrinsic fibre-norm/inverse-metric content is gone, and what
remains is a scalar chart computation.  `dcont_idens_of_joint` then derives K5's `hdcont` and
`hidens` on the open window from `hdens` alone.

## 3. The remaining frontier, classified

**One frontier, named precisely: the chart-frame components of the connection-difference
carrier `A₀₃` (and, one derivative up, of `S₀₄`).**  Classification: **missing groundwork /
API**, not a mathematical obstruction — every ingredient exists, they have never been
composed.  Expected size ~250–450 lines.  Route:

1. Repackage `hgram` (on `ℝ × M`) as `GenJointGram g α (Ioo a b)` — the second half of
   `genGram_of_family` is reusable verbatim; only the first half (which manufactures `hsmooth`
   from `MetricFamilySmoothOn.frameCompSmooth`) is replaced by `hgram` itself.
2. Transport `gen_joint_christoffel` from `ℝ × E` back to `ℝ × M` — `christ_of_family` is the
   template (note it uses the `M × ℝ` factor order; ours is `ℝ × M`).
3. Evaluate `CovariantDerivative.difference (metricCov g₁) (metricCov g₂) x` on the chart
   frame via `LeviCivita_chartBasisVec_alpha_basis_apply` twice, giving
   `connDiffLowAt g₁ g₂ x (e_i, e_j, e_k) = ∑_m (Γ¹ − Γ²)^m_{ji} · G¹_{m k}` on
   `chartLeviCivitaGoodSet α`.  **Watch the domain**: this is the good set, not the whole
   trivialization base set, so the brick's `hA` hypothesis has to be re-localized (the brick
   itself is stated over `baseSet`, which is what `chartInvGram_inverse` needs — the two
   neighbourhoods must be intersected, and the brick's local argument survives that
   intersection unchanged since it only ever uses a *nbhd* of the point).
4. For `S₀₄`, the same chain through `gen_joint_riemann`, plus a chart reading of the **mixed**
   object `riemannCurvature04At g₁ (metricCov g₂)` — Riemann of the *second* connection lowered
   by the *first* metric.  This mixed lowering has no existing chart lemma and is the single
   genuinely new statement in the whole chain.

**Do I expect to close this without user intervention?**  Yes for steps 1–3 (routine
composition of located lemmas).  Step 4 is the risk: it is a new chart identity, and the
`Analysis/Parabolic/RicciLinearization` import it forces into `Evolution/` is a layering
decision worth a planner ruling before it is taken.

**Second, smaller gap:** the closed-edge times.  `dcont_idens_of_joint` covers `Ioo a b`;
K5's `metrics_eq_on` wants `hdcont`/`hidens` on `Icc a c`.  Closing that needs either a
closed-slab `hdens` or a *direct spatial* continuity producer for the density.  The latter is
blocked on the same object: `metricTensor0S` and `rm04Section` give bundled smooth
`Tensor0SField`s for the metric and curvature carriers, but there is **no bundled smooth
section for the connection difference** — `connectionDifferenceTensorAt` is pointwise-only and
`connDiffOutAt` is `private` in `ForwardUniqueFields.lean`.  Same root cause as the main
frontier.

## 4. Lean lessons

* `metricDiffSq` / `connDiffSq` / `rmDiffSq` are plain `def`s over `normSq0S`; `refine` will
  unfold them, but `simp only [metricDiffSq_def]` first makes the unification robust and the
  proof readable.  `forwardUniqueDensity` composes with `ContMDiffOn.add` up to `rfl`.
* `ContMDiffAt.prod` is the `Finset.prod` lemma (the pair constructor is `prodMk`) — the same
  convention `normSq0S_smooth` relies on.
* `ContMDiff.div_const` does not exist at the manifold level; use `.mul contMDiff_const` with
  an explicit `(1 / 2 : ℝ)`.
* `normSq0S_eq_coord` wants `MetricInverseInBasis`, `chartInvGram_inverse` supplies
  `MetricInverseInBasis_gen` — they are definitionally equal once the frame argument is a
  `Module.Basis`, so the mismatch elaborates away silently.
* Section-variable hygiene: introducing `variable (g₁ : ℝ → SmoothRiemannianMetric I M)`
  mid-section and then declaring later theorems with their own explicit `g₁` compiles but is
  confusing; the four slot lemmas were wrapped in their own `section Slots`.
* `fun t ht => …` where the theorem's `t` is implicit and inferred from `ht` trips the unused-
  variable linter — write `_t`.

## 5. Relocation TODOs (campaign end, not now)

* `inner0S_smooth` / `inner0S_continuous` / `normSq0S_continuous` belong next to
  `normSq0S_smooth` in `Tensor/RSTensor/MetricTrace/Connection.lean`; they are general
  `(0,s)`-field facts with nothing Ricci-flow about them.
* `integrable_of_continuous` duplicates the intent of the two existing copies of
  `Continuous.integrable_of_hasCompactSupport_riemannianVolumeMeasure`
  (`Analysis/Integration/DivergenceTheorem/IntegrationByParts.lean:59` and
  `…/WithBoundary/Divergence/IntegrationByParts.lean:76` — **two identically-named lemmas in
  the same namespace**, which is itself a defect worth cleaning).  The family-level wrapper
  belongs in `Analysis/Integration/Measure/`.
* `chartGramDet_jointContMDiffOn` / `chartGramAdj_jointContMDiffOn` /
  `chartInvGram_jointContMDiffOn` belong beside their spatial counterparts in
  `Geometry/Operator/Gradient.lean`, or in a new `Geometry/Metric/ChartGramJoint.lean`.
* `normSq0S_jointContMDiffOn` — canonical home is the metric-trace/fibre-norm layer, once a
  second consumer appears.
