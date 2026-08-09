# ForwardUniqueRateLe.lean — brick K4 (forward-uniqueness lane, Route K)

Status: **OUTCOME (A) — all four mission parts delivered, 0 `sorry`, axiom-clean**
(`propext, Classical.choice, Quot.sound` on every public declaration), targeted build
re-run after the final source edit (fresh-olean audit) and GREEN with no linter warnings.
917 lines, 20 public + 2 private declarations, **no instances, no axioms, no notation**
under the hardened hygiene sweep.

## What this file provides

The Grönwall-facing estimate of `ShortTime/FORWARD_UNIQUE_PRO_RULING.md` §6,
`E′ ≤ K·E − κ·D ≤ K·E`, on top of K3's exact first variation.

1. **Young kit** — `two_inner0S_le_eps`, `neg_two_inner0S_le_eps` (the ε-unbalanced
   polarisation the absorption steps need; `Tensor0SMetricIneq.lean` only had the balanced
   `two_inner0S_le`), `normSq0S_smul`.
2. **Density algebra** — `density_nonneg`, `metricDiffSq_le_dens`, `connDiffSq_le_dens`,
   `rmDiffSq_le_dens`.
3. **The dissipation** — `forwardUniqueDissipation g₁ Sfield t :=
   ∫ |metricNabla0S (g₁ t) Sfield|²_{g₁ t} dμ_{g₁ t}` (lane's own ∇, energy's own measure),
   plus `dissipation_nonneg`.
4. **The currency bridge** (the gateway, see below) — `innerPt_eq_inner0S`,
   `l2Inner_eq_integral`, and the two IBP restatements `intInner_lap_eq_neg`
   (`∫⟨Δ_g T, T⟩ = −∫|∇^g T|²`) and `intInner_div_eq_neg` (`∫⟨div_g V, T⟩ = −∫⟨∇^g T, V⟩`).
5. **Sub-lemma 1** — `ricciDiffSq_le`.
6. **Rate splitting** — `rateRest`, `rateIntegrand_eq`, `rate_eq_add`.
7. **The analytic core** — `sPart_le`.
8. **h/A/volume parts** — `rateRest_le` (pointwise), `intRateRest_le`.
9. **Capstone** — `forwardUniqueRate_le`.

## The mathematical route, and the one place the mission's shape was sharpened

### Sub-lemma 1: the Ricci-difference bound has NO background·|h₀₂|² term

The mission expected `|Ric₁ − Ric₂|² ≤ C(n)(|S₀₄|² + background·|h₀₂|²)` with an
"own-vs-`g₁` trace discrepancy" that is `h₀₂`-algebraic. That discrepancy is **zero**:
Ricci is a *pure contraction* of the `(1,3)` Riemann tensor, and lowering with a metric and
tracing back with the *same* metric cancels. So `Ric_i = tr_{g₁}(Rm04_i^{g₁})` for **both**
flows when both are lowered with `g₁`, and therefore

`Ric₁ − Ric₂ = tr_{g₁}(S₀₄)` exactly.

`ricciDiffSq_le` is stated with the trace representative `V` and its norm bound as named
inputs (and a background slot `B` kept, so a producer that does carry a lowering defect
still fits), and the estimate itself is `traceNormSq_le` at `s = 2`, giving `n⁴`.

**Producer debt (small, named).** The tensor-level identity
`Ric_g = metric trace of riemannCurvature04At` **does not exist** in the tree. What exists is
component-level: `ricciFromRm13_comp_eq_rm04_trace`
(`Geometry/Curvature/Components/RicciTrace.lean:40`) and
`ricciFromRm13At_rm04_first_trace_convention` (`Geometry/Curvature/Convention.lean:83`),
both contracting **Rm04 slots 1 and 4** (not "first two"), gated on `Rm04LowersRm13At`,
which `riemannCurvature04At_eq_lower_riemannCurvatureAt`
(`Geometry/Curvature/Riemann/Basic/Pointwise.lean:660`) discharges directly. So the missing
producer is: *lift that component identity to the tensor level and permute slots (1,4) into
the first-two position*. Slot permutation is free for the norm —
`Tensor0SBundle.normSq0S_domDomCongr` (`Tensor/RSTensor/NormSqProduct.lean:94`, needs an
orthonormal-frame witness) — but there is **no `inner0S_domDomCongr`** (zero occurrences of
`inner0S` with `domDomCongr` in the tree); a polarisation mirror of `normSq0S_domDomCongr`
is the natural dedup addition.

### The currency bridge was the real gate, and it is now closed

K2.7 proved IBP in the **model** currency `tensorL2Inner g 0 s (ccLift0S g T).toFun …`;
K3's energy is an integral of the **fibre** pairing `inner0S`. **No lemma in the tree
connected `tensorInnerPointwise` to `inner0S`** (verified: zero declarations mention both).
Without the bridge, K4's S-part could only have been stated with the IBP as a hypothesis —
pure bookkeeping debt.

The bridge is now proved:

* `lowerZero_unit` (private) — `r = 0` index lowering is unit evaluation.
* `innerPtDiag` (private) — diagonal identification via one `g`-orthonormal frame:
  model side through `tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`, fibre side through
  `normSq0S_identity_eq_sum_sq`, reindexed across `Fin (0 + s) ≃ Fin s`.
* `innerPt_eq_inner0S` — the off-diagonal case **by polarisation** (`normSq0S_add` on the
  fibre side, `tensorInnerPointwise_add_left/right` + `tensorInnerPointwise_symm` on the
  model side, `TensorRSSpace.toModel_add` and CLM `add_apply` to move `+` across the lift).
  This avoids redoing the `Fin (0 + s)` diagonal-sum gymnastics for the cross term.
* `l2Inner_eq_integral` — integrate pointwise, then `ccLift0S_unit`.

**Dedup item for the planner (3rd occurrence).** `innerPtDiag` + `lowerZero_unit` are a
re-derivation of the **private** `rfns_eq_normSq0S_unit` / `lowerAllUpper_zero_eq_unit`
(`HCGCompactness/MetricCovDerivBridge.lean:181, 159`), themselves already duplicated at
`HCGCompactness/UnifCurvatureJetBound.lean:477, 459`. The canonical home is the
`RiemannianFiberNormSq` layer, next to `riemannianFiberNormSq_eq_tensorInnerPointwise`.
`innerPt_eq_inner0S` and `l2Inner_eq_integral` are genuinely new and belong in the
`Analysis/Integration/L2/Pairing/` layer once the lane settles.

### S-part (the analytic core)

With `Ṡ = Δ₁S₀₄ + div₁U₀₅ + rem` taken as the explicit hypothesis `hSdec` in exactly the
shape `rmLowComp_deriv` produces (three summands, no re-derivation):
principal `→ −2D` by `intInner_lap_eq_neg`; flux `→ −2∫⟨∇S, U⟩ ≤ εD + ε⁻¹C_U·E` by
`intInner_div_eq_neg` + `neg_two_inner0S_le_eps` + `hU`; remainder `→ (C_rem+1)E` by
`two_inner0S_le` + `hrem`. Total `(ε − 2)D + (ε⁻¹C_U + C_rem + 1)E`.

### A-part, and why the capstone carries TWO Young parameters

`|∂ₜA₀₃|²` legitimately contains `|∇¹S₀₄|²` (K1C-b), so a *balanced* Young step would put
`C_A·D` on the wrong side and the `κ` in `E′ ≤ KE − κD` could go negative for a large `C_A`.
The fix is a second free parameter `δ` on the A cross term: `2⟨Ȧ, A⟩ ≤ δ|Ȧ|² + δ⁻¹|A|²`,
contributing only `δ·C_A·D`. The capstone's smallness hypothesis is therefore

`habs : δ * C_A + ε ≤ 1`  ⟹  `κ = 1`.

## The capstone's full named-hypothesis package

`forwardUniqueRate_le (g₁ g₂ Adot Sdot Sfield U rem) {t ε δ C_A C_R C_Ric C_V C_U C_rem}`:

| slot | statement | producer |
|---|---|---|
| `hε`, `hδ` | `0 < ε`, `0 < δ` | free Young parameters |
| `habs` | `δ·C_A + ε ≤ 1` | choice of `δ`, `ε` given `C_A` |
| `hcar` | `∀x, Sfield x = rmDiffLowAt (g₁ t) (g₂ t) x` | the S₀₄ carrier realisation |
| `hSdec` | `∀x, Sdot t x = roughLap0SField (g₁ t) Sfield x + covDiv0SField (g₁ t) U x + rem x` | `rmLowComp_deriv` (K2.6 / R4 bridge) |
| `hU` | `∀x, ‖U x‖² ≤ C_U · density` | `rmFluxNormSq_le` (K2.4) on a slab |
| `hrem` | `∀x, ‖rem x‖² ≤ C_rem · density` | `rmRemNormSq_le` (K2.5) + `rmDotRem` bounds |
| `hreact` | `∀x, React₂ + React₃ + React₄ ≤ C_R · density` | slab `|Ric₁|` bound (**open, see below**) |
| `hRic` | `∀x, ‖Ric₁ − Ric₂‖² ≤ C_Ric · density` | `ricciDiffSq_le` + the slot-convention producer |
| `hAdot` | `∀x, ‖Adot t x‖² ≤ C_A·(density + ‖∇¹S₀₄‖²)` | **K1C-b slot** (concurrent) |
| `hvol` | `∀x, ½·traceTimeDerivMetric g₁ t x ≤ C_V` | slab bound on `½ tr_{g₁}(∂ₜg₁) = −scal₁` |
| `hirest`, `hipair`, `hilap`, `hidiv`, `hirem`, `hinab`, `hidis`, `hidens` | `Integrable …` against `riemannianMeasureFamily g₁ t` | continuity + `CompactSpace M` (the `hdens` joint-regularity debt from №6) |

Conclusion:
`forwardUniqueRate g₁ g₂ Adot Sdot t ≤ K · forwardUniqueEnergy g₁ g₂ t − forwardUniqueDissipation g₁ Sfield t`
with the **explicit** constant `K = C_R + 4C_Ric + 2 + δC_A + δ⁻¹ + C_V + ε⁻¹C_U + C_rem`.

`hAdot` is deliberately stated in the form *implied by* (and weaker than) the ruling's
`|∂ₜA₀₃|² ≤ C(|h₀₂|² + |A₀₃|² + |∇¹S₀₄|²)`, since `|h₀₂|² + |A₀₃|² ≤ density`; K1C-b's output
therefore feeds it with no adapter.

## Instance set (RULING R5)

The file carries `[InnerProductSpace ℝ E]` and the endpoint instance set, mirroring
`ForwardUniqueIBP.lean` exactly (which is forced: `covDivergence` and the Green pairing are
stated over an inner-product model). This is endpoint-altitude assembly, ratified by R5.
No separate `[NormedSpace ℝ E]` variable is declared (that would be a diamond).

**Hygiene note.** The first draft copied `ForwardUniqueEnergy.lean`'s
`private local instance : MeasurableSpace M := borel M` block (six times). They turned out to
be **entirely unnecessary** here and were removed: `riemannianVolumeMeasure` /
`riemannianMeasureFamily` have the Borel σ-algebra baked into their elaborated type, so
`∫ … ∂μ` and `Integrable f μ` infer it from `μ`. The file now declares **zero** instances.
Worth checking whether the same removal applies to `ForwardUniqueEnergy.lean`.

## Lean lessons (durable)

* **`rw [someDef]` on a definition whose body mentions another definition can unfold both.**
  `rw [forwardUniqueDissipation, forwardUniqueEnergy]` left `riemannianMeasureFamily g₁ t`
  behind, so a following `set μ := riemannianVolumeMeasure …` silently failed to fold it and
  the final `linarith` saw two syntactically different measures. Exactly **one**
  `rw [riemannianMeasureFamily_def]` is needed after unfolding both defs — a second copy
  errors with "did not find an occurrence", which is what makes this confusing: the error is
  reported for the *last* lemma in the `rw` list, while the earlier one already succeeded and
  rewrote *all* occurrences.
* **`← integral_add` is a trap.** Rewriting backwards makes Lean solve for `f` and `g` by
  higher-order unification and it produces the Pi-sum `((fun x => …) + fun x => …) a` in the
  goal, which no later `rw` matches. Always go forwards: state the pointwise-split integral
  as an explicit `have h1 : ∫ … = ∫ x, (A x + (B x + C x)) ∂μ := integral_congr_ae …`, then
  `rw [h1, integral_add hA hBC, integral_add hB hC]`. Same for the RHS of an
  `integral_mono`: give the summed integrability as a `have` with an **explicitly written,
  beta-reduced type**, otherwise `Integrable.add` hands `integral_mono` a Pi-sum.
* **`linarith` cannot expand `(c + 1) * d`.** Every place a constant bundle multiplies the
  density/energy/dissipation, supply the distributed identity as a `have … := by ring`
  hypothesis and pass it to `linarith`; this is far more robust than reaching for `nlinarith`
  (which failed on the same goals). The final capstone assembly is one such `hring`.
* **`integral_congr_ae` leaves an un-beta-reduced goal** `(fun x => f x) x = (fun x => g x) x`
  under `Filter.Eventually.of_forall fun x => ?_`; `rw` then fails on patterns that print
  correctly. Insert `change <the beta-reduced equation>` first (**not** `show` — the style
  linter `linter.style.show` rejects `show` when it changes the goal, which it does here).
* `separableFormAt_zero` + `toModel_tensorRS_apply`
  (`Geometry/Connection/MetricCompatibility/TensorLoweringParallel.lean:89, 255`) are the two
  public lemmas that make the `r = 0` lowering collapse to unit evaluation; both live in
  `DifferentialGeometry.Integral.Connection`.

## Reused, not reinvented (per project search rule)

`traceNormSq_le`, `rmFluxNormSq_le`, `rmRemNormSq_le` (`ForwardUniqueRmBounds.lean`);
`two_inner0S_le`, `abs_inner0S_le`, `normSq0S_add/_sub/_neg`, `inner0S_*` bilinearity
(`Tensor0SMetricIneq.lean`); `l2Inner_nabla_eq_neg_div`, `l2Inner_nabla_self_eq_neg_lap`,
`ccLift0S`, `ccLift0S_unit` (`ForwardUniqueIBP.lean`); `forwardUniqueDensity/DensityDot/Rate/
Energy`, `movingReact0S`, `metricDiffDot` (`ForwardUniqueEnergy.lean`);
`roughLap0SField`, `covDiv0SField`, `metricNabla0S` (`ForwardUniqueRmDiff.lean`);
`exists_gOrthonormalBasis`, `metricInverseInBasis_of_orthonormal`,
`normSq0S_identity_eq_sum_sq`, `tensorInnerPointwise_0s_eq_diag_sum_orthoFrame`,
`tensorInnerPointwise_add_left/right/_symm`, `TensorRSSpace.toModel_add`,
`riemannianMeasureFamily_def`, `traceTimeDerivMetric`.

`ricciEdgeMetric` (`Evolution/RicciEdgeBounds.lean`) was **not** consumed here: this brick's
metric comparison enters only through `hU`/`hrem`, whose producers (`rmRemNormSq_le`) already
take the `Λ`-comparison in `ricciEdgeMetric` shape. K5 is where `ricciEdgeMetric` supplies it.

## Remaining risk / next

No mathematical frontier is left **inside** K4. The open producers it now names precisely:

1. **`hreact` (the moving-metric reaction bound).** `movingReact0S` is
   `ricReactionContract` of `Ric₁` against `W ⊗ W` in the canonical finite basis; the needed
   pointwise bound `|movingReact0S g x s Q W| ≤ C(n)·‖Q‖·‖W‖²` does not exist yet. It is a
   `fluxNormSq_le`-pattern frame estimate (routine, ~80 lines) and would turn `hreact` from
   a slab assumption into `C_R = C(n)·sup_slab‖Ric₁‖`. **Recommended next micro-brick.**
2. **The Ricci-trace slot-convention producer** for `ricciDiffSq_le`'s `htr` (see above) —
   also routine, but needs the missing `inner0S_domDomCongr` / a `normSq0S_domDomCongr`
   application.
3. **K1C-b** (`hAdot`) — concurrent lane.
4. **Integrability** — eight `Integrable` slots, all consequences of the joint `(t,x)`
   continuity tower that K3 already logged as the `hdens` debt (№6). They are *not* new
   frontiers, but they are not free either.

For **K5** (edge-Grönwall + integral-zero-to-equality): the capstone's output is exactly
`E′ ≤ K·E − D` with `D ≥ 0` (`dissipation_nonneg`), so the Grönwall step only needs
`E′ ≤ K·E`, which follows by `linarith [dissipation_nonneg …]`. No further shape work.
